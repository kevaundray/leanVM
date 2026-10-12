module

public import LeanVMCircuits.Rec.Relax
public import LeanVMCircuits.Rec.TreeSound

@[expose] public section

/-!
The tree's edges, from the dumps: a node's circuit reads each child's statement words as the claims that statement makes on the polynomials and matrices, scaled as the child's kind requires.

A node circuit hints each child's statement (`Design::node`), one `E` word per position of the statement's layout (`StatementLayout`: the kind, the digest's two halves, the dense point, each dense polynomial's value, the matrices' row and column points, each flock circuit's two matrix values), and its reduction takes, with the claims of its own proofs, the claims the child's statement carries (`Design::carried`): on each dense polynomial, at its prefix of the point, its value, scaled for the circuits' fixed polynomials by whether the child is a node; on each flock circuit's two matrices, at its prefixes of the row and column points, their values. A dump marks the layout (`edge layout`), each child's statement words (`edge child`) and the claims the reduction takes (`edge dense`, `edge term`, `edge matrix`, `edge row`, `edge col`).

An edge certificate (`EdgeCert`) records them with the calls that compute each child's scale from its kind word (`ScaleCert`) and the call that reads its digest. `EdgeCert.accepts` checks the layout fits, each child has the layout's words, its scale is computed from its kind word as the tier computes it, its digest is read from its digest words, and every claim the child's words make (`stmtClaims`, at the scale's wire) is one the reduction takes.

`EdgeCert.edge`: in any assignment satisfying the circuit the calls build, if a child's words carry statement `st`, every claim `st` makes at its kind's scale (`nodeScale`) is among the claims the reduction takes, and the digest the circuit reads is `st`'s. `EdgeCert.edge_holds`: when those claims hold, `st`'s do. `hedge_of_certs` gives `TreeSound.tree_sound`'s edge premise for a tree whose circuits have accepted certificates, reading a node's input claims as its reduction's and a node's statement as its words' claims; `tree_sound_certs` is `tree_sound` with it.

That the parent's hinted words carry the child's statement is the recursive verifier's soundness, a premise (`hpub`): the parent verifies the child's proof with these words as its statement.
-/

namespace LeanVMCircuits.Rec.Edges

open LeanVMCircuits.Rec Model

/-! Claims, over wires or values. -/

/-- One claim on a dense polynomial (`DenseTerm`): the shared prefix's first `nLow` coordinates, then public bits, then `top`, scaled by `scale` when present. -/
structure Term (α : Type) where
  nLow : ℕ
  bits : ℕ
  bitsLen : ℕ
  top : List α
  scale : Option α
  value : α
  deriving DecidableEq, Repr

/-- Claims on one dense polynomial at points sharing a prefix (`DenseClaim`). -/
structure Dense (α : Type) where
  poly : ℕ
  low : List α
  terms : List (Term α)
  deriving DecidableEq, Repr

/-- A matrix's coefficient in a matrix claim (`Coefficient`). -/
inductive Coef (α : Type) where
  | zero
  | one
  | of (x : α)
  deriving DecidableEq, Repr

/-- A matrix claim's row weight (`RowWeight`). -/
inductive RowW (α : Type) where
  | skip (z : α) (rest : List α)
  | point (p : List α)
  deriving DecidableEq, Repr

/-- A matrix claim's column weight (`ColWeight`). -/
inductive ColW (α : Type) where
  | slices (s rest : List α)
  | point (p : List α)
  deriving DecidableEq, Repr

/-- A claim on a flock circuit's matrices (`MatrixClaim`). -/
structure Matrix (α : Type) where
  circuit : ℕ
  row : RowW α
  col : ColW α
  coefs : Coef α × Coef α
  value : α
  deriving DecidableEq, Repr

/-- What a reduction takes: its dense and matrix claims (`NodeClaims`, without the bound values). -/
structure Claims (α : Type) where
  dense : List (Dense α) := []
  matrices : List (Matrix α) := []
  deriving DecidableEq, Repr

variable {α β : Type}

def Term.map (f : α → β) (t : Term α) : Term β := ⟨t.nLow, t.bits, t.bitsLen, t.top.map f, t.scale.map f, f t.value⟩
def Dense.map (f : α → β) (d : Dense α) : Dense β := ⟨d.poly, d.low.map f, d.terms.map (Term.map f)⟩
def Coef.map (f : α → β) : Coef α → Coef β
  | .zero => .zero
  | .one => .one
  | .of x => .of (f x)
def RowW.map (f : α → β) : RowW α → RowW β
  | .skip z rest => .skip (f z) (rest.map f)
  | .point p => .point (p.map f)
def ColW.map (f : α → β) : ColW α → ColW β
  | .slices s rest => .slices (s.map f) (rest.map f)
  | .point p => .point (p.map f)
def Matrix.map (f : α → β) (m : Matrix α) : Matrix β :=
  ⟨m.circuit, m.row.map f, m.col.map f, (m.coefs.1.map f, m.coefs.2.map f), f m.value⟩
def Claims.map (f : α → β) (c : Claims α) : Claims β := ⟨c.dense.map (Dense.map f), c.matrices.map (Matrix.map f)⟩

/-- Claims are true under a reading `tD`, `tM` of each dense and matrix claim: the polynomials' and matrices' values at an outcome. -/
def Claims.Holds (tD : Dense β → Prop) (tM : Matrix β → Prop) (c : Claims β) : Prop :=
  (∀ d ∈ c.dense, tD d) ∧ ∀ m ∈ c.matrices, tM m

/-- Every claim of `a` is one of `b`'s. -/
def Claims.Sub (a b : Claims β) : Prop := (∀ d ∈ a.dense, d ∈ b.dense) ∧ ∀ m ∈ a.matrices, m ∈ b.matrices

theorem Claims.Holds.of_sub {tD : Dense β → Prop} {tM : Matrix β → Prop} {a b : Claims β} (h : b.Holds tD tM)
    (hs : a.Sub b) : a.Holds tD tM :=
  ⟨fun d hd => h.1 d (hs.1 d hd), fun m hm => h.2 m (hs.2 m hm)⟩

/-! A statement's layout and the claims its words make. -/

/-- `StatementLayout` with the prefixes its claims are at: the dense point's and matrix points' widths, how many dense polynomials and flock circuits, each dense polynomial's variables and each flock circuit's matrix variables. -/
structure Layout where
  nDense : ℕ
  nPolys : ℕ
  nMatrix : ℕ
  nFlocks : ℕ
  vars : List ℕ
  klog : List ℕ
  deriving DecidableEq, Repr, Inhabited

namespace Layout

/-- Where the dense values start: after the kind, the digest's two halves and the dense point. -/
def dv (L : Layout) : ℕ := 3 + L.nDense
def rowsAt (L : Layout) : ℕ := L.dv + L.nPolys
def colsAt (L : Layout) : ℕ := L.rowsAt + L.nMatrix
def matsAt (L : Layout) : ℕ := L.colsAt + L.nMatrix
/-- How many words a statement has. -/
def len (L : Layout) : ℕ := L.matsAt + 2 * L.nFlocks

/-- A prefix length for each dense polynomial and flock circuit, within its point. -/
def ok (L : Layout) : Bool :=
  L.vars.length == L.nPolys && L.klog.length == L.nFlocks && L.vars.all (· ≤ L.nDense) &&
    L.klog.all (· ≤ L.nMatrix)

end Layout

/-- Whether a dense polynomial holds circuits' fixed columns (`DensePoly::is_fixed`: `Fixed` and `Wide`). -/
def isFixed (p : ℕ) : Bool := 2 ≤ p

/-- The claim words `x` make on dense polynomial `p` (`Design::carried`): at the point's first `vars p` coordinates, its value, scaled by `σ` on a fixed polynomial. -/
def stmtDense (L : Layout) (x : ℕ → β) (σ : β) (p : ℕ) : Dense β where
  poly := p
  low := (List.range (L.vars.getD p 0)).map fun i => x (3 + i)
  terms := [{ nLow := L.vars.getD p 0, bits := 0, bitsLen := 0, top := [],
              scale := if isFixed p then some σ else none, value := x (L.dv + p) }]

/-- The claim words `x` make on flock circuit `f`'s matrix `k` (`MatrixClaim::carried`): at the row and column points' first `klog f` coordinates, its value. -/
def stmtMatrix (L : Layout) (x : ℕ → β) (f k : ℕ) : Matrix β where
  circuit := f
  row := .point ((List.range (L.klog.getD f 0)).map fun i => x (L.rowsAt + i))
  col := .point ((List.range (L.klog.getD f 0)).map fun i => x (L.colsAt + i))
  coefs := if k = 0 then (.one, .zero) else (.zero, .one)
  value := x (L.matsAt + 2 * f + k)

/-- Every claim a statement's words `x` make, fixed polynomials' claims scaled by `σ`. -/
def stmtClaims (L : Layout) (x : ℕ → β) (σ : β) : Claims β where
  dense := (List.range L.nPolys).map (stmtDense L x σ)
  matrices := (List.range L.nFlocks).flatMap fun f => [stmtMatrix L x f 0, stmtMatrix L x f 1]

theorem stmtClaims_map (L : Layout) (x : ℕ → α) (σ : α) (f : α → β) :
    (stmtClaims L x σ).map f = stmtClaims L (f ∘ x) (f σ) := by
  simp only [Claims.map, stmtClaims, List.map_map, List.map_flatMap, List.map_cons, List.map_nil, Claims.mk.injEq]
  constructor
  · apply List.map_congr_left
    intro p _
    simp only [Function.comp_apply, Dense.map, stmtDense, List.map_map, List.map_cons, List.map_nil, Term.map,
      Dense.mk.injEq, true_and, List.cons.injEq, Term.mk.injEq, and_true]
    refine ⟨rfl, ?_⟩
    split <;> rfl
  · apply List.flatMap_congr
    intro g _
    simp only [Matrix.map, stmtMatrix, RowW.map, ColW.map, List.map_map, Function.comp_apply]
    congr 2

theorem getD_le {xs : List ℕ} {n i : ℕ} (h : xs.all (· ≤ n) = true) : xs.getD i 0 ≤ n := by
  rw [List.getD_eq_getElem?_getD]
  cases hx : xs[i]? with
  | none => simp
  | some a =>
    simp only [List.all_eq_true, decide_eq_true_eq] at h
    exact h a (List.mem_of_getElem? hx)

/-- A statement's claims read only its words. -/
theorem stmtClaims_congr {L : Layout} (hL : L.ok = true) {x y : ℕ → β} (σ : β) (h : ∀ i < L.len, x i = y i) :
    stmtClaims L x σ = stmtClaims L y σ := by
  simp only [Layout.ok, Bool.and_eq_true, beq_iff_eq] at hL
  obtain ⟨⟨⟨-, -⟩, hv⟩, hk⟩ := hL
  simp only [Layout.len, Layout.matsAt, Layout.colsAt, Layout.rowsAt, Layout.dv] at h
  simp only [stmtClaims, Claims.mk.injEq]
  constructor
  · apply List.map_congr_left
    intro p hp
    rw [List.mem_range] at hp
    have hvp := getD_le (i := p) hv
    simp only [stmtDense, Dense.mk.injEq, List.cons.injEq, Term.mk.injEq, and_true, true_and]
    refine ⟨List.map_congr_left fun i hi => h _ ?_, h _ (by simp only [Layout.dv]; omega)⟩
    rw [List.mem_range] at hi
    omega
  · apply List.flatMap_congr
    intro f hf
    rw [List.mem_range] at hf
    have hkf := getD_le (i := f) hk
    have hm : ∀ k < 2, stmtMatrix L x f k = stmtMatrix L y f k := by
      intro k hk2
      simp only [stmtMatrix, Matrix.mk.injEq, RowW.point.injEq, ColW.point.injEq, true_and]
      refine ⟨List.map_congr_left fun i hi => h _ ?_, List.map_congr_left fun i hi => h _ ?_, h _ ?_⟩
      · rw [List.mem_range] at hi; simp only [Layout.rowsAt, Layout.dv]; omega
      · rw [List.mem_range] at hi; simp only [Layout.colsAt, Layout.rowsAt, Layout.dv]; omega
      · simp only [Layout.matsAt, Layout.colsAt, Layout.rowsAt, Layout.dv]; omega
    rw [hm 0 (by omega), hm 1 (by omega)]

/-! A child's scale: one, or whether it is a node, from its kind word. -/

/-- How a tier computes a child's scale from its kind word (`Design::kind_rows`). -/
inductive Mode where
  /-- Two kinds: the kind word is the bit. -/
  | kind
  /-- The large tier, whose children are all nodes: one. -/
  | one
  /-- `b` index bits: one plus the product of each low bit plus one. -/
  | bits (b : ℕ)
  deriving DecidableEq, Repr

/-- Bit `k` of a word's first limb, in `K`. -/
noncomputable def bitK (x : Fin 4 → K) (k : ℕ) : K := if (toWord (x 0)).testBit k then 1 else 0

/-- The product of each of the first `k` bits plus one: one when they are all zero, else zero. -/
noncomputable def firstProd (x : Fin 4 → K) : ℕ → E
  | 0 => 1
  | k + 1 => firstProd x k * (emb (bitK x k) + 1)

/-- The scale of a child of kind word `x`. -/
noncomputable def nodeScale : Mode → (Fin 4 → K) → E
  | .kind, x => toE (x 0) (x 1) (x 2)
  | .one, _ => 1
  | .bits b, x => firstProd x b + 1

/-- A statement word's `E` element. -/
noncomputable def stE (st : ℕ → Fin 4 → K) (i : ℕ) : E := toE (st i 0) (st i 1) (st i 2)

/-- Output `k` of call `j`. -/
def out (os : Array (List ℕ)) (j k : ℕ) : ℕ := (os.getD j []).getD k 0

/-- Where a circuit computes a child's scale: its kind word itself, a `one` call's output, or for `bits` the `one` call, the kind's `e_to_k` and its first limb's `split`, per bit its `k_to_e1`, the `add` of one and the `mul` into the product, and the last `add` of one. -/
inductive ScaleCert where
  | kind
  | one (call : ℕ)
  | bits (one eToK split last : ℕ) (steps : List (ℕ × ℕ × ℕ))
  deriving DecidableEq, Repr, Inhabited

def ScaleCert.mode : ScaleCert → Mode
  | .kind => .kind
  | .one _ => .one
  | .bits _ _ _ _ steps => .bits steps.length

/-- The product's wire after `k` bits, from the one wire `o`. -/
def accAt (os : Array (List ℕ)) (o : ℕ) (steps : List (ℕ × ℕ × ℕ)) : ℕ → ℕ
  | 0 => o
  | k + 1 => out os (steps.getD k (0, 0, 0)).2.2 0

/-- The scale's wire, for kind word `kw`. -/
def ScaleCert.wire (os : Array (List ℕ)) (kw : ℕ) : ScaleCert → ℕ
  | .kind => kw
  | .one c => out os c 0
  | .bits _ _ _ last _ => out os last 0

/-- The named calls compute the scale from kind word `kw`. -/
def ScaleCert.ok (cs : Array Call) (os : Array (List ℕ)) (kw : ℕ) : ScaleCert → Bool
  | .kind => true
  | .one c => cs[c]? == some .one
  | .bits o e s last steps =>
    let one := out os o 0
    cs[o]? == some .one && cs[e]? == some (.eToK kw) && cs[s]? == some (.split (out os e 0)) &&
      steps.length ≤ 64 &&
      (List.range steps.length).all (fun k =>
        let (a, p, m) := steps.getD k (0, 0, 0)
        cs[a]? == some (.kToE1 (out os s k)) && cs[p]? == some (.add (out os a 0) one) &&
          cs[m]? == some (.mul (accAt os one steps k) (out os p 0))) &&
      cs[last]? == some (.add (accAt os one steps steps.length) one)

/-- Every call holds its contract. -/
def AllHold (cs : Array Call) (os : Array (List ℕ)) (st : ℕ → Fin 4 → K) (val : Val) : Prop :=
  ∀ j (hj : j < cs.size), cs[j].Holds st val (os.getD j [])

theorem holds_at {cs : Array Call} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val} (hF : AllHold cs os st val)
    {j : ℕ} {c : Call} (h : cs[j]? = some c) : c.Holds st val (os.getD j []) := by
  obtain ⟨hj, rfl⟩ := Array.getElem?_eq_some_iff.mp h
  exact hF j hj

/-- The scale's wire carries `nodeScale` of the kind word. -/
theorem ScaleCert.sem {cs : Array Call} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val}
    (hF : AllHold cs os st val) (sc : ScaleCert) (kw : ℕ) (h : sc.ok cs os kw = true) :
    Model.ev val (sc.wire os kw) = nodeScale sc.mode (val kw) := by
  cases sc with
  | kind => rfl
  | one c =>
    simp only [ScaleCert.ok, beq_iff_eq] at h
    exact holds_at hF h
  | bits o e s last steps =>
    simp only [ScaleCert.ok, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range]
      at h
    obtain ⟨⟨⟨⟨⟨ho, he⟩, hs⟩, h64⟩, hsteps⟩, hlast⟩ := h
    have hone : Model.ev val (out os o 0) = 1 := holds_at hF ho
    have hE : ∀ i : Fin 4, i.val < 3 → val (out os e i) 0 = val kw i := holds_at hF he
    obtain ⟨hbit, hword⟩ : (∀ i < 64, val (out os s i) 0 = 0 ∨ val (out os s i) 0 = 1) ∧
        toWord (val (out os e 0) 0) = num (fun i => if val (out os s i) 0 = 1 then 1 else 0) 64 :=
      holds_at hF hs
    have hw : toWord (val kw 0) = num (fun i => if val (out os s i) 0 = 1 then 1 else 0) 64 := by
      rw [← hword]; exact congrArg toWord (hE 0 (by decide)).symm
    have hacc : ∀ k ≤ steps.length, Model.ev val (accAt os (out os o 0) steps k) = firstProd (val kw) k := by
      intro k hk
      induction k with
      | zero => exact hone
      | succ k ih =>
        have hk' : k < steps.length := by omega
        obtain ⟨⟨ha, hp⟩, hm⟩ := hsteps k hk'
        have hA : Model.ev val (out os (steps.getD k (0, 0, 0)).1 0) = emb (val (out os s k) 0) := holds_at hF ha
        have hP : Model.ev val (out os (steps.getD k (0, 0, 0)).2.1 0) =
            Model.ev val (out os (steps.getD k (0, 0, 0)).1 0) + Model.ev val (out os o 0) := holds_at hF hp
        have hM : Model.ev val (out os (steps.getD k (0, 0, 0)).2.2 0) =
            Model.ev val (accAt os (out os o 0) steps k) * Model.ev val (out os (steps.getD k (0, 0, 0)).2.1 0) :=
          holds_at hF hm
        have hb : val (out os s k) 0 = bitK (val kw) k := by
          have hk64 : k < 64 := by omega
          have ht := congrArg (fun n => Nat.testBit n k) hw
          simp only [testBit_num _ 64 k hk64] at ht
          have z1 : (0 : ZMod 2) ≠ 1 := by decide
          unfold bitK
          rcases hbit k hk64 with e | e <;> simp_all
        show Model.ev val (out os (steps.getD k (0, 0, 0)).2.2 0) =
          firstProd (val kw) k * (emb (bitK (val kw) k) + 1)
        rw [hM, ih (by omega), hP, hA, hone, hb]
    show Model.ev val (out os last 0) = firstProd (val kw) steps.length + 1
    have hL : Model.ev val (out os last 0) =
        Model.ev val (accAt os (out os o 0) steps steps.length) + Model.ev val (out os o 0) :=
      holds_at hF hlast
    rw [hL, hacc _ le_rfl, hone]

/-! The certificate. -/

/-- A child's edge: its statement's words, the calls computing its scale, and the `halves_to_d` call reading its digest. -/
structure ChildEdge where
  words : List ℕ
  scale : ScaleCert
  digest : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- A circuit's edges: its calls, its statement's layout, the claims its reduction takes and its children. -/
structure EdgeCert where
  calls : Array Call
  layout : Layout
  claims : Claims ℕ
  children : List ChildEdge

/-- The claims a child's words make, at its scale's wire. -/
def ChildEdge.claims (L : Layout) (os : Array (List ℕ)) (ch : ChildEdge) : Claims ℕ :=
  stmtClaims L (fun i => ch.words.getD i 0) (ch.scale.wire os (ch.words.getD 0 0))

/-- A child's edge checks: its words are the layout's, its scale is computed from its kind word, its digest is read from its digest words, and the claims its words make are among those the reduction takes. -/
def ChildEdge.ok (c : EdgeCert) (os : Array (List ℕ)) (ch : ChildEdge) : Bool :=
  ch.words.length == c.layout.len && ch.scale.ok c.calls os (ch.words.getD 0 0) &&
    c.calls[ch.digest]? == some (.halvesToD (ch.words.getD 1 0) (ch.words.getD 2 0)) &&
    (ch.claims c.layout os).dense.all (fun d => decide (d ∈ c.claims.dense)) &&
    (ch.claims c.layout os).matrices.all (fun m => decide (m ∈ c.claims.matrices))

/-- The verdict on the outputs `os` of the certificate's calls. -/
def EdgeCert.accepts (c : EdgeCert) (os : Array (List ℕ)) : Bool :=
  c.layout.ok && c.children.all (ChildEdge.ok c os)

/-- The replay's verdict: the calls replay with every equality, building a circuit of the layout's statement length, and the certificate accepts their outputs. -/
def EdgeCert.check (c : EdgeCert) : Bool :=
  match replayR c.calls #[] 0 {} #[] with
  | some (t, os) => t.statement == c.layout.len && c.accepts os
  | none => false

theorem allHold_of_replay {cs : Array Call} {t : State} {os : Array (List ℕ)}
    (hr : replayR cs #[] 0 {} #[] = some (t, os)) {st : ℕ → Fin 4 → K} {val : Val} (hsat : Sat st t val) :
    AllHold cs os st val := by
  obtain ⟨-, -, -, hfacts⟩ := replayR_sound cs #[] 0 {} #[] t os inv_empty rfl (Nat.zero_le _)
    (fun j hj => absurd hj (Nat.not_lt_zero _)) hr
  intro j hj
  exact ((hfacts j hj) hj).1 st val hsat (by simp)

/-- An accepted edge: in an assignment satisfying the circuit, if a child's words carry statement `st`, every claim `st` makes at its kind's scale is one the reduction takes, and the digest the circuit reads is `st`'s two halves. -/
theorem EdgeCert.edge (c : EdgeCert) {t : State} {os : Array (List ℕ)}
    (hr : replayR c.calls #[] 0 {} #[] = some (t, os)) (hacc : c.accepts os = true)
    {stP : ℕ → Fin 4 → K} {val : Val} (hsat : Sat stP t val) {ch : ChildEdge} (hch : ch ∈ c.children)
    (st : ℕ → Fin 4 → K) (hpub : ∀ i < c.layout.len, val (ch.words.getD i 0) = st i) :
    (stmtClaims c.layout (stE st) (nodeScale ch.scale.mode (st 0))).Sub (c.claims.map (Model.ev val)) ∧
      (val (out os ch.digest 0) 0 = st 1 0 ∧ val (out os ch.digest 0) 1 = st 1 1 ∧
        val (out os ch.digest 0) 2 = st 2 0 ∧ val (out os ch.digest 0) 3 = st 2 1) := by
  have hF := allHold_of_replay hr hsat
  simp only [EdgeCert.accepts, Bool.and_eq_true, List.all_eq_true] at hacc
  obtain ⟨hL, hall⟩ := hacc
  have hok := hall ch hch
  simp only [ChildEdge.ok, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hlen, hsc⟩, hdig⟩, hd⟩, hm⟩ := hok
  have hlen3 : 3 ≤ c.layout.len := by
    simp only [Layout.len, Layout.matsAt, Layout.colsAt, Layout.rowsAt, Layout.dv]; omega
  have h0 := hpub 0 (by omega)
  have hσ : Model.ev val (ch.scale.wire os (ch.words.getD 0 0)) = nodeScale ch.scale.mode (st 0) := by
    rw [ch.scale.sem hF _ hsc, h0]
  have hx : stmtClaims c.layout (stE st) (nodeScale ch.scale.mode (st 0)) =
      (ch.claims c.layout os).map (Model.ev val) := by
    rw [ChildEdge.claims, stmtClaims_map, hσ]
    exact stmtClaims_congr hL _ fun i hi => by simp only [Function.comp_apply, Model.ev, hpub i hi, stE]
  refine ⟨?_, ?_⟩
  · rw [hx]
    refine ⟨fun d hd' => ?_, fun m hm' => ?_⟩
    · simp only [Claims.map, List.mem_map] at hd' ⊢
      obtain ⟨d', hd'', rfl⟩ := hd'
      exact ⟨d', hd d' hd'', rfl⟩
    · simp only [Claims.map, List.mem_map] at hm' ⊢
      obtain ⟨m', hm'', rfl⟩ := hm'
      exact ⟨m', hm m' hm'', rfl⟩
  · have H : Call.Holds stP val (os.getD ch.digest []) (.halvesToD (ch.words.getD 1 0) (ch.words.getD 2 0)) :=
      holds_at hF hdig
    obtain ⟨e0, e1, e2, e3, -, -⟩ := H
    rw [hpub 1 (by omega)] at e0 e1
    rw [hpub 2 (by omega)] at e2 e3
    exact ⟨e0, e1, e2, e3⟩

/-- When the reduction's claims hold, the child's statement's claims do. -/
theorem EdgeCert.edge_holds (c : EdgeCert) {t : State} {os : Array (List ℕ)}
    (hr : replayR c.calls #[] 0 {} #[] = some (t, os)) (hacc : c.accepts os = true)
    {stP : ℕ → Fin 4 → K} {val : Val} (hsat : Sat stP t val) {ch : ChildEdge} (hch : ch ∈ c.children)
    (st : ℕ → Fin 4 → K) (hpub : ∀ i < c.layout.len, val (ch.words.getD i 0) = st i)
    (tD : Dense E → Prop) (tM : Matrix E → Prop) (hin : (c.claims.map (Model.ev val)).Holds tD tM) :
    (stmtClaims c.layout (stE st) (nodeScale ch.scale.mode (st 0))).Holds tD tM :=
  hin.of_sub (c.edge hr hacc hsat hch st hpub).1

/-! Over a tree. -/

section Tree

variable {ι Ω : Type}

/-- A node's input claims: its reduction's, at its assignment. -/
def ins (cert : ι → EdgeCert) (val : ι → Ω → Val) (tD : Dense E → Prop) (tM : Matrix E → Prop) (v : ι) (ω : Ω) :
    Prop :=
  ((cert v).claims.map (Model.ev (val v ω))).Holds tD tM

/-- A node's statement: its words' claims, at the scale its parent's tier gives its kind. -/
def stmt (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (slot : ι → ℕ) (L : Layout) (st : ι → Ω → ℕ → Fin 4 → K)
    (tD : Dense E → Prop) (tM : Matrix E → Prop) (v : ι) (ω : Ω) : Prop :=
  (stmtClaims L (stE (st v ω))
    (nodeScale ((cert (T.parent v)).children.getD (slot v) default).scale.mode (st v ω 0))).Holds tD tM

/-- `TreeSound.tree_sound`'s edge premise, from accepted certificates: each node's circuit replays to `t v` with outputs `os v` and its certificate accepts, every certificate has layout `L`, each node but the root is child `slot v` of its parent's, at each outcome each node's assignment satisfies its circuit with its statement, and a parent's words for a child carry the child's statement (`hpub`). -/
theorem hedge_of_certs (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State) (os : ι → Array (List ℕ))
    (hr : ∀ v ∈ T.nodes, replayR (cert v).calls #[] 0 {} #[] = some (t v, os v))
    (hacc : ∀ v ∈ T.nodes, (cert v).accepts (os v) = true) (L : Layout) (hL : ∀ v ∈ T.nodes, (cert v).layout = L)
    (slot : ι → ℕ) (hslot : ∀ v ∈ T.nodes, v ≠ T.root → slot v < (cert (T.parent v)).children.length)
    (st : ι → Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val) (hsat : ∀ v ∈ T.nodes, ∀ ω, Sat (st v ω) (t v) (val v ω))
    (hpub : ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω, ∀ i < L.len,
      val (T.parent v) ω (((cert (T.parent v)).children.getD (slot v) default).words.getD i 0) = st v ω i)
    (tD : Dense E → Prop) (tM : Matrix E → Prop) :
    ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω, ins cert val tD tM (T.parent v) ω → stmt T cert slot L st tD tM v ω := by
  intro v hv hne ω hin
  have hp := (T.parent_mem v hv hne).1
  have hch : (cert (T.parent v)).children.getD (slot v) default ∈ (cert (T.parent v)).children := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hslot v hv hne), Option.getD_some]
    exact List.getElem_mem _
  have := (cert (T.parent v)).edge_holds (hr _ hp) (hacc _ hp) (hsat _ hp ω) hch (st v ω)
    (fun i hi => hpub v hv hne ω i (by rw [hL _ hp] at hi; exact hi)) tD tM hin
  rw [hL _ hp] at this
  exact this

/-- `TreeSound.tree_sound` with its edges from accepted certificates: off every node's `bad`, every node's statement and input claims hold. -/
theorem tree_sound_certs (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State) (os : ι → Array (List ℕ))
    (hr : ∀ v ∈ T.nodes, replayR (cert v).calls #[] 0 {} #[] = some (t v, os v))
    (hacc : ∀ v ∈ T.nodes, (cert v).accepts (os v) = true) (L : Layout) (hL : ∀ v ∈ T.nodes, (cert v).layout = L)
    (slot : ι → ℕ) (hslot : ∀ v ∈ T.nodes, v ≠ T.root → slot v < (cert (T.parent v)).children.length)
    (st : ι → Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val) (hsat : ∀ v ∈ T.nodes, ∀ ω, Sat (st v ω) (t v) (val v ω))
    (hpub : ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω, ∀ i < L.len,
      val (T.parent v) ω (((cert (T.parent v)).children.getD (slot v) default).words.getD i 0) = st v ω i)
    (tD : Dense E → Prop) (tM : Matrix E → Prop) (bad : ι → Set Ω)
    (hstep : ∀ v ∈ T.nodes, ∀ ω, ω ∉ bad v → stmt T cert slot L st tD tM v ω → ins cert val tD tM v ω)
    (hroot : ∀ ω, stmt T cert slot L st tD tM T.root ω) (ω : Ω) (hω : ∀ v ∈ T.nodes, ω ∉ bad v) :
    ∀ v ∈ T.nodes, stmt T cert slot L st tD tM v ω ∧ ins cert val tD tM v ω :=
  TreeSound.tree_sound T _ _ bad hstep
    (hedge_of_certs T cert t os hr hacc L hL slot hslot st val hsat hpub tD tM) hroot ω hω

end Tree

end LeanVMCircuits.Rec.Edges
