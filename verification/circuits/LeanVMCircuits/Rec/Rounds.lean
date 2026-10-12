module

public import LeanVMCircuits.Rec.UnionRows
public import LeanVMCircuits.Rec.Sumcheck

@[expose] public section

/-!
A sumcheck's rounds, read off the builder's calls.

Every sumcheck of the recursion verifier reads its round polynomials with `RoundPolynomial::read` and takes the next
claim with `poly_eval`: the prover sends every coefficient but one, and the verifier computes the fixed one from the
running claim (the linear one, `c_1 = claim + ∑_{i ≥ 2} c_i`, or with the round's eq weight `e` factored out the
constant one, `c_0 = claim + e · ∑_{i ≥ 1} c_i`), so the round's check holds by construction. The reduction's only
test is the last: the last claim against the value the verifier computes for it.

A round certificate (`RoundCert`) names the calls: the fold of the coefficients past the fixed one, the fixed
coefficient's call, the challenge, and Horner's `mul_add` per coefficient from the last. `RoundCert.ok` checks each
named call is in the replay with the wires the code gives it. A sumcheck certificate (`SumcheckCert`) chains rounds,
each round's claim the previous round's Horner output, from the reduction's input claim.

A proof-of-work certificate (`PowCert`) names `Transcript::check_pow`'s calls: the trial's compression, its words, the
split of its first word, and the tests holding the word's top `bits` bits to zero. `pow_sem`: where every replayed
call holds and the tests hold, the trial compression's first output word is below `2^(64 - bits)`.

`sumRound_sem`: in an assignment where every replayed call holds, the round polynomial `g` of the coefficients' values
has degree at most the certificate's, passes the round's check against the claim (`Sumcheck.lin`), and the next claim
is `g` at the challenge.
-/

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model Polynomial

/-- `fold(acc, |acc, &c| v.add(acc, c))`: one `add` per wire. -/
def foldCalls (os : Array (List ℕ)) (acc : ℕ) : List ℕ → List ℕ → List (ℕ × Call)
  | c :: cs, j :: js => (j, .add acc c) :: foldCalls os (outAt os j 0) cs js
  | _, _ => []

/-- The fold's output. -/
def foldOut (os : Array (List ℕ)) (acc : ℕ) : List ℕ → List ℕ → ℕ
  | _ :: cs, j :: js => foldOut os (outAt os j 0) cs js
  | _, _ => acc

/-- Horner at `x` from `acc`: one `mul_add(acc, x, c)` per wire. -/
def hornerCalls (os : Array (List ℕ)) (x acc : ℕ) : List ℕ → List ℕ → List (ℕ × Call)
  | c :: cs, j :: js => (j, .mulAdd acc x c) :: hornerCalls os x (outAt os j 0) cs js
  | _, _ => []

/-- Horner's output. -/
def hornerOut (os : Array (List ℕ)) (acc : ℕ) : List ℕ → List ℕ → ℕ
  | _ :: cs, j :: js => hornerOut os (outAt os j 0) cs js
  | _, _ => acc

/-- One round of a sumcheck: its coefficient wires, constant first, the fixed one included; its eq weight when
factored out; the calls making the fixed coefficient (a `zero`, an `add` per coefficient past the fixed one, then the
fixed one's); its challenge and Horner's calls (a `zero`, then a `mul_add` per coefficient from the last); where the
challenge is drawn (its `k_to_e` call, and for each word the `d_to_k` call, the word's place, and the squeeze); and the
number of its transcript's blocks absorbed before that squeeze. -/
structure RoundCert where
  coeffs : List ℕ
  weight : Option ℕ
  tailZero : ℕ
  tailAt : List ℕ
  fixedAt : ℕ
  chal : ℕ
  hornerZero : ℕ
  hornerAt : List ℕ
  chalAt : ℕ
  words : List (ℕ × ℕ × ℕ)
  time : ℕ
  deriving Inhabited, Repr

namespace RoundCert

variable (os : Array (List ℕ)) (rc : RoundCert)

/-- The fixed coefficient's index: the constant one with an eq weight, else the linear one. -/
def fixed : ℕ := if rc.weight.isSome then 0 else 1

/-- The coefficients past the fixed one, summed. -/
def tail : ℕ := foldOut os (o os rc.tailZero) (rc.coeffs.drop (rc.fixed + 1)) rc.tailAt

/-- The next claim: the round polynomial at the challenge. -/
def next : ℕ := hornerOut os (o os rc.hornerZero) rc.coeffs.reverse rc.hornerAt

/-- The fixed coefficient's call: `claim + e · tail` or `claim + tail`. -/
def fixedCall (claim : ℕ) : Call := match rc.weight with
  | some e => .mulAdd e (rc.tail os) claim
  | none => .add claim (rc.tail os)

/-- The round's calls. -/
def calls (claim : ℕ) : List (ℕ × Call) :=
  [(rc.tailZero, .zero), (rc.hornerZero, .zero), (rc.fixedAt, rc.fixedCall os claim)] ++
    foldCalls os (o os rc.tailZero) (rc.coeffs.drop (rc.fixed + 1)) rc.tailAt ++
    hornerCalls os rc.chal (o os rc.hornerZero) rc.coeffs.reverse rc.hornerAt

/-- The round's calls are in the replay, its polynomial has `d + 1` coefficients, and the fixed coefficient is the
fixed call's output. -/
def ok (cs : Array Call) (rl : Array Bool) (d claim : ℕ) : Bool :=
  rc.coeffs.length == d + 1 && 2 ≤ rc.coeffs.length && rc.tailAt.length + rc.fixed + 1 == rc.coeffs.length &&
    rc.hornerAt.length == rc.coeffs.length && o os rc.fixedAt == rc.coeffs.getD rc.fixed 0 &&
    callsOk cs rl (rc.calls os claim)

/-- The coefficients the prover sends: all but the fixed one. -/
def sent : List ℕ := rc.coeffs.eraseIdx rc.fixed

end RoundCert

/-- A sumcheck: its input claim, its rounds, their degree, its test (an equality of the circuit, between the last
claim and `final`) and its transcript. -/
structure SumcheckCert where
  claim0 : ℕ
  rounds : List RoundCert
  deg : ℕ
  test : ℕ
  final : ℕ
  transcript : ℕ
  deriving Inhabited, Repr

namespace SumcheckCert

variable (os : Array (List ℕ)) (sc : SumcheckCert)

/-- Round `i`'s claim: the input claim, then each round's next claim. -/
def claimAt (i : ℕ) : ℕ := if i = 0 then sc.claim0 else (sc.rounds.getD (i - 1) default).next os

/-- Every round's calls are in the replay, each round reading the claim the previous one leaves. -/
def ok (cs : Array Call) (rl : Array Bool) : Bool :=
  0 < sc.rounds.length &&
    (List.range sc.rounds.length).all fun i => (sc.rounds.getD i default).ok os cs rl sc.deg (sc.claimAt os i)

end SumcheckCert

/-- A proof-of-work check: the trial's `compress` call, the `d_to_k` of its digest, the `split` of its first word,
its difficulty, and the `eq_k_const` tests of the word's top bits, from bit `64 - bits` up. -/
structure PowCert where
  compressAt : ℕ
  dkAt : ℕ
  splitAt : ℕ
  bits : ℕ
  testAt : List ℕ
  deriving Inhabited, Repr

namespace PowCert

variable (os : Array (List ℕ)) (pc : PowCert)

/-- The trial's digest, its first word, and the word's bit `k`. -/
def trial : ℕ := o os pc.compressAt
def word : ℕ := outAt os pc.dkAt 0
def bit (k : ℕ) : ℕ := outAt os pc.splitAt k

/-- The calls are in the replay, and each top bit has its test. -/
def ok (cs : Array Call) (rl : Array Bool) : Bool :=
  pc.bits ≤ 64 && pc.testAt.length == pc.bits &&
    (match cs[pc.compressAt]? with
      | some (.compress acc x ds) =>
        callsOk cs rl [(pc.compressAt, .compress acc x ds), (pc.dkAt, .dToK (pc.trial os)),
          (pc.splitAt, .split (pc.word os))]
      | _ => false) &&
    (List.range pc.bits).all fun k => cs[pc.testAt.getD k 0]? == some (.eqConstK (pc.bit os (64 - pc.bits + k)) 0)

end PowCert

/-! What the calls give. -/

section Sem

variable {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val}

theorem callsOk_cons {x : ℕ × Call} {l : List (ℕ × Call)} (h : callsOk cs rl (x :: l) = true) :
    callsOk cs rl [x] = true ∧ callsOk cs rl l = true := by
  rw [show x :: l = [x] ++ l from rfl, callsOk_append, Bool.and_eq_true] at h
  exact h

theorem fold_sem (hF : Facts cs rl os st val) : ∀ (acc : ℕ) (ws js : List ℕ), ws.length = js.length →
    callsOk cs rl (foldCalls os acc ws js) = true →
      Model.ev val (foldOut os acc ws js) = Model.ev val acc + (ws.map (Model.ev val)).sum
  | acc, [], [], _, _ => by simp [foldOut]
  | acc, w :: ws, j :: js, hl, h => by
    obtain ⟨h1, h2⟩ := callsOk_cons h
    have hj : Model.ev val (o os j) = Model.ev val acc + Model.ev val w := holds_of_mem hF h1 (List.mem_singleton_self _)
    rw [foldOut, fold_sem hF (o os j) ws js (by simpa using hl) h2, hj, List.map_cons, List.sum_cons]
    ring
  | _, [], _ :: _, hl, _ => by simp at hl
  | _, _ :: _, [], hl, _ => by simp at hl

theorem horner_sem (hF : Facts cs rl os st val) (x : ℕ) : ∀ (acc : ℕ) (ws js : List ℕ), ws.length = js.length →
    callsOk cs rl (hornerCalls os x acc ws js) = true →
      Model.ev val (hornerOut os acc ws js) = (ws.map (Model.ev val)).foldl (fun a c => a * Model.ev val x + c) (Model.ev val acc)
  | acc, [], [], _, _ => by simp [hornerOut]
  | acc, w :: ws, j :: js, hl, h => by
    obtain ⟨h1, h2⟩ := callsOk_cons h
    have hj : Model.ev val (o os j) = Model.ev val acc * Model.ev val x + Model.ev val w := holds_of_mem hF h1 (List.mem_singleton_self _)
    rw [hornerOut, horner_sem hF x (o os j) ws js (by simpa using hl) h2, hj, List.map_cons, List.foldl_cons]
  | _, [], _ :: _, hl, _ => by simp at hl
  | _, _ :: _, [], hl, _ => by simp at hl

open Sumcheck in
/-- A round's polynomial, of the coefficients' values, has degree at most `d`, passes the round's check against the
claim, and is the next claim at the challenge. -/
theorem sumRound_sem (hF : Facts cs rl os st val) {rc : RoundCert} {d claim : ℕ}
    (hok : rc.ok os cs rl d claim = true) :
    (polyOf (rc.coeffs.map (Model.ev val))).natDegree ≤ d ∧
      lin (rc.weight.map (Model.ev val)) (polyOf (rc.coeffs.map (Model.ev val))) = Model.ev val claim ∧
      Model.ev val (rc.next os) = (polyOf (rc.coeffs.map (Model.ev val))).eval (Model.ev val rc.chal) := by
  simp only [RoundCert.ok, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨hlen, hge⟩, htl⟩, hhl⟩, hfx⟩, hcalls⟩ := hok
  simp only [RoundCert.calls, callsOk_append, Bool.and_eq_true] at hcalls
  obtain ⟨⟨hhead, hfold⟩, hhorner⟩ := hcalls
  obtain ⟨hz1, hrest⟩ := callsOk_cons hhead
  obtain ⟨hz2, hfc⟩ := callsOk_cons hrest
  have hz1' : Model.ev val (o os rc.tailZero) = 0 := holds_of_mem hF hz1 (List.mem_singleton_self _)
  have hz2' : Model.ev val (o os rc.hornerZero) = 0 := holds_of_mem hF hz2 (List.mem_singleton_self _)
  have hfc' : (rc.fixedCall os claim).Holds st val (os.getD rc.fixedAt []) :=
    holds_of_mem hF hfc (List.mem_singleton_self _)
  have htail : Model.ev val (rc.tail os) = ((rc.coeffs.drop (rc.fixed + 1)).map (Model.ev val)).sum := by
    rw [RoundCert.tail, fold_sem hF _ _ _ (by simp; omega) hfold, hz1', zero_add]
  refine ⟨(natDegree_polyOf _).trans (by simp; omega), ?_, ?_⟩
  · -- The fixed coefficient is the claim plus the tail, or the claim plus the weight times the tail.
    have hfv : Model.ev val (rc.coeffs.getD rc.fixed 0) = Model.ev val (o os rc.fixedAt) := by rw [hfx]
    match hc : rc.coeffs, hw : rc.weight with
    | c0 :: c1 :: rest, none =>
      have hfix : rc.fixed = 1 := by simp [RoundCert.fixed, hw]
      simp only [RoundCert.fixedCall, hw, Call.Holds] at hfc'
      rw [getD_o] at hfc'
      rw [hfix, hc] at htail hfv
      simp only [List.drop_succ_cons, List.drop_zero, List.getD_cons_succ, List.getD_cons_zero] at htail hfv
      rw [hfc', htail] at hfv
      simp only [Option.map_none, lin, eval_polyOf_zero, eval_polyOf_one, List.map_cons, List.sum_cons, hfv,
        List.head?_cons, Option.getD_some]
      linear_combination (Model.ev val c0 + (rest.map (Model.ev val)).sum) * two_E
    | c0 :: rest, some e =>
      have hfix : rc.fixed = 0 := by simp [RoundCert.fixed, hw]
      simp only [RoundCert.fixedCall, hw, Call.Holds] at hfc'
      rw [getD_o] at hfc'
      rw [hfix, hc] at htail hfv
      simp only [List.drop_succ_cons, List.drop_zero, List.getD_cons_zero] at htail hfv
      rw [hfc', htail] at hfv
      simp only [Option.map_some, lin, eval_polyOf_zero, eval_polyOf_one, List.map_cons, List.sum_cons, hfv,
        List.head?_cons, Option.getD_some]
      linear_combination (Model.ev val e * (rest.map (Model.ev val)).sum) * two_E
    | [], _ => simp [hc] at hge
    | [_], _ => simp [hc] at hge
  · rw [RoundCert.next, horner_sem hF _ _ _ _ (by simp; omega) hhorner, hz2', eval_polyOf, List.map_reverse,
      List.foldl_reverse]

/-- Where every replayed call holds and the proof-of-work tests hold, the trial compression's first output word is
below `2^(64 - bits)`: its top `bits` bits are zero. -/
theorem pow_sem (hF : Facts cs rl os st val) {pc : PowCert} (hok : pc.ok os cs rl = true)
    (htests : ∀ k < pc.bits, val (pc.bit os (64 - pc.bits + k)) 0 = 0) :
    ∃ acc x ds, cs[pc.compressAt]? = some (.compress acc x ds) ∧
      (Rec.node (words4 (val acc)) (words4 (xds val x ds)) 0).toNat < 2 ^ (64 - pc.bits) := by
  simp only [PowCert.ok, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hb, -⟩, hcalls⟩, -⟩ := hok
  split at hcalls
  · rename_i acc x ds hc
    refine ⟨acc, x, ds, hc, ?_⟩
    obtain ⟨h1, hrest⟩ := callsOk_cons hcalls
    obtain ⟨h2, h3⟩ := callsOk_cons hrest
    have hcomp : words4 (val (PowCert.trial os pc)) = Rec.node (words4 (val acc)) (words4 (xds val x ds)) :=
      holds_of_mem hF h1 (List.mem_singleton_self _)
    have hdk : ∀ i : Fin 4, val (outAt os pc.dkAt i) 0 = val (PowCert.trial os pc) i :=
      holds_of_mem hF h2 (List.mem_singleton_self _)
    have hsp : (∀ i < 64, val (PowCert.bit os pc i) 0 = 0 ∨ val (PowCert.bit os pc i) 0 = 1) ∧
        toWord (val (PowCert.word os pc) 0) = num (fun i => if val (PowCert.bit os pc i) 0 = 1 then 1 else 0) 64 :=
      holds_of_mem hF h3 (List.mem_singleton_self _)
    have hw : val (PowCert.word os pc) 0 = val (PowCert.trial os pc) 0 := hdk 0
    rw [← hcomp, words4, BitVec.toNat_ofNat, ← hw, hsp.2, Nat.mod_eq_of_lt (num_lt _ 64)]
    refine Nat.lt_pow_two_of_testBit _ fun i hi => ?_
    by_cases h64 : i < 64
    · rw [testBit_num _ _ _ h64]
      have := htests (i - (64 - pc.bits)) (by omega)
      rw [show 64 - pc.bits + (i - (64 - pc.bits)) = i by omega] at this
      simp [this]
    · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (num_lt _ 64) (Nat.pow_le_pow_right (by norm_num) (by omega)))
  · simp at hcalls

end Sem

end LeanVMCircuits.Rec.Bind
