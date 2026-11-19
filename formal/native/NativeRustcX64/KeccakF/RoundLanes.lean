module

public import NativeRustcX64.KeccakF.Inv
public import NativeRustcX64.KeccakF.Blocks

/-!
# The loop body computes `permute`'s round (x86-64)

`body_lanes`: where the loop body runs (`body`) in an environment whose registers and frame slots
hold the lanes `a` and the parities `c` where the loop head keeps them (`laneRegs`, `laneSlots`,
`parRegs`) and whose round-constant load is `rc`, the machine after it holds the round's lanes
(`roundCL a c rc`) and new parities (`newPar a c rc`) in the same places. Each is an identity of
XORs, AND-NOTs and rotations of the inputs: rustc's reassociation and operand order, matched by
`ac_rfl` after the round's lanes are written as 64-bit vectors.
-/

namespace NativeRustcX64.KeccakF

open NativeRustcX64.Sym NativeRustc.Keccak LeanVM.Semantics

public section

/-- A rotation count of a literal below 64 is the literal. -/
theorem shiftCount_lit {n : Nat} (h : n < 64) : shiftCount .W64 (BitVec.ofNat 64 n) = n := by
  have h8 : Width.W8.bits = 8 := rfl
  simp only [shiftCount, shiftMask, low, BitVec.toNat_setWidth, BitVec.toNat_ofNat, h8]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  exact Nat.and_two_pow_sub_one_of_lt_two_pow (n := 6) (by omega)

/-- Unfolds a lane of `permute`'s round to 64-bit vector operations on its inputs. -/
macro "round_simp" : tactic => `(tactic| simp (disch := omega) only [roundCL, newPar, bC, tC,
  thetaD, chi, UInt64.toBitVec_xor, UInt64.toBitVec_and, UInt64.toBitVec_not, Nat.reduceMod,
  Nat.reduceAdd, Nat.reduceSub, reduceIte, OfNat.ofNat_ne_zero, Nat.succ_ne_zero, rot_zero,
  toBitVec_rot_left, Nat.reduceLT, Nat.lt_irrefl, Nat.zero_lt_succ])

theorem allOf_append {α : Type} {P : α → Prop} {l₁ l₂ : List α} (h₁ : AllOf P l₁)
    (h₂ : AllOf P l₂) : AllOf P (l₁ ++ l₂) := by
  induction l₁ with
  | nil => exact h₂
  | cons a l ih => exact ⟨h₁.1, ih h₁.2⟩

theorem allOf_laneSlots {P : Nat × Nat → Prop} (hA : AllOf P laneSlotsA)
    (hB : AllOf P laneSlotsB) : AllOf P laneSlots :=
  allOf_append hA hB

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem body_regs [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec Common.KeccakF.b1 startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 248)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 (env.load 0 152 8).toNat 8 = rc.toBitVec) :
    AllOf (fun p : Reg64 × Nat => m.regs.get64 p.1 = (roundCL a c rc p.2).toBitVec) laneRegs := by
  rw [body] at hx
  cases hx
  simp only [AllOf, laneRegs, laneSlots, parRegs] at hregs hslots hpar
  obtain ⟨h6, h10, h12, h20, h22, h23, h24, -⟩ := hregs
  obtain ⟨h0, h1, h2, h3, h4, h5, h7, h8, h9, h11, h13, h14, h15, h16, h17, h18, h19, h21, -⟩ := hslots
  obtain ⟨c0, c1, c2, c3, c4, -⟩ := hpar
  simp only [AllOf, laneRegs]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> refine (hm.regs _ _ rfl).trans ?_
  all_goals
    clear hm
    sym_simp
    simp (disch := omega) only [shiftCount_lit]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, c0, c1, c2, c3, c4, Nat.zero_add, hrc]
    round_simp
    ac_rfl

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem body_slotsA [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec Common.KeccakF.b1 startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 248)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 (env.load 0 152 8).toNat 8 = rc.toBitVec) :
    AllOf (fun p : Nat × Nat =>
      WordAt m.dmem (b + BitVec.ofNat 64 p.1) (roundCL a c rc p.2).toBitVec) laneSlotsA := by
  rw [body] at hx
  cases hx
  simp only [AllOf, laneRegs, laneSlots, parRegs] at hregs hslots hpar
  obtain ⟨h6, h10, h12, h20, h22, h23, h24, -⟩ := hregs
  obtain ⟨h0, h1, h2, h3, h4, h5, h7, h8, h9, h11, h13, h14, h15, h16, h17, h18, h19, h21, -⟩ := hslots
  obtain ⟨c0, c1, c2, c3, c4, -⟩ := hpar
  simp only [AllOf, laneSlotsA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;>
    refine wordAt_of_eq (wordAt_write hm hb (by decide) rfl) ?_
  all_goals
    clear hm
    sym_simp
    simp (disch := omega) only [shiftCount_lit]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, c0, c1, c2, c3, c4, Nat.zero_add, hrc]
    round_simp
    ac_rfl

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem body_slotsB [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec Common.KeccakF.b1 startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 248)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 (env.load 0 152 8).toNat 8 = rc.toBitVec) :
    AllOf (fun p : Nat × Nat =>
      WordAt m.dmem (b + BitVec.ofNat 64 p.1) (roundCL a c rc p.2).toBitVec) laneSlotsB := by
  rw [body] at hx
  cases hx
  simp only [AllOf, laneRegs, laneSlots, parRegs] at hregs hslots hpar
  obtain ⟨h6, h10, h12, h20, h22, h23, h24, -⟩ := hregs
  obtain ⟨h0, h1, h2, h3, h4, h5, h7, h8, h9, h11, h13, h14, h15, h16, h17, h18, h19, h21, -⟩ := hslots
  obtain ⟨c0, c1, c2, c3, c4, -⟩ := hpar
  simp only [AllOf, laneSlotsB]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;>
    refine wordAt_of_eq (wordAt_write hm hb (by decide) rfl) ?_
  all_goals
    clear hm
    sym_simp
    simp (disch := omega) only [shiftCount_lit]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, c0, c1, c2, c3, c4, Nat.zero_add, hrc]
    round_simp
    ac_rfl

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem body_par [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec Common.KeccakF.b1 startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 248)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 (env.load 0 152 8).toNat 8 = rc.toBitVec) :
    AllOf (fun p : Reg64 × Nat => m.regs.get64 p.1 = (newPar a c rc p.2).toBitVec) parRegs := by
  rw [body] at hx
  cases hx
  simp only [AllOf, laneRegs, laneSlots, parRegs] at hregs hslots hpar
  obtain ⟨h6, h10, h12, h20, h22, h23, h24, -⟩ := hregs
  obtain ⟨h0, h1, h2, h3, h4, h5, h7, h8, h9, h11, h13, h14, h15, h16, h17, h18, h19, h21, -⟩ := hslots
  obtain ⟨c0, c1, c2, c3, c4, -⟩ := hpar
  simp only [AllOf, parRegs]
  refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩ <;> refine (hm.regs _ _ rfl).trans ?_
  all_goals
    clear hm
    sym_simp
    simp (disch := omega) only [shiftCount_lit]
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, c0, c1, c2, c3, c4, Nat.zero_add, hrc]
    round_simp
    ac_rfl

/-- **The loop body is `permute`'s round.** -/
theorem body_lanes [Labels] {env : Env} {m : MachineData} {S : SState} {x : Exit}
    (hx : exec Common.KeccakF.b1 startBody = some (S, x)) (hm : Match env S m)
    {b : BitVec 64} (hb : env.regions[0]? = some (b, 248)) {a c : Nat → UInt64} {rc : UInt64}
    (hregs : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (a p.2).toBitVec) laneRegs)
    (hslots : AllOf (fun p : Nat × Nat => env.load 0 p.1 8 = (a p.2).toBitVec) laneSlots)
    (hpar : AllOf (fun p : Reg64 × Nat => env.regs p.1 = (c p.2).toBitVec) parRegs)
    (hrc : env.load 1 (env.load 0 152 8).toNat 8 = rc.toBitVec) :
    AllOf (fun p : Reg64 × Nat => m.regs.get64 p.1 = (roundCL a c rc p.2).toBitVec) laneRegs ∧
    AllOf (fun p : Nat × Nat =>
      WordAt m.dmem (b + BitVec.ofNat 64 p.1) (roundCL a c rc p.2).toBitVec) laneSlots ∧
    AllOf (fun p : Reg64 × Nat => m.regs.get64 p.1 = (newPar a c rc p.2).toBitVec) parRegs :=
  ⟨body_regs hx hm hb hregs hslots hpar hrc,
    allOf_laneSlots (body_slotsA hx hm hb hregs hslots hpar hrc)
      (body_slotsB hx hm hb hregs hslots hpar hrc),
    body_par hx hm hb hregs hslots hpar hrc⟩

end

end NativeRustcX64.KeccakF
