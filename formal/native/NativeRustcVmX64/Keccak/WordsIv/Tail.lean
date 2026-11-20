module

public import NativeRustcVmX64.Keccak.WordsIv.Full

/-!
# `keccak256_words::<fiat_shamir_iv's closure>` (x86-64): the last block's words

From the last block's first lane (`tail_head`; RBX its first index `B = 17 nb`), lane `j < 15` is
`lane2_step` (`tail{j}`: its call and XOR blocks if index `B + j` is below the count, else its
zero block). Lane 15's blocks advance RBX to `B + 16` and branch on it (`tail15`), lane 16's word
is `iv_word`'s (`b109`) or zero (`b20`, `tail16`). `tail_run`: to the padding block with lane 16's
word in RAX.
-/

namespace NativeRustcVmX64.WordsIv

open NativeRustcX64 NativeRustcX64.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcVm.Keccak (wordBlocks)
open NativeRustcVmX64.WordsHash (frame Ctx Lanes pre RegsAt regsAt_keep regsAt_cons lane_two
  eval_posCmp add64 ctx_step lanes_keep)
open Vm.Keccak256WordsOfFiatShamirIv

@[expose] public section

/-- The state after the whole blocks. -/
abbrev stA (m0 : MachineData) : KeccakState := wordBlocks (wv m0) (nb m0)

/-- The last block's first index. -/
abbrev bT (m0 : MachineData) : Nat := 17 * nb m0

end

public section

theorem tail_small [Labels] {m0 : MachineData} (g : Geo m0) : bT m0 + 17 < 2 ^ 32 := by
  have := nb17_le g
  have := g.cnt
  have := g.len
  have := g.small
  unfold bT
  omega

/-- The branch on index `B + 16`, RBX `B + 16` already. -/
theorem cmp16_eval [Labels] {m0 : MachineData} (g : Geo m0) {env : Env} {B : Nat}
    (hx : env.regs .rbx = BitVec.ofNat 64 B) (h13 : env.regs .r13 = m0.regs.get64 .rsi)
    (hB : B + 16 < 2 ^ 32) :
    (SBool.cmp .ult .W64 (.bin .add .W64 (.lit 16) (.reg .rbx)) (.reg .r13)).eval env =
      decide (B + 16 < cnt m0) := by
  have hc := cnt_small g
  simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, add64, hx, h13]
  rw [bv_eq_ofNat (m0.regs.get64 .rsi),
    NativeRustcVmX64.WordsHash.ult_ofNat (by omega) (by unfold cnt at hc; omega)]
  rw [Nat.add_comm 16 B]
  rfl

/-- RBX `B + 16` after lane 15's blocks. -/
theorem rbx16 [Labels] {m0 m m' : MachineData} {B : Nat} {S : SState}
    (hm : Match (Env.ofMachine m [(frame m0, 296)]) S m')
    (hR : RegsAt m (RL m0 .rbx B []))
    (h : S.reg .rbx = some (.bin .add .W64 (.lit 16) (.reg .rbx)))
    (hk : WordsHash.keepsRegs S [.r13, .r12, .r15] = true) :
    RegsAt m' (RL m0 .rbx (B + 16) []) := by
  have hk' := regsAt_keep hm (R := [(.r13, m0.regs.get64 .rsi), (.r12, bc m0),
    (.r15, m0.regs.get64 .r8)]) ⟨hR.1, hR.2.1, hR.2.2.1, trivial⟩ rfl hk
  refine ⟨hk'.1, hk'.2.1, hk'.2.2.1, ?_, trivial⟩
  show m'.regs.get64 .rbx = BitVec.ofNat 64 (B + 16)
  rw [hm.regs .rbx _ h]
  simp only [Sym.eval, add64, Env.ofMachine_regs, hR.2.2.2.1, BitVec.ofNat_add_ofNat]
  congr 1
  omega

variable [Host]

theorem tail0 (hiv : Spec (label NativeRustcVmX64.ivWordLabel) NativeRustcVmX64.IvWordPre
      NativeRustcVmX64.IvWordPost) {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k (RL m0 .rbx (bT m0) []) (stA m0) (bT m0) 0 32 385 st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k (RD m0 .rbx (bT m0) [] 1) (stA m0) (bT m0) 1 391 40) st :=
  lane2_step hiv g (j := 0) (R := RL m0 .rbx (bT m0) []) (by decide) (by have := tail_small g; omega) (fun _ h => h) (fun _ h => h.2.2.2.1)
    (names := [.r13, .r12, .r15, .rbx]) rfl (by decide)
    (ic hp b3_in_code (List.cons_ne_nil _ _)) tailC0 rfl rfl rfl rfl rfl (by decide +kernel) rfl
    (ic hp b4_in_code (List.cons_ne_nil _ _)) tailX0 rfl rfl rfl (by decide +kernel)
    (posX := true) rfl (label_at hp b79_in_code rfl) rfl
    (ic hp b78_in_code (List.cons_ne_nil _ _)) tailZ0 rfl rfl rfl (by decide +kernel)
    (posZ := false) rfl (label_at hp b5_in_code rfl) rfl h

theorem tail1 (hiv : Spec (label NativeRustcVmX64.ivWordLabel) NativeRustcVmX64.IvWordPre
      NativeRustcVmX64.IvWordPost) {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k (RD m0 .rbx (bT m0) [] 1) (stA m0) (bT m0) 1 391 40 st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k (RD m0 .rbx (bT m0) [] 2) (stA m0) (bT m0) 2 399 46) st :=
  lane2_step hiv g (j := 1) (R := RD m0 .rbx (bT m0) [] 1) (by decide) (by have := tail_small g; omega) (fun _ h => h.2) (fun _ h => h.1)
    (names := [.r13, .r12, .r15, .rbx]) rfl (by decide)
    (ic hp b79_in_code (List.cons_ne_nil _ _)) tailC1 rfl rfl rfl rfl rfl (by decide +kernel) rfl
    (ic hp b80_in_code (List.cons_ne_nil _ _)) tailX1 rfl rfl rfl (by decide +kernel)
    (posX := false) rfl (label_at hp b6_in_code rfl) rfl
    (ic hp b5_in_code (List.cons_ne_nil _ _)) tailZ1 rfl rfl rfl (by decide +kernel)
    (posZ := true) rfl (label_at hp b81_in_code rfl) rfl h

theorem tail2 (hiv : Spec (label NativeRustcVmX64.ivWordLabel) NativeRustcVmX64.IvWordPre
      NativeRustcVmX64.IvWordPost) {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k (RD m0 .rbx (bT m0) [] 2) (stA m0) (bT m0) 2 399 46 st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k (RD m0 .rbx (bT m0) [] 3) (stA m0) (bT m0) 3 407 52) st :=
  lane2_step hiv g (j := 2) (R := RD m0 .rbx (bT m0) [] 2) (by decide) (by have := tail_small g; omega) (fun _ h => h.2) (fun _ h => h.1)
    (names := [.r13, .r12, .r15, .rbx]) rfl (by decide)
    (ic hp b81_in_code (List.cons_ne_nil _ _)) tailC2 rfl rfl rfl rfl rfl (by decide +kernel) rfl
    (ic hp b82_in_code (List.cons_ne_nil _ _)) tailX2 rfl rfl rfl (by decide +kernel)
    (posX := false) rfl (label_at hp b7_in_code rfl) rfl
    (ic hp b6_in_code (List.cons_ne_nil _ _)) tailZ2 rfl rfl rfl (by decide +kernel)
    (posZ := true) rfl (label_at hp b83_in_code rfl) rfl h

theorem tail3 (hiv : Spec (label NativeRustcVmX64.ivWordLabel) NativeRustcVmX64.IvWordPre
      NativeRustcVmX64.IvWordPost) {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k (RD m0 .rbx (bT m0) [] 3) (stA m0) (bT m0) 3 407 52 st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k (RD m0 .rbx (bT m0) [] 4) (stA m0) (bT m0) 4 415 58) st :=
  lane2_step hiv g (j := 3) (R := RD m0 .rbx (bT m0) [] 3) (by decide) (by have := tail_small g; omega) (fun _ h => h.2) (fun _ h => h.1)
    (names := [.r13, .r12, .r15, .rbx]) rfl (by decide)
    (ic hp b83_in_code (List.cons_ne_nil _ _)) tailC3 rfl rfl rfl rfl rfl (by decide +kernel) rfl
    (ic hp b84_in_code (List.cons_ne_nil _ _)) tailX3 rfl rfl rfl (by decide +kernel)
    (posX := false) rfl (label_at hp b8_in_code rfl) rfl
    (ic hp b7_in_code (List.cons_ne_nil _ _)) tailZ3 rfl rfl rfl (by decide +kernel)
    (posZ := true) rfl (label_at hp b85_in_code rfl) rfl h

theorem tail4 (hiv : Spec (label NativeRustcVmX64.ivWordLabel) NativeRustcVmX64.IvWordPre
      NativeRustcVmX64.IvWordPost) {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k (RD m0 .rbx (bT m0) [] 4) (stA m0) (bT m0) 4 415 58 st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k (RD m0 .rbx (bT m0) [] 5) (stA m0) (bT m0) 5 423 64) st :=
  lane2_step hiv g (j := 4) (R := RD m0 .rbx (bT m0) [] 4) (by decide) (by have := tail_small g; omega) (fun _ h => h.2) (fun _ h => h.1)
    (names := [.r13, .r12, .r15, .rbx]) rfl (by decide)
    (ic hp b85_in_code (List.cons_ne_nil _ _)) tailC4 rfl rfl rfl rfl rfl (by decide +kernel) rfl
    (ic hp b86_in_code (List.cons_ne_nil _ _)) tailX4 rfl rfl rfl (by decide +kernel)
    (posX := false) rfl (label_at hp b9_in_code rfl) rfl
    (ic hp b8_in_code (List.cons_ne_nil _ _)) tailZ4 rfl rfl rfl (by decide +kernel)
    (posZ := true) rfl (label_at hp b87_in_code rfl) rfl h

theorem tail5 (hiv : Spec (label NativeRustcVmX64.ivWordLabel) NativeRustcVmX64.IvWordPre
      NativeRustcVmX64.IvWordPost) {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k (RD m0 .rbx (bT m0) [] 5) (stA m0) (bT m0) 5 423 64 st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k (RD m0 .rbx (bT m0) [] 6) (stA m0) (bT m0) 6 431 70) st :=
  lane2_step hiv g (j := 5) (R := RD m0 .rbx (bT m0) [] 5) (by decide) (by have := tail_small g; omega) (fun _ h => h.2) (fun _ h => h.1)
    (names := [.r13, .r12, .r15, .rbx]) rfl (by decide)
    (ic hp b87_in_code (List.cons_ne_nil _ _)) tailC5 rfl rfl rfl rfl rfl (by decide +kernel) rfl
    (ic hp b88_in_code (List.cons_ne_nil _ _)) tailX5 rfl rfl rfl (by decide +kernel)
    (posX := false) rfl (label_at hp b10_in_code rfl) rfl
    (ic hp b9_in_code (List.cons_ne_nil _ _)) tailZ5 rfl rfl rfl (by decide +kernel)
    (posZ := true) rfl (label_at hp b89_in_code rfl) rfl h

theorem tail6 (hiv : Spec (label NativeRustcVmX64.ivWordLabel) NativeRustcVmX64.IvWordPre
      NativeRustcVmX64.IvWordPost) {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k (RD m0 .rbx (bT m0) [] 6) (stA m0) (bT m0) 6 431 70 st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k (RD m0 .rbx (bT m0) [] 7) (stA m0) (bT m0) 7 439 76) st :=
  lane2_step hiv g (j := 6) (R := RD m0 .rbx (bT m0) [] 6) (by decide) (by have := tail_small g; omega) (fun _ h => h.2) (fun _ h => h.1)
    (names := [.r13, .r12, .r15, .rbx]) rfl (by decide)
    (ic hp b89_in_code (List.cons_ne_nil _ _)) tailC6 rfl rfl rfl rfl rfl (by decide +kernel) rfl
    (ic hp b90_in_code (List.cons_ne_nil _ _)) tailX6 rfl rfl rfl (by decide +kernel)
    (posX := false) rfl (label_at hp b11_in_code rfl) rfl
    (ic hp b10_in_code (List.cons_ne_nil _ _)) tailZ6 rfl rfl rfl (by decide +kernel)
    (posZ := true) rfl (label_at hp b91_in_code rfl) rfl h

theorem tail7 (hiv : Spec (label NativeRustcVmX64.ivWordLabel) NativeRustcVmX64.IvWordPre
      NativeRustcVmX64.IvWordPost) {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k (RD m0 .rbx (bT m0) [] 7) (stA m0) (bT m0) 7 439 76 st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k (RD m0 .rbx (bT m0) [] 8) (stA m0) (bT m0) 8 447 82) st :=
  lane2_step hiv g (j := 7) (R := RD m0 .rbx (bT m0) [] 7) (by decide) (by have := tail_small g; omega) (fun _ h => h.2) (fun _ h => h.1)
    (names := [.r13, .r12, .r15, .rbx]) rfl (by decide)
    (ic hp b91_in_code (List.cons_ne_nil _ _)) tailC7 rfl rfl rfl rfl rfl (by decide +kernel) rfl
    (ic hp b92_in_code (List.cons_ne_nil _ _)) tailX7 rfl rfl rfl (by decide +kernel)
    (posX := false) rfl (label_at hp b12_in_code rfl) rfl
    (ic hp b11_in_code (List.cons_ne_nil _ _)) tailZ7 rfl rfl rfl (by decide +kernel)
    (posZ := true) rfl (label_at hp b93_in_code rfl) rfl h

theorem tail8 (hiv : Spec (label NativeRustcVmX64.ivWordLabel) NativeRustcVmX64.IvWordPre
      NativeRustcVmX64.IvWordPost) {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k (RD m0 .rbx (bT m0) [] 8) (stA m0) (bT m0) 8 447 82 st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k (RD m0 .rbx (bT m0) [] 9) (stA m0) (bT m0) 9 455 88) st :=
  lane2_step hiv g (j := 8) (R := RD m0 .rbx (bT m0) [] 8) (by decide) (by have := tail_small g; omega) (fun _ h => h.2) (fun _ h => h.1)
    (names := [.r13, .r12, .r15, .rbx]) rfl (by decide)
    (ic hp b93_in_code (List.cons_ne_nil _ _)) tailC8 rfl rfl rfl rfl rfl (by decide +kernel) rfl
    (ic hp b94_in_code (List.cons_ne_nil _ _)) tailX8 rfl rfl rfl (by decide +kernel)
    (posX := false) rfl (label_at hp b13_in_code rfl) rfl
    (ic hp b12_in_code (List.cons_ne_nil _ _)) tailZ8 rfl rfl rfl (by decide +kernel)
    (posZ := true) rfl (label_at hp b95_in_code rfl) rfl h

theorem tail9 (hiv : Spec (label NativeRustcVmX64.ivWordLabel) NativeRustcVmX64.IvWordPre
      NativeRustcVmX64.IvWordPost) {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k (RD m0 .rbx (bT m0) [] 9) (stA m0) (bT m0) 9 455 88 st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k (RD m0 .rbx (bT m0) [] 10) (stA m0) (bT m0) 10 463 94) st :=
  lane2_step hiv g (j := 9) (R := RD m0 .rbx (bT m0) [] 9) (by decide) (by have := tail_small g; omega) (fun _ h => h.2) (fun _ h => h.1)
    (names := [.r13, .r12, .r15, .rbx]) rfl (by decide)
    (ic hp b95_in_code (List.cons_ne_nil _ _)) tailC9 rfl rfl rfl rfl rfl (by decide +kernel) rfl
    (ic hp b96_in_code (List.cons_ne_nil _ _)) tailX9 rfl rfl rfl (by decide +kernel)
    (posX := false) rfl (label_at hp b14_in_code rfl) rfl
    (ic hp b13_in_code (List.cons_ne_nil _ _)) tailZ9 rfl rfl rfl (by decide +kernel)
    (posZ := true) rfl (label_at hp b97_in_code rfl) rfl h

theorem tail10 (hiv : Spec (label NativeRustcVmX64.ivWordLabel) NativeRustcVmX64.IvWordPre
      NativeRustcVmX64.IvWordPost) {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k (RD m0 .rbx (bT m0) [] 10) (stA m0) (bT m0) 10 463 94 st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k (RD m0 .rbx (bT m0) [] 11) (stA m0) (bT m0) 11 471 100) st :=
  lane2_step hiv g (j := 10) (R := RD m0 .rbx (bT m0) [] 10) (by decide) (by have := tail_small g; omega) (fun _ h => h.2) (fun _ h => h.1)
    (names := [.r13, .r12, .r15, .rbx]) rfl (by decide)
    (ic hp b97_in_code (List.cons_ne_nil _ _)) tailC10 rfl rfl rfl rfl rfl (by decide +kernel) rfl
    (ic hp b98_in_code (List.cons_ne_nil _ _)) tailX10 rfl rfl rfl (by decide +kernel)
    (posX := false) rfl (label_at hp b15_in_code rfl) rfl
    (ic hp b14_in_code (List.cons_ne_nil _ _)) tailZ10 rfl rfl rfl (by decide +kernel)
    (posZ := true) rfl (label_at hp b99_in_code rfl) rfl h

theorem tail11 (hiv : Spec (label NativeRustcVmX64.ivWordLabel) NativeRustcVmX64.IvWordPre
      NativeRustcVmX64.IvWordPost) {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k (RD m0 .rbx (bT m0) [] 11) (stA m0) (bT m0) 11 471 100 st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k (RD m0 .rbx (bT m0) [] 12) (stA m0) (bT m0) 12 479 106) st :=
  lane2_step hiv g (j := 11) (R := RD m0 .rbx (bT m0) [] 11) (by decide) (by have := tail_small g; omega) (fun _ h => h.2) (fun _ h => h.1)
    (names := [.r13, .r12, .r15, .rbx]) rfl (by decide)
    (ic hp b99_in_code (List.cons_ne_nil _ _)) tailC11 rfl rfl rfl rfl rfl (by decide +kernel) rfl
    (ic hp b100_in_code (List.cons_ne_nil _ _)) tailX11 rfl rfl rfl (by decide +kernel)
    (posX := false) rfl (label_at hp b16_in_code rfl) rfl
    (ic hp b15_in_code (List.cons_ne_nil _ _)) tailZ11 rfl rfl rfl (by decide +kernel)
    (posZ := true) rfl (label_at hp b101_in_code rfl) rfl h

theorem tail12 (hiv : Spec (label NativeRustcVmX64.ivWordLabel) NativeRustcVmX64.IvWordPre
      NativeRustcVmX64.IvWordPost) {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k (RD m0 .rbx (bT m0) [] 12) (stA m0) (bT m0) 12 479 106 st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k (RD m0 .rbx (bT m0) [] 13) (stA m0) (bT m0) 13 487 112) st :=
  lane2_step hiv g (j := 12) (R := RD m0 .rbx (bT m0) [] 12) (by decide) (by have := tail_small g; omega) (fun _ h => h.2) (fun _ h => h.1)
    (names := [.r13, .r12, .r15, .rbx]) rfl (by decide)
    (ic hp b101_in_code (List.cons_ne_nil _ _)) tailC12 rfl rfl rfl rfl rfl (by decide +kernel) rfl
    (ic hp b102_in_code (List.cons_ne_nil _ _)) tailX12 rfl rfl rfl (by decide +kernel)
    (posX := false) rfl (label_at hp b17_in_code rfl) rfl
    (ic hp b16_in_code (List.cons_ne_nil _ _)) tailZ12 rfl rfl rfl (by decide +kernel)
    (posZ := true) rfl (label_at hp b103_in_code rfl) rfl h

theorem tail13 (hiv : Spec (label NativeRustcVmX64.ivWordLabel) NativeRustcVmX64.IvWordPre
      NativeRustcVmX64.IvWordPost) {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k (RD m0 .rbx (bT m0) [] 13) (stA m0) (bT m0) 13 487 112 st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k (RD m0 .rbx (bT m0) [] 14) (stA m0) (bT m0) 14 495 118) st :=
  lane2_step hiv g (j := 13) (R := RD m0 .rbx (bT m0) [] 13) (by decide) (by have := tail_small g; omega) (fun _ h => h.2) (fun _ h => h.1)
    (names := [.r13, .r12, .r15, .rbx]) rfl (by decide)
    (ic hp b103_in_code (List.cons_ne_nil _ _)) tailC13 rfl rfl rfl rfl rfl (by decide +kernel) rfl
    (ic hp b104_in_code (List.cons_ne_nil _ _)) tailX13 rfl rfl rfl (by decide +kernel)
    (posX := false) rfl (label_at hp b18_in_code rfl) rfl
    (ic hp b17_in_code (List.cons_ne_nil _ _)) tailZ13 rfl rfl rfl (by decide +kernel)
    (posZ := true) rfl (label_at hp b105_in_code rfl) rfl h

theorem tail14 (hiv : Spec (label NativeRustcVmX64.ivWordLabel) NativeRustcVmX64.IvWordPre
      NativeRustcVmX64.IvWordPost) {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k (RD m0 .rbx (bT m0) [] 14) (stA m0) (bT m0) 14 495 118 st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k (RD m0 .rbx (bT m0) [] 15) (stA m0) (bT m0) 15 503 124) st :=
  lane2_step hiv g (j := 14) (R := RD m0 .rbx (bT m0) [] 14) (by decide) (by have := tail_small g; omega) (fun _ h => h.2) (fun _ h => h.1)
    (names := [.r13, .r12, .r15, .rbx]) rfl (by decide)
    (ic hp b105_in_code (List.cons_ne_nil _ _)) tailC14 rfl rfl rfl rfl rfl (by decide +kernel) rfl
    (ic hp b106_in_code (List.cons_ne_nil _ _)) tailX14 rfl rfl rfl (by decide +kernel)
    (posX := false) rfl (label_at hp b19_in_code rfl) rfl
    (ic hp b18_in_code (List.cons_ne_nil _ _)) tailZ14 rfl rfl rfl (by decide +kernel)
    (posZ := true) rfl (label_at hp b107_in_code rfl) rfl h

/-- **Lane 15**: its blocks advance RBX to `B + 16` and branch on it. -/
theorem tail15 (hiv : Spec (label NativeRustcVmX64.ivWordLabel) NativeRustcVmX64.IvWordPre
      NativeRustcVmX64.IvWordPost) {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k (RD m0 .rbx (bT m0) [] 15) (stA m0) (bT m0) 15 503 124 st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k (RL m0 .rbx (bT m0 + 16) []) (stA m0) (bT m0) 16 511 130) st := by
  have hB := tail_small g
  refine lane_two (fun m hc hl hin => ?_) (fun m hc hl hz => ?_) h
  · have hRL := hc.regs.2
    refine Eventually.bind (call_step hiv g hc hl (ic hp b107_in_code (List.cons_ne_nil _ _))
      tailC15 rfl rfl rfl rfl rfl hRL.2.1 hRL.2.2.1 hc.regs.1 hin hRL
      (names := [.r13, .r12, .r15, .rbx]) rfl (by decide +kernel) (by decide) rfl) fun st h => ?_
    exact xorV_step g (j := 15) (R := RL m0 .rbx (bT m0) []) (by decide) h
      (ic hp b108_in_code (List.cons_ne_nil _ _)) tailX15 rfl rfl
      (fun _ _ hR hm => rbx16 hm hR rfl (by decide +kernel)) rfl
      (fun _ hR => eval_posCmp (cmp16_eval g hR.2.2.2.1 hR.1 (by omega)) false)
      (label_at hp b20_in_code rfl) rfl
  · exact zero_step g (j := 15) (by decide) hz hc hl (ic hp b19_in_code (List.cons_ne_nil _ _))
      tailZ15 rfl rfl (fun _ hm => rbx16 hm hc.regs.2 rfl (by decide +kernel)) rfl
      (eval_posCmp (cmp16_eval g hc.regs.2.2.2.2.1 hc.regs.2.1 (by omega)) true)
      (label_at hp b109_in_code rfl) rfl

/-- **Lane 16's word in RAX**: `iv_word`'s (`b109`) or zero (`b20`), at the padding block. -/
theorem tail16 (hiv : Spec (label NativeRustcVmX64.ivWordLabel) NativeRustcVmX64.IvWordPre
      NativeRustcVmX64.IvWordPost) {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k (RL m0 .rbx (bT m0 + 16) []) (stA m0) (bT m0) 16 511 130 st) :
    Eventually (step1 Host.exe) (ValAt m0 k (RL m0 .rbx (bT m0 + 16) []) (stA m0) (bT m0) 16 516) st := by
  refine lane_two (fun m hc hl hin => ?_) (fun m hc hl hz => ?_) h
  · exact call_step hiv g hc hl (ic hp b109_in_code (List.cons_ne_nil _ _)) tailC16 rfl rfl rfl rfl
      rfl hc.regs.2.1 hc.regs.2.2.1 hc.regs.2.2.2.1 hin hc.regs
      (names := [.r13, .r12, .r15, .rbx]) rfl (by decide +kernel) (by decide) rfl
  · obtain ⟨hwf, hm⟩ := main_env g.stk hc (vars := fun _ => 0) (ret := 0)
    refine exec_then (ic hp b20_in_code (List.cons_ne_nil _ _)) tailZ16 hwf (fun _ h => by cases h)
      hm fun st hm' hpc => .done _ ⟨?_, ?_, ?_, ?_⟩
    · exact ctx_step g.stk (slotsI_low m0) hc hm' hwf rfl rfl rfl
        (regsAt_keep hm' hc.regs (names := [.r13, .r12, .r15, .rbx]) rfl (by decide +kernel))
    · exact lanes_keep hm' rfl (fun w hw => by cases hw) hl
    · rw [hm'.regs .rax _ rfl, wv_of_ge hz]
      rfl
    · simp only [PcOk] at hpc
      rw [hpc]
      exact label_at hp b110_in_code rfl

/-- **The last block's words**: from its first lane to the padding block, lane 16's word in
RAX. -/
theorem tail_run (hiv : Spec (label NativeRustcVmX64.ivWordLabel) NativeRustcVmX64.IvWordPre
      NativeRustcVmX64.IvWordPost) {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k (RL m0 .rbx (bT m0) []) (stA m0) (bT m0) 0 32 385 st) :
    Eventually (step1 Host.exe) (ValAt m0 k (RL m0 .rbx (bT m0 + 16) []) (stA m0) (bT m0) 16 516) st := by
  refine Eventually.bind (tail0 hiv hp g h) fun st h => ?_
  refine Eventually.bind (tail1 hiv hp g h) fun st h => ?_
  refine Eventually.bind (tail2 hiv hp g h) fun st h => ?_
  refine Eventually.bind (tail3 hiv hp g h) fun st h => ?_
  refine Eventually.bind (tail4 hiv hp g h) fun st h => ?_
  refine Eventually.bind (tail5 hiv hp g h) fun st h => ?_
  refine Eventually.bind (tail6 hiv hp g h) fun st h => ?_
  refine Eventually.bind (tail7 hiv hp g h) fun st h => ?_
  refine Eventually.bind (tail8 hiv hp g h) fun st h => ?_
  refine Eventually.bind (tail9 hiv hp g h) fun st h => ?_
  refine Eventually.bind (tail10 hiv hp g h) fun st h => ?_
  refine Eventually.bind (tail11 hiv hp g h) fun st h => ?_
  refine Eventually.bind (tail12 hiv hp g h) fun st h => ?_
  refine Eventually.bind (tail13 hiv hp g h) fun st h => ?_
  refine Eventually.bind (tail14 hiv hp g h) fun st h => ?_
  refine Eventually.bind (tail15 hiv hp g h) fun st h => ?_
  exact tail16 hiv hp g h

end

end NativeRustcVmX64.WordsIv
