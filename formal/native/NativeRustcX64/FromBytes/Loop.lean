module

public import NativeRustcX64.FromBytes.Inv
meta import NativeRustcX64.FromBytes.Inv
meta import NativeRustcX64.Code.Xmss.FromBytes

/-!
# `from_bytes`'s closure: the loop over the chain values

Blocks 2, 3 and 4, one turn per pair of chain values, `i < 29`: the bounds checks
`pos + 32 i + 16 < 2389` and `≤ 2372` hold, the cursor becomes `pos + 32 i + 48`, and values
`2 i`, `2 i + 1` (32 bytes of the signature from `pos + 16 + 32 i`) are copied to the frame at
`24 + 32 i` (stack offsets). A fresh environment per turn: region 0 the cursor, 1 the values read,
2 their slot in the frame; the address sums `rcx + rax` and `rsi + rax` are aliases of regions 1
and 2. `loop`: from the head before turn `0` to the end of the loop (`LoopDone`).
-/

namespace NativeRustcX64.Xmss.FromBytes

open NativeRustcX64.Sym

set_option Elab.async false

/-- The symbolic state at the loop's head. -/
@[expose] public def stL : SState := init [8, 32, 32] [(.r15, .ptr 0 0)] [] []
  [(.bin .add .W64 (.reg .rcx) (.reg .rax), (1, 16)),
    (.bin .add .W64 (.reg .rsi) (.reg .rax), (2, 0))]

sym_block b2_execL := exec b2 stL

/-- After block 2. -/
@[expose] public def stL1 : SState := ((exec b2 stL).getD (stL, .fall)).1

sym_block b3_execL := exec b3 stL1

/-- After block 3. -/
@[expose] public def stL2 : SState := ((exec b3 stL1).getD (stL, .fall)).1

sym_block b4_execL := exec b4 stL2

/-- After block 4. -/
@[expose] public def stL3 : SState := ((exec b4 stL2).getD (stL, .fall)).1

theorem stL3_chain : ∀ t < 32,
    findWrite 2 (0 + t) stL3.mem = some (.load 1 (8 * (t / 8)) 8, t % 8) := by decide +kernel

theorem stL3_cursor : ∀ t < 8, findWrite 0 (0 + t) stL3.mem =
    some (.bin .add .W64 (.lit 48) (.bin .add .W64 (.reg .rdi) (.reg .rax)), t) := by
  decide +kernel

theorem stL3_writes : writesBelow stL3 [(0, 8), (2, 32)] = true := by decide +kernel

theorem stL3_keeps : ∀ r ∈ [Reg64.rbx, .rbp, .rcx, .rsi, .rdi, .rsp, .r14],
    stL3.reg r = some (.reg r) := by decide +kernel

theorem stL3_regs : stL3.reg .rax = some (.bin .add .W64 (.reg .rax) (.lit 32)) ∧
    stL3.reg .rdx = some (.reg .rax) ∧ stL3.reg .r15 = some (.ptr 0 0) := by decide +kernel

/-- The environment of turn `i`. -/
@[expose] public def envL (m₀ m : MachineData) (i : Nat) : Env :=
  Env.ofMachine m [(cur m₀, 8), (sig m₀ + BitVec.ofNat 64 (pos m₀ + 16 + 32 * i), 32),
    (base m₀ + BitVec.ofNat 64 (24 + 32 * i), 32)]

section
variable {m₀ m : MachineData} {i : Nat}

theorem envL_wf (P : Pre m₀) (hi : i < 29) (C : Common m₀ m) : (envL m₀ m i).WF := by
  have := P.pos
  exact Env.wf_of ⟨⟨P.curMapped.kept C.kept, P.curNW⟩,
    ⟨(P.sigMapped.sub (by omega)).kept C.kept, NoWrap.sub P.sigNW (by omega)⟩,
    ⟨(P.stackMapped.sub (by omega)).kept C.kept, P.baseNW.sub (by omega)⟩, trivial⟩
    (pairwise3 (P.curSig.sub_right P.sigNW (by omega) (by omega))
      (P.curF.sub_right P.baseNW (by omega) (by omega))
      ((P.sigF.sub_left P.sigNW (by omega) (by omega)).sub_right P.baseNW (by omega) (by omega)))

theorem match_envL [Labels] (h : LoopAt m₀ m i) : Match (envL m₀ m i) stL m := by
  unfold envL stL
  apply match_ofMachine
  · exact ⟨rfl, rfl, rfl, trivial⟩
  · exact ⟨h.common.r15.trans (by simp [Sym.eval, Env.base]), trivial⟩
  · exact trivial
  · exact trivial
  · refine ⟨?_, ?_, trivial⟩
    · simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, h.rcx, h.rax,
        Env.base_ofMachine_eq, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some,
        Option.getD_some]
      rw [show (BitVec.ofInt 64 (16 : Int)) = BitVec.ofNat 64 16 from rfl, addr_add_addr,
        addr_add_addr, show pos m₀ + 32 + 32 * i = pos m₀ + 16 + 32 * i + 16 by omega]
    · simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, h.rsi, h.rax,
        Env.base_ofMachine_eq, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some,
        Option.getD_some]
      rw [show (BitVec.ofInt 64 (0 : Int)) = 0#64 from rfl, BitVec.add_zero, addr_add_addr]

/-- A byte of the stack outside turn `i`'s slot is outside the turn's regions. -/
theorem envL_outside (P : Pre m₀) (hi : i < 29) {o : Nat}
    (ho : o < 24 + 32 * i ∨ 56 + 32 * i ≤ o) (ho' : o < 1928) :
    (envL m₀ m i).Outside (base m₀ + BitVec.ofNat 64 o) := by
  have := P.pos
  exact Env.outside_of_apart ⟨P.curF.sub_right P.baseNW (by omega) (by omega),
    (P.sigF.sub_left P.sigNW (by omega) (by omega)).sub_right P.baseNW (by omega) (by omega),
    apart_offsets P.baseNW (by omega) (by omega) (by omega) (by omega) (by omega), trivial⟩

/-- Bytes of the stack outside turn `i`'s slot are kept. -/
theorem keep_stackL [Labels] (P : Pre m₀) (hi : i < 29) {S : SState} {m' : MachineData}
    (hm : Match (envL m₀ m i) S m') {o : Nat} {bs : List UInt8}
    (ho : o + bs.length ≤ 24 + 32 * i ∨ 56 + 32 * i ≤ o) (ho' : o + bs.length ≤ 1928)
    (h : BytesAt m.dmem (base m₀ + BitVec.ofNat 64 o) bs) :
    BytesAt m'.dmem (base m₀ + BitVec.ofNat 64 o) bs :=
  hm.bytesAt_outside (fun t ht => by
    rw [addr_add_addr]
    exact envL_outside P hi (by omega) (by omega)) h

end

theorem ofNat_add_lit (x c : Nat) :
    BitVec.ofNat 64 x + BitVec.ofNat 64 c = BitVec.ofNat 64 (x + c) := (BitVec.ofNat_add x c).symm

theorem lit_add_ofNat (x c : Nat) :
    BitVec.ofNat 64 c + BitVec.ofNat 64 x = BitVec.ofNat 64 (x + c) := by
  rw [BitVec.add_comm, ofNat_add_lit]

/-- What a turn leaves. -/
structure AfterTurn (m₀ m : MachineData) (i : Nat) : Prop where
  common : Common m₀ m
  rbx : m.regs.get64 .rbx = out m₀
  r14 : m.regs.get64 .r14 = sig m₀
  rax : m.regs.get64 .rax = BitVec.ofNat 64 (32 * (i + 1))
  rdx : m.regs.get64 .rdx = BitVec.ofNat 64 (32 * i)
  rdi : m.regs.get64 .rdi = BitVec.ofNat 64 (pos m₀)
  rcx : m.regs.get64 .rcx = sig m₀ + BitVec.ofNat 64 (pos m₀ + 32)
  rsi : m.regs.get64 .rsi = base m₀ + BitVec.ofNat 64 24
  cursor : BytesAt m.dmem (cur m₀) (regBytes (BitVec.ofNat 64 (pos m₀ + 16 + 32 * (i + 1))))
  chain : ∀ j < 2 * (i + 1),
    BytesAt m.dmem (base m₀ + BitVec.ofNat 64 (24 + 16 * j)) (chainSlot m₀ j)

/-- The machine state after a turn. -/
theorem afterTurn [Labels] {m₀ m m' : MachineData} {i : Nat} (P : Pre m₀)
    (h : LoopAt m₀ m i) (hm : Match (envL m₀ m i) stL3 m') : AfterTurn m₀ m' i := by
  have C := h.common
  have hi := h.lt
  have hwf := envL_wf P hi C
  have := P.pos
  have hk := stL3_keeps
  have hreg : ∀ r ∈ [Reg64.rbx, .rbp, .rcx, .rsi, .rdi, .rsp, .r14],
      m'.regs.get64 r = m.regs.get64 r := fun r hr => hm.regs r _ (hk r hr)
  obtain ⟨hax, hdx, h15⟩ := stL3_regs
  refine ⟨⟨(hm.regs .r15 _ h15).trans (by simp [Sym.eval, Env.base, envL, cur]),
    (hreg .rbp (by simp)).trans C.rbp, (hreg .rsp (by simp)).trans C.rsp, ?_,
    C.kept.trans (hm.kept hwf),
    fun j hj => keep_stackL P hi hm (by simp [length_regBytes]; omega)
      (by simp [length_regBytes]; omega) (C.save j hj), ?_⟩,
    (hreg .rbx (by simp)).trans h.rbx, (hreg .r14 (by simp)).trans h.r14, ?_, ?_,
    (hreg .rdi (by simp)).trans h.rdi, (hreg .rcx (by simp)).trans h.rcx,
    (hreg .rsi (by simp)).trans h.rsi, ?_, ?_⟩
  · refine (C.same.trans (hm.sameOutside_below hwf stL3_writes)).mono fun p hp => ?_
    rcases hp with hp | ⟨rb, hrb, b, sz, hb, hin⟩
    · exact hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hrb
      rcases hrb with rfl | rfl
      · simp only [envL, Env.ofMachine_regions] at hb
        cases hb
        exact Or.inr hin
      · simp only [envL, Env.ofMachine_regions] at hb
        cases hb
        exact P.stack_scratch (by omega) hin
  · exact keep_stackL (o := 8) P hi hm (by rw [P.rand_length]; omega) (by rw [P.rand_length]; omega)
      C.rand
  · rw [hm.regs .rax _ hax]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, envL, h.rax,
      ofNat_add_lit]
    rw [show 32 * i + 32 = 32 * (i + 1) by omega]
  · rw [hm.regs .rdx _ hdx]
    exact h.rax
  · have := bytesAt_add_zero
      (hm.bytesAt_write (r := 0) (o := 0) (n := 8) rfl (by omega) stL3_cursor)
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, envL, h.rax, h.rdi,
      ofNat_add_lit] at this
    rw [show pos m₀ + 16 + 32 * (i + 1) = 48 + (pos m₀ + 32 * i) by omega]
    simpa [regBytes] using this
  · intro j hj
    by_cases hji : j < 2 * i
    · exact keep_stackL P hi hm (by rw [P.chainSlot_length (by omega)]; omega)
        (by rw [P.chainSlot_length (by omega)]; omega) (h.chain j hji)
    · obtain ⟨u, hu, rfl⟩ : ∃ u < 2, j = 2 * i + u := ⟨j - 2 * i, by omega, by omega⟩
      refine bytesAt_slice (by omega) fun t ht => ?_
      have hg := hm.get?_load (r := 2) rfl (by omega) (stL3_chain (16 * u + t) (by omega))
        (by omega) (le_refl 8)
      simp only [Nat.zero_add] at hg
      rw [addr_add_addr, show 24 + 16 * (2 * i + u) + t = 24 + 32 * i + (16 * u + t) by omega,
        ← addr_add_addr, hg, show 8 * ((16 * u + t) / 8) + (16 * u + t) % 8 = 16 * u + t by omega]
      simp only [Env.base, envL, Env.ofMachine_regions, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.map_some, Option.getD_some, Env.ofMachine_mem0,
        addr_add_addr]
      rw [show pos m₀ + 16 + 32 * i + (16 * u + t) = pos m₀ + 16 + 16 * (2 * i + u) + t by omega,
        C.same _ (P.sig_not_scratch (by omega))]
      rfl

/-- **A turn of the loop**: from the head before turn `i`, the head before turn `i + 1`, or the
loop's end after the last turn. -/
theorem turn [Host] {k : Nat} (hp : Placed code k) {m₀ : MachineData} (P : Pre m₀) {i : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcX64.Xmss.FromBytes.b2Offset)) (h : LoopAt m₀ st.data i) :
    Eventually (step1 Host.exe) (fun st' => (st'.pc = Host.addrOf (k + NativeRustcX64.Xmss.FromBytes.b5Offset) ∧ LoopDone m₀ st'.data) ∨
      (i + 1 < 29 ∧ st'.pc = Host.addrOf (k + NativeRustcX64.Xmss.FromBytes.b2Offset) ∧ LoopAt m₀ st'.data (i + 1))) st := by
  have hi := h.lt
  have hwf := envL_wf P hi h.common
  have := P.pos
  have h2 : (SBool.not (SBool.cmp .ult .W64
      (.bin .add .W64 (.lit 16) (.bin .add .W64 (.reg .rdi) (.reg .rax))) (.lit 2389))).eval
      (envL m₀ st.data i) = false := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply, low_W64, ext_W64,
      Env.ofMachine_regs, envL, h.rax, h.rdi, ofNat_add_lit]
    simp [BitVec.ult]
    omega
  refine cond_step (b2_in_code.trans hp.1 (List.cons_ne_nil _ _)) b2_execL hwf hpc (match_envL h)
    h2 fun st₁ hpc₁ hm₁ => ?_
  have h3 : (SBool.and (SBool.not (SBool.cmp .ult .W64
      (.bin .add .W64 (.lit 16) (.bin .add .W64 (.reg .rdi) (.reg .rax))) (.lit 2372)))
      (SBool.not (SBool.cmp .eq .W64
      (.bin .add .W64 (.lit 16) (.bin .add .W64 (.reg .rdi) (.reg .rax))) (.lit 2372)))).eval
      (envL m₀ st.data i) = false := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply, low_W64, ext_W64,
      Env.ofMachine_regs, envL, h.rax, h.rdi, ofNat_add_lit]
    simp [BitVec.ult, BitVec.toNat_eq]
    omega
  refine cond_step (b3_in_code.trans hp.1 (List.cons_ne_nil _ _)) b3_execL hwf hpc₁ hm₁ h3
    fun st₂ hpc₂ hm₂ => ?_
  refine exec_at (b4_in_code.trans hp.1 (List.cons_ne_nil _ _)) b4_execL hwf
    (fun _ h => nomatch h) hpc₂ hm₂ fun st₃ hm₃ hpc₃ => ?_
  have hm : Match (envL m₀ st.data i) stL3 st₃.data := by unfold stL3; rw [b4_execL]; exact hm₃
  have A := afterTurn P h hm
  refine .done _ ?_
  have hc : (SBool.not (SBool.cmp .eq .W64 (.bin .add .W64 (.reg .rax) (.lit 32)) (.lit 928))).eval
      (envL m₀ st.data i) = decide (i + 1 < 29) := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply, low_W64, ext_W64,
      Env.ofMachine_regs, envL, h.rax, ofNat_add_lit]
    by_cases hlt : i + 1 < 29
    · simp only [hlt, decide_true, Bool.not_eq_true']
      simp [BitVec.toNat_eq]
      omega
    · simp only [hlt, decide_false, Bool.not_eq_false']
      simp [BitVec.toNat_eq]
      omega
  simp only [PcOk, hc] at hpc₃
  by_cases hlt : i + 1 < 29
  · simp only [hlt, decide_true, ite_true] at hpc₃
    exact Or.inr ⟨hlt, hpc₃.trans (hp.label NativeRustcX64.Xmss.FromBytes.label_2_at),
      ⟨A.common, hlt, A.rbx, A.r14, A.rax, A.rdi, A.rcx, A.rsi, A.cursor, A.chain⟩⟩
  · simp only [hlt, decide_false, Bool.false_eq_true, ite_false] at hpc₃
    have hi' : i = 28 := by omega
    subst hi'
    exact Or.inl ⟨hpc₃, ⟨A.common, A.rbx, A.r14, A.rdi, A.rdx, A.rsi, A.cursor, A.chain⟩⟩

/-- **The loop over the chain values**: from its head before turn `0` to its end. -/
public theorem loop [Host] {k : Nat} (hp : Placed code k) {m₀ : MachineData} (P : Pre m₀)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcX64.Xmss.FromBytes.b2Offset)) (h : LoopAt m₀ st.data 0) :
    Eventually (step1 Host.exe) (fun st' => st'.pc = Host.addrOf (k + NativeRustcX64.Xmss.FromBytes.b5Offset) ∧ LoopDone m₀ st'.data)
      st :=
  Sym.loop (I := fun n s => ∃ i, i + n = 29 ∧ 0 < n ∧ s.pc = Host.addrOf (k + NativeRustcX64.Xmss.FromBytes.b2Offset) ∧
      LoopAt m₀ s.data i)
    (fun n s ⟨i, hn, hn0, hpc, h⟩ => NativeRustcX64.Eventually.mono (turn hp P hpc h)
      fun s' h' => by
      rcases h' with h' | ⟨hlt, hpc', h'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨n - 1, by omega, i + 1, by omega, by omega, hpc', h'⟩)
    (n := 29) ⟨0, rfl, by decide, hpc, h⟩

end NativeRustcX64.Xmss.FromBytes
