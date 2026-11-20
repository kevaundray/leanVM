module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.FoldRow
public import NativeRustcVmX64.KeccakGkr.KeccakOpen.FoldAddress
public import NativeRustcVmX64.KeccakGkr.KeccakOpen.ExecL
public import NativeRustcVmX64.KeccakGkr.KeccakOpen.ExecS
public import NativeRustcVmX64.KeccakGkr.KeccakOpen.ExecR01

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.KeccakOpen
open NativeRustcVm.Transcript (off DecArea)

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}
  {cx : Cx} {rows : Array (Array EW)}

theorem row0 (hp : Placed code k) (h : PreOk a s c m0)
    (hcpy : Spec (Labels.label "memcpy") MemcpyPre MemcpyPost)
    (hmul : Spec (Labels.label ewMulLabel) EWMulPre EWMulPost) (hA : cx.a = a)
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {i : Nat} (hi : i < 32) {st : MachineState} (hpc : st.pc = Host.addrOf (k + 44))
    (hh : Row cx m0 rows 0 i (varsOf cx.sl 0 i) kR0 [] st.data) :
    Eventually (step1 Host.exe) (fun st' ↦
      st'.pc = (if i + 1 < 32 then Host.addrOf (k + 44) else Host.addrOf (k + 82)) ∧
      Row cx m0 rows 0 (i + 1) (varsOf cx.sl 0 (i + 1)) kR0 [] st'.data) st := by
  refine (row_run (t := 0) (i := i) (vars := varsOf cx.sl 0 i) (dst := 1024 * i)
    (ks0 := kR0) (ks1 := k5) (ks2 := k5) (ks := kI0)
    (ws0 := []) (ws1 := w5) (ws2 := w5) (ws := w5)
    (ib := .rbx) (cx0 := .r12) (cx1 := .r13) (lo0 := .rbp) (lo1 := .r15)
    (dr := .r14) (s0 := 8) (so := 8)
    hp hcpy hmul h hA hrsz hrow (by decide) hi (varsOf_ok cx (by decide))
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    b5_in_code b6_in_code b7_in_code b8_in_code b9_in_code
    (by simp [b5]) (by simp [b6]) (by simp [b7]) (by simp [b8]) (by simp [b9])
    (by rw [f5.1]) (by rw [f6.1]) (by rw [f7.1]) (by rw [f8.1])
    (label_of_infix hp b8_in_code rfl) x5 x6 x7 x8 x9
    f5.2 f6.2 f7.2 f8.2 f9.2 (eval_srcA (by omega)) (eval_srcB (by omega))
    (by decide) (by decide) rfl (.head _) (.tail _ (.head _))
    (fun _ hk ↦ (hk.get (r := .r14) (v := P3) (.tail _ (.tail _ (.head _)))).trans eval_P3)
    hpc hh).bind fun st1 ⟨hpc1, hh1⟩ ↦ ?_
  have hpc1' : st1.pc = Host.addrOf (k + 77) := hpc1.trans (by rw [f9.1])
  refine blk_run hp h hA (varsOf_ok cx (by decide)) (by decide) (by decide)
    b10_in_code (by simp [b10]) x10 f10.2 (ret := 0) nofun hpc1'
    hh1.mid hh1.known hh1.words fun st2 hpc2 _ hm2 hk2 hw2 hso2 ↦ ?_
  have htest := row_test (ret := 0) hi (by decide) hh1.words
  have hpc2' : st2.pc = (if i + 1 < 32 then Host.addrOf (k + 44) else Host.addrOf (k + 82)) := by
    simpa only [PcOk, htest, decide_eq_true_eq, f10.1,
      label_of_infix hp b5_in_code rfl] using hpc2
  exact .done _ ⟨hpc2', hm2, next_kR0 hk2, trivial, low64_rows h hh1.rows hso2⟩

theorem row1 (hp : Placed code k) (h : PreOk a s c m0)
    (hcpy : Spec (Labels.label "memcpy") MemcpyPre MemcpyPost)
    (hmul : Spec (Labels.label ewMulLabel) EWMulPre EWMulPost) (hA : cx.a = a)
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {i : Nat} (hi : i < 16) {st : MachineState} (hpc : st.pc = Host.addrOf (k + 88))
    (hh : Row cx m0 rows 1 i (varsOf cx.sl 1 i) kR1 [] st.data) :
    Eventually (step1 Host.exe) (fun st' ↦
      st'.pc = (if i + 1 < 16 then Host.addrOf (k + 88) else Host.addrOf (k + 126)) ∧
      Row cx m0 rows 1 (i + 1) (varsOf cx.sl 1 (i + 1)) kR1 [] st'.data) st := by
  refine (row_run (t := 1) (i := i) (vars := varsOf cx.sl 1 i) (dst := 1024 * i)
    (ks0 := kR1) (ks1 := k12) (ks2 := k12) (ks := kI1)
    (ws0 := []) (ws1 := w5) (ws2 := w5) (ws := w5)
    (ib := .rbp) (cx0 := .r12) (cx1 := .r13) (lo0 := .r14) (lo1 := .r15)
    (dr := .rbx) (s0 := 8) (so := 8)
    hp hcpy hmul h hA hrsz hrow (by decide) hi (varsOf_ok cx (by decide))
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    b12_in_code b13_in_code b14_in_code b15_in_code b16_in_code
    (by simp [b12]) (by simp [b13]) (by simp [b14]) (by simp [b15]) (by simp [b16])
    (by rw [f12.1]) (by rw [f13.1]) (by rw [f14.1]) (by rw [f15.1])
    (label_of_infix hp b15_in_code rfl) x12 x13 x14 x15 x16
    f12.2 f13.2 f14.2 f15.2 f16.2 (eval_srcA (by omega)) (eval_srcB (by omega))
    (by decide) (by decide) rfl (.head _) (.tail _ (.head _))
    (fun _ hk ↦ (hk.get (r := .rbx) (v := P3) (.tail _ (.tail _ (.head _)))).trans eval_P3)
    hpc hh).bind fun st1 ⟨hpc1, hh1⟩ ↦ ?_
  have hpc1' : st1.pc = Host.addrOf (k + 121) := hpc1.trans (by rw [f16.1])
  refine blk_run hp h hA (varsOf_ok cx (by decide)) (by decide) (by decide)
    b17_in_code (by simp [b17]) x17 f17.2 (ret := 0) nofun hpc1'
    hh1.mid hh1.known hh1.words fun st2 hpc2 _ hm2 hk2 hw2 hso2 ↦ ?_
  have htest := row_test (ret := 0) hi (by decide) hh1.words
  have hpc2' : st2.pc = (if i + 1 < 16 then Host.addrOf (k + 88) else Host.addrOf (k + 126)) := by
    simpa only [PcOk, htest, decide_eq_true_eq, f17.1,
      label_of_infix hp b12_in_code rfl] using hpc2
  exact .done _ ⟨hpc2', hm2, next_kR1 hk2, trivial, low64_rows h hh1.rows hso2⟩

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
