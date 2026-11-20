module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.FoldR2Rows

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.KeccakOpen
open NativeRustcVm.Transcript (off DecArea)

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}
  {cx : Cx} {rows : Array (Array EW)}

theorem row2_1 (hp : Placed code k) (h : PreOk a s c m0)
    (hcpy : Spec (Labels.label "memcpy") MemcpyPre MemcpyPost)
    (hmul : Spec (Labels.label ewMulLabel) EWMulPre EWMulPost) (hA : cx.a = a)
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + 159))
    (hh : Row cx m0 rows 2 1 (varsOf cx.sl 2 0) k18 w19 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + 189) ∧
      Row cx m0 rows 2 2 (varsOf cx.sl 2 0) k18 w24 st'.data) st := by
  refine (row_run (t := 2) (i := 1) (vars := varsOf cx.sl 2 0) (dst := 0)
    (ks0 := k18) (ks1 := k18) (ks2 := k18) (ks := k18)
    (ws0 := w19) (ws1 := w23) (ws2 := w24) (ws := w24)
    (ib := .rbx) (cx0 := .rbp) (cx1 := .r12) (lo0 := .r14) (lo1 := .r15)
    (dr := .r13) (s0 := 1032) (so := 8)
    hp hcpy hmul h hA hrsz hrow (by decide) (by decide) (varsOf_ok cx (by decide))
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    b23_in_code b24_in_code b25_in_code b26_in_code b27_in_code
    (by simp [b23]) (by simp [b24]) (by simp [b25]) (by simp [b26]) (by simp [b27])
    (by rw [f23.1]) (by rw [f24.1]) (by rw [f25.1]) (by rw [f26.1])
    (label_of_infix hp b26_in_code rfl) x23 x24 x25 x26 x27
    f23.2 f24.2 f25.2 f26.2 f27.2 rfl rfl (by decide) (by decide) (by decide)
    (.head _) (.tail _ (.head _))
    (fun _ hk ↦ hk.get (r := .r13) (v := P) (.tail _ (.tail _ (.head _)))) hpc hh).mono
    fun st' ⟨hp', hh'⟩ ↦ ⟨hp'.trans (by rw [f27.1]), hh'⟩

theorem row2_2 (hp : Placed code k) (h : PreOk a s c m0)
    (hcpy : Spec (Labels.label "memcpy") MemcpyPre MemcpyPost)
    (hmul : Spec (Labels.label ewMulLabel) EWMulPre EWMulPost) (hA : cx.a = a)
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + 189))
    (hh : Row cx m0 rows 2 2 (varsOf cx.sl 2 0) k18 w24 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + 219) ∧
      Row cx m0 rows 2 3 (varsOf cx.sl 2 0) k18 w29 st'.data) st := by
  refine (row_run (t := 2) (i := 2) (vars := varsOf cx.sl 2 0) (dst := 0)
    (ks0 := k18) (ks1 := k18) (ks2 := k18) (ks := k18)
    (ws0 := w24) (ws1 := w28) (ws2 := w29) (ws := w29)
    (ib := .rbx) (cx0 := .rbp) (cx1 := .r12) (lo0 := .r14) (lo1 := .r15)
    (dr := .r13) (s0 := 2048) (so := 0)
    hp hcpy hmul h hA hrsz hrow (by decide) (by decide) (varsOf_ok cx (by decide))
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    b28_in_code b29_in_code b30_in_code b31_in_code b32_in_code
    (by simp [b28]) (by simp [b29]) (by simp [b30]) (by simp [b31]) (by simp [b32])
    (by rw [f28.1]) (by rw [f29.1]) (by rw [f30.1]) (by rw [f31.1])
    (label_of_infix hp b31_in_code rfl) x28 x29 x30 x31 x32
    f28.2 f29.2 f30.2 f31.2 f32.2 rfl rfl (by decide) (by decide) (by decide)
    (.head _) (.tail _ (.head _))
    (fun _ hk ↦ hk.get (r := .r13) (v := P) (.tail _ (.tail _ (.head _)))) hpc hh).mono
    fun st' ⟨hp', hh'⟩ ↦ ⟨hp'.trans (by rw [f32.1]), hh'⟩

theorem row2_3 (hp : Placed code k) (h : PreOk a s c m0)
    (hcpy : Spec (Labels.label "memcpy") MemcpyPre MemcpyPost)
    (hmul : Spec (Labels.label ewMulLabel) EWMulPre EWMulPost) (hA : cx.a = a)
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + 219))
    (hh : Row cx m0 rows 2 3 (varsOf cx.sl 2 0) k18 w29 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + 248) ∧
      Row cx m0 rows 2 4 (varsOf cx.sl 2 0) k18 W6 st'.data) st := by
  refine (row_run (t := 2) (i := 3) (vars := varsOf cx.sl 2 0) (dst := 0)
    (ks0 := k18) (ks1 := k18) (ks2 := k18) (ks := k18)
    (ws0 := w29) (ws1 := W6) (ws2 := W6) (ws := W6)
    (ib := .rbx) (cx0 := .rbp) (cx1 := .r12) (lo0 := .r14) (lo1 := .r15)
    (dr := .r13) (s0 := 3072) (so := 0)
    hp hcpy hmul h hA hrsz hrow (by decide) (by decide) (varsOf_ok cx (by decide))
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    b33_in_code b34_in_code b35_in_code b36_in_code b37_in_code
    (by simp [b33]) (by simp [b34]) (by simp [b35]) (by simp [b36]) (by simp [b37])
    (by rw [f33.1]) (by rw [f34.1]) (by rw [f35.1]) (by rw [f36.1])
    (label_of_infix hp b36_in_code rfl) x33 x34 x35 x36 x37
    f33.2 f34.2 f35.2 f36.2 f37.2 rfl rfl (by decide) (by decide) (by decide)
    (.head _) (.tail _ (.head _))
    (fun _ hk ↦ hk.get (r := .r13) (v := P) (.tail _ (.tail _ (.head _)))) hpc hh).mono
    fun st' ⟨hp', hh'⟩ ↦ ⟨hp'.trans (by rw [f37.1]), hh'⟩

theorem row2_4 (hp : Placed code k) (h : PreOk a s c m0)
    (hcpy : Spec (Labels.label "memcpy") MemcpyPre MemcpyPost)
    (hmul : Spec (Labels.label ewMulLabel) EWMulPre EWMulPost) (hA : cx.a = a)
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + 248))
    (hh : Row cx m0 rows 2 4 (varsOf cx.sl 2 0) k18 W6 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + 276) ∧
      Row cx m0 rows 2 5 (varsOf cx.sl 2 0) k18 W6 st'.data) st := by
  refine (row_run (t := 2) (i := 4) (vars := varsOf cx.sl 2 0) (dst := 0)
    (ks0 := k18) (ks1 := k18) (ks2 := k18) (ks := k18)
    (ws0 := W6) (ws1 := W6) (ws2 := W6) (ws := W6)
    (ib := .rbx) (cx0 := .rbp) (cx1 := .r12) (lo0 := .r14) (lo1 := .r15)
    (dr := .r13) (s0 := 4096) (so := 0)
    hp hcpy hmul h hA hrsz hrow (by decide) (by decide) (varsOf_ok cx (by decide))
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    b38_in_code b39_in_code b40_in_code b41_in_code b42_in_code
    (by simp [b38]) (by simp [b39]) (by simp [b40]) (by simp [b41]) (by simp [b42])
    (by rw [f38.1]) (by rw [f39.1]) (by rw [f40.1]) (by rw [f41.1])
    (label_of_infix hp b41_in_code rfl) x38 x39 x40 x41 x42
    f38.2 f39.2 f40.2 f41.2 f42.2 rfl rfl (by decide) (by decide) (by decide)
    (.head _) (.tail _ (.head _))
    (fun _ hk ↦ hk.get (r := .r13) (v := P) (.tail _ (.tail _ (.head _)))) hpc hh).mono
    fun st' ⟨hp', hh'⟩ ↦ ⟨hp'.trans (by rw [f42.1]), hh'⟩

theorem row2_5 (hp : Placed code k) (h : PreOk a s c m0)
    (hcpy : Spec (Labels.label "memcpy") MemcpyPre MemcpyPost)
    (hmul : Spec (Labels.label ewMulLabel) EWMulPre EWMulPost) (hA : cx.a = a)
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + 276))
    (hh : Row cx m0 rows 2 5 (varsOf cx.sl 2 0) k18 W6 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + 304) ∧
      Row cx m0 rows 2 6 (varsOf cx.sl 2 0) k18 W6 st'.data) st := by
  refine (row_run (t := 2) (i := 5) (vars := varsOf cx.sl 2 0) (dst := 0)
    (ks0 := k18) (ks1 := k18) (ks2 := k18) (ks := k18)
    (ws0 := W6) (ws1 := W6) (ws2 := W6) (ws := W6)
    (ib := .rbx) (cx0 := .rbp) (cx1 := .r12) (lo0 := .r14) (lo1 := .r15)
    (dr := .r13) (s0 := 5128) (so := 8)
    hp hcpy hmul h hA hrsz hrow (by decide) (by decide) (varsOf_ok cx (by decide))
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    b43_in_code b44_in_code b45_in_code b46_in_code b47_in_code
    (by simp [b43]) (by simp [b44]) (by simp [b45]) (by simp [b46]) (by simp [b47])
    (by rw [f43.1]) (by rw [f44.1]) (by rw [f45.1]) (by rw [f46.1])
    (label_of_infix hp b46_in_code rfl) x43 x44 x45 x46 x47
    f43.2 f44.2 f45.2 f46.2 f47.2 rfl rfl (by decide) (by decide) (by decide)
    (.head _) (.tail _ (.head _))
    (fun _ hk ↦ hk.get (r := .r13) (v := P) (.tail _ (.tail _ (.head _)))) hpc hh).mono
    fun st' ⟨hp', hh'⟩ ↦ ⟨hp'.trans (by rw [f47.1]), hh'⟩

theorem row2_6 (hp : Placed code k) (h : PreOk a s c m0)
    (hcpy : Spec (Labels.label "memcpy") MemcpyPre MemcpyPost)
    (hmul : Spec (Labels.label ewMulLabel) EWMulPre EWMulPost) (hA : cx.a = a)
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + 304))
    (hh : Row cx m0 rows 2 6 (varsOf cx.sl 2 0) k18 W6 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + 332) ∧
      Row cx m0 rows 2 7 (varsOf cx.sl 2 0) k18 W6 st'.data) st := by
  refine (row_run (t := 2) (i := 6) (vars := varsOf cx.sl 2 0) (dst := 0)
    (ks0 := k18) (ks1 := k18) (ks2 := k18) (ks := k18)
    (ws0 := W6) (ws1 := W6) (ws2 := W6) (ws := W6)
    (ib := .rbx) (cx0 := .rbp) (cx1 := .r12) (lo0 := .r14) (lo1 := .r15)
    (dr := .r13) (s0 := 6152) (so := 8)
    hp hcpy hmul h hA hrsz hrow (by decide) (by decide) (varsOf_ok cx (by decide))
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    b48_in_code b49_in_code b50_in_code b51_in_code b52_in_code
    (by simp [b48]) (by simp [b49]) (by simp [b50]) (by simp [b51]) (by simp [b52])
    (by rw [f48.1]) (by rw [f49.1]) (by rw [f50.1]) (by rw [f51.1])
    (label_of_infix hp b51_in_code rfl) x48 x49 x50 x51 x52
    f48.2 f49.2 f50.2 f51.2 f52.2 rfl rfl (by decide) (by decide) (by decide)
    (.head _) (.tail _ (.head _))
    (fun _ hk ↦ hk.get (r := .r13) (v := P) (.tail _ (.tail _ (.head _)))) hpc hh).mono
    fun st' ⟨hp', hh'⟩ ↦ ⟨hp'.trans (by rw [f52.1]), hh'⟩

theorem row2_7 (hp : Placed code k) (h : PreOk a s c m0)
    (hcpy : Spec (Labels.label "memcpy") MemcpyPre MemcpyPost)
    (hmul : Spec (Labels.label ewMulLabel) EWMulPre EWMulPost) (hA : cx.a = a)
    (hrsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + 332))
    (hh : Row cx m0 rows 2 7 (varsOf cx.sl 2 0) k18 W6 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + 360) ∧
      Row cx m0 rows 2 8 (varsOf cx.sl 2 0) k18 W6 st'.data) st := by
  refine (row_run (t := 2) (i := 7) (vars := varsOf cx.sl 2 0) (dst := 0)
    (ks0 := k18) (ks1 := k18) (ks2 := k18) (ks := k18)
    (ws0 := W6) (ws1 := W6) (ws2 := W6) (ws := W6)
    (ib := .rbx) (cx0 := .rbp) (cx1 := .r12) (lo0 := .r14) (lo1 := .r15)
    (dr := .r13) (s0 := 7168) (so := 0)
    hp hcpy hmul h hA hrsz hrow (by decide) (by decide) (varsOf_ok cx (by decide))
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    b53_in_code b54_in_code b55_in_code b56_in_code b57_in_code
    (by simp [b53]) (by simp [b54]) (by simp [b55]) (by simp [b56]) (by simp [b57])
    (by rw [f53.1]) (by rw [f54.1]) (by rw [f55.1]) (by rw [f56.1])
    (label_of_infix hp b56_in_code rfl) x53 x54 x55 x56 x57
    f53.2 f54.2 f55.2 f56.2 f57.2 rfl rfl (by decide) (by decide) (by decide)
    (.head _) (.tail _ (.head _))
    (fun _ hk ↦ hk.get (r := .r13) (v := P) (.tail _ (.tail _ (.head _)))) hpc hh).mono
    fun st' ⟨hp', hh'⟩ ↦ ⟨hp'.trans (by rw [f57.1]), hh'⟩

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
