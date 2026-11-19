module

public import NativeX64.Instr
public import Kraken.X64.OmniSemantics
import all Kraken.Mem

/-!
# Facts about Kraken's machine for the instruction bridge

Registers read and written at 64 bits, addresses of QM's memory operands and of the scratch bank,
aligned 64-bit loads and stores through `MemRel`, and the monotonicity of `Effects.All`.
-/

public section

namespace NativeX64

open Native hiding Reg64 Width
open Std

/-! ## Registers -/

theorem get_r64 (regs : Reg64s) (r : Native.Reg64) : regs.get (r64 r) = regs.get64 r.toX64 := by
  simp only [Reg64s.get, Reg.base, Reg.offset, BitVec.take, BitVec.drop, Width.bits]
  simp

theorem get64_set64 (regs : Reg64s) (d r : Native.Reg64) (v : BitVec 64) :
    (regs.set64 d.toX64 v).get64 r.toX64 = if r = d then v else regs.get64 r.toX64 := by
  cases d <;> cases r <;> rfl

theorem StateRel.get {s : QState} {m : MachineData} (h : StateRel s m) (r : Native.Reg64) :
    m.regs.get (r64 r) = (s.reg r).toBitVec := by
  rw [get_r64, h.1]

theorem StateRel.setReg {s : QState} {m : MachineData} (h : StateRel s m) (d : Native.Reg64)
    (hd : d ≠ .rsp) (v : UInt64) : StateRel (s.setReg d v) (m.setReg (r64 d) v.toBitVec) := by
  have hsp : (s.setReg d v).reg .rsp = s.reg .rsp := by simp [Ne.symm hd]
  refine ⟨fun r => ?_, h.2.1, ?_, ?_⟩
  · change (m.regs.set64 d.toX64 v.toBitVec).get64 r.toX64 = _
    rw [get64_set64]
    by_cases hrd : r = d
    · subst hrd; simp [QState.setReg]
    · simp [hrd, QState.setReg, h.1]
  · rw [hsp]; exact h.2.2.1
  · rw [hsp]; exact h.2.2.2

theorem StateRel.setReg' {s : QState} {m : MachineData} (h : StateRel s m) (d : Native.Reg64)
    (hd : d ≠ .rsp) {v : UInt64} {w : BitVec 64} (hw : w = v.toBitVec) :
    StateRel (s.setReg d v) (m.setReg (r64 d) w) := hw ▸ h.setReg d hd v

/-! ## Addresses -/

theorem Addr.interp_eq [Labels] (a : Addr) {s : QState} {m : MachineData} (h : StateRel s m)
    (p : Std.Rco Int64) :
    BitVec.zeroExtend 64 (AddrExpr.interp (address_size := ⟨.W64⟩) a.toAddrExpr m.regs p) =
      (a.eval s).toBitVec := by
  obtain ⟨base, idx, disp⟩ := a
  have hd : BitVec.ofInt 64 disp.toInt = disp.toBitVec := BitVec.ofInt_toInt
  rcases idx with _ | ⟨r, w⟩
  · simp only [AddrExpr.interp, Addr.toAddrExpr, Addr.eval, ConstExpr.interp, BitVec.toAddressSize,
      BitVec.take, BitVec.signed, Width.bits, BitVec.extractLsb'_eq_self, h.1, Option.map_none,
      Int.add_zero, BitVec.setWidth_eq, UInt64.toBitVec_add, Int64.toBitVec_toUInt64]
    rw [BitVec.ofInt_add, BitVec.ofInt_toInt, hd]
    simp
  · simp only [AddrExpr.interp, Addr.toAddrExpr, Addr.eval, ConstExpr.interp, BitVec.toAddressSize,
      BitVec.take, BitVec.signed, Width.bits, BitVec.extractLsb'_eq_self, h.1, Option.map_some,
      BitVec.setWidth_eq, UInt64.toBitVec_add, UInt64.toBitVec_mul, Int64.toBitVec_toUInt64]
    rw [BitVec.ofInt_add, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
      BitVec.ofInt_toInt, hd]
    cases w <;> rfl

/-- The scratch word a register `i < 16` names: word `i` of the red zone. -/
theorem bankIdx_eval (s : QState) (i : Native.Reg64) (hi : s.reg i < 16) :
    (bankIdx i).eval s = s.reg .rsp - 128 + (8 * (s.reg i).toNat).toUInt64 := by
  have hi' : (s.reg i).toNat < 16 := UInt64.lt_iff_toNat_lt.mp hi
  have h128 : ((-128 : Int64).toUInt64).toNat = 2 ^ 64 - 128 := by decide
  have hr := (s.reg .rsp).toNat_lt_size
  apply UInt64.toNat_inj.mp
  simp only [bankIdx, Addr.eval, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_sub,
    h128, toNat_slot hi', show (Native.Width.W64.bytes).toUInt64.toNat = 8 from rfl,
    show (128 : UInt64).toNat = 128 from rfl, UInt64.size] at hr ⊢
  omega

/-- The scratch word `k < 16`: word `k` of the red zone. -/
theorem bankSlot_eval (s : QState) {k : Nat} (hk : k < 16) :
    (bankSlot k).eval s = s.reg .rsp - 128 + (8 * k).toUInt64 := by
  have hr := (s.reg .rsp).toNat_lt_size
  apply UInt64.toNat_inj.mp
  simp only [bankSlot, Addr.eval, Int64.toUInt64_sub, Int64.toUInt64_ofNat', ← Nat.toUInt64_eq,
    UInt64.toNat_add, UInt64.toNat_sub, toNat_slot hk, show (128 : UInt64).toNat = 128 from rfl,
    show ((128 : Int64).toUInt64).toNat = 128 from rfl, UInt64.toNat_zero, UInt64.size] at hr ⊢
  omega

/-! ## Memory -/

theorem loadBytes_congr {d₁ d₂ : DataMem} {a : BitVec 64} {n : Nat}
    (h : ∀ i < n, d₁.get? (a + .ofNat 64 i) = d₂.get? (a + .ofNat 64 i)) :
    d₁.loadBytes a n = d₂.loadBytes a n := by
  unfold Mem.loadBytes
  congr 1
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem loadBytes_At (bs : List UInt8) (a : BitVec 64) (hl : bs.length ≤ 2 ^ 64)
    (d : DataMem) : Mem.loadBytes (d.union (bs.At a)) a bs.length = some bs := by
  unfold Mem.loadBytes
  have hget : ∀ i ∈ List.range bs.length,
      (d.union (bs.At a)).get? (a + .ofNat 64 i) = some bs[i]! := by
    intro i hi
    have hi := List.mem_range.mp hi
    rw [ExtHashMap.get?_eq_getElem?, ExtHashMap.union_eq, ExtHashMap.getElem?_union,
      ← ExtHashMap.get?_eq_getElem?, get?_At_idx _ _ _ (by omega) hl,
      List.getElem?_eq_getElem hi, getElem!_pos bs i hi]
    rfl
  rw [List.map_congr_left hget]
  have : (List.range bs.length).map (fun i => some bs[i]!) = bs.map some := by
    apply List.ext_getElem (by simp)
    intro i h₁ h₂
    simp only [List.length_map, List.length_range] at h₁
    simp [List.getElem?_eq_getElem h₁]
  rw [this, List.mapM_map]
  simpa using List.mapM_pure (m := Option) (f := id) (l := bs)

/-- Two aligned words at different addresses share no byte. -/
theorem aligned_disjoint {a b : UInt64} (ha : a.toNat % 8 = 0) (hb : b.toNat % 8 = 0) (hab : b ≠ a)
    {i j : Nat} (hi : i < 8) (hj : j < 8) :
    b.toBitVec + .ofNat 64 i ≠ a.toBitVec + .ofNat 64 j := by
  intro h
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, UInt64.toNat_toBitVec] at h'
  have hb' := b.toNat_lt_size
  have ha' := a.toNat_lt_size
  have hba : b.toNat ≠ a.toNat := fun e => hab (UInt64.toNat_inj.mp e)
  simp only [UInt64.size] at hb' ha'
  rw [Nat.mod_eq_of_lt (by omega : i < 2 ^ 64), Nat.mod_eq_of_lt (by omega : j < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
  omega

theorem MemRel.store {q : UInt64 → Option UInt64} {d : DataMem} (hm : MemRel q d) {a v : UInt64}
    (h : q a = some v) (x : UInt64) :
    MemRel (Function.update q a (some x)) (Mem.storeInt d a.toBitVec 8 x.toBitVec.toInt) := by
  have ha := (hm a v h).1
  have hlen : (Int.toBytes 8 x.toBitVec.toInt).length = 8 := Int.toBytes_length _ _
  intro b y hb
  by_cases hba : b = a
  · subst hba
    simp only [Function.update_self, Option.some.injEq] at hb
    subst hb
    refine ⟨ha, ?_⟩
    unfold Mem.storeInt Mem.storeBytes
    have := loadBytes_At (Int.toBytes 8 x.toBitVec.toInt) b.toBitVec (by omega) d
    rwa [hlen] at this
  · rw [Function.update_of_ne hba] at hb
    obtain ⟨hb8, hload⟩ := hm b y hb
    refine ⟨hb8, ?_⟩
    rw [← hload]
    apply loadBytes_congr
    intro i hi
    unfold Mem.storeInt Mem.storeBytes
    rw [ExtHashMap.get?_eq_getElem?, ExtHashMap.get?_eq_getElem?, ExtHashMap.union_eq,
      ExtHashMap.getElem?_union_of_not_mem_right]
    rw [mem_At_iff]
    rintro ⟨j, hj, he⟩
    exact aligned_disjoint ha hb8 hba hi (hlen ▸ hj) he

/-- A store to an aligned word that is none of `q`'s keeps `q`'s words. -/
theorem MemRel.store_apart {q : UInt64 → Option UInt64} {d : DataMem} (hm : MemRel q d)
    {a : UInt64} (ha : a.toNat % 8 = 0) (hq : ∀ b v, q b = some v → b ≠ a) (x : UInt64) :
    MemRel q (Mem.storeInt d a.toBitVec 8 x.toBitVec.toInt) := by
  have hlen : (Int.toBytes 8 x.toBitVec.toInt).length = 8 := Int.toBytes_length _ _
  intro b y hb
  obtain ⟨hb8, hload⟩ := hm b y hb
  refine ⟨hb8, ?_⟩
  rw [← hload]
  apply loadBytes_congr
  intro i hi
  unfold Mem.storeInt Mem.storeBytes
  rw [ExtHashMap.get?_eq_getElem?, ExtHashMap.get?_eq_getElem?, ExtHashMap.union_eq,
    ExtHashMap.getElem?_union_of_not_mem_right]
  rw [mem_At_iff]
  rintro ⟨j, hj, he⟩
  exact aligned_disjoint ha hb8 (hq b y hb) hi (hlen ▸ hj) he

theorem loadInt_of_rel {q : UInt64 → Option UInt64} {d : DataMem} (hm : MemRel q d) {a v : UInt64}
    (h : q a = some v) : Mem.loadInt d a.toBitVec 8 = some (Int.ofBytes v.toBytes) := by
  simp [Mem.loadInt, (hm a v h).2]

theorem load_All {q : UInt64 → Option UInt64} {m : MachineData} (hm : MemRel q m.dmem)
    {a v : UInt64} (h : q a = some v) (ret : BitVec 64 → MachineData → Effects)
    (P : MachineState → Prop) :
    (m.load a.toBitVec .W64 ret).All P = (ret v.toBitVec m).All P := by
  unfold MachineData.load
  rw [Effects.All_require_read_access]
  simp only [_root_.Width.bytes, loadInt_of_rel hm h]
  rw [UInt64.toBytes, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]

theorem store_All {q : UInt64 → Option UInt64} {m : MachineData} (hm : MemRel q m.dmem)
    {a v : UInt64} (h : q a = some v) (x : BitVec 64) (ret : MachineData → Effects)
    (P : MachineState → Prop) :
    (m.store (w := .W64) a.toBitVec x ret).All P =
      (ret { m with dmem := Mem.storeInt m.dmem a.toBitVec 8 x.toInt }).All P := by
  unfold MachineData.store
  rw [Effects.All_require_write_access]
  simp only [_root_.Width.bytes, loadInt_of_rel hm h]

theorem StateRel.store {s : QState} {m : MachineData} (hr : StateRel s m) {a v : UInt64}
    (h : s.mem a = some v) (x : UInt64) :
    StateRel (s.setMem a x) { m with dmem := Mem.storeInt m.dmem a.toBitVec 8 x.toBitVec.toInt } := by
  refine ⟨hr.1, hr.2.1.store h x,
    hr.2.2.1.store_apart (hr.2.1 a v h).1 (fun b w hb e ↦ ?_) x, fun b w hb ↦ ?_⟩
  · subst e
    rw [hr.2.2.2 b v h] at hb
    cases hb
  · show bankAt s.scr (s.reg .rsp - 128) b = none
    by_cases hba : b = a
    · subst hba
      exact hr.2.2.2 b v h
    · rw [QState.setMem_mem, ite_eq_right hba] at hb
      exact hr.2.2.2 b w hb

/-- A store to scratch word `k` of the red zone. -/
theorem StateRel.setScr {s : QState} {m : MachineData} (hr : StateRel s m) {k : Nat} (hk : k < 16)
    (x : UInt64) :
    StateRel (s.setScr k x)
      { m with dmem := (Mem.storeInt m.dmem (s.reg .rsp - 128 + (8 * k).toUInt64).toBitVec 8
        x.toBitVec.toInt) } := by
  have hb := bankAt_slot s.scr (s.reg .rsp - 128) hk
  refine ⟨hr.1, hr.2.1.store_apart (hr.2.2.1 _ _ hb).1 (fun b w hw e ↦ ?_) x, ?_,
    fun b w hw ↦ bankAt_none (hr.2.2.2 b w hw)⟩
  · subst e
    rw [hr.2.2.2 _ _ hw] at hb
    cases hb
  · show MemRel (bankAt (Function.update s.scr k x) (s.reg .rsp - 128)) _
    rw [bankAt_update _ _ hk]
    exact hr.2.2.1.store hb x

/-! ## `Effects.All` -/

theorem Effects.All.mono {P Q : MachineState → Prop} (hPQ : ∀ st, P st → Q st) {e : Effects}
    (h : e.All P) : e.All Q := by
  induction e with
  | done => exact hPQ _ h
  | unimplemented | gp_unaligned | nonmem_load | nonmem_store => exact h
  | undefined _ ih => exact fun v => ih v (h v)
  | require_read_access _ _ ih | require_write_access _ _ ih | require_exec_access _ _ ih =>
    exact ih () h

end NativeX64
