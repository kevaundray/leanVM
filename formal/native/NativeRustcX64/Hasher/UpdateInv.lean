module

public import NativeRustcX64.Hasher.Bytes
public import NativeRustcX64.Hasher.UpdateExec
public import NativeRustcX64.KeccakF.Inv

/-!
# `Hasher::update`'s loop: its states (x86-64)

From the entry state `m0` (hasher at `hAt m0`, input `input m0` of `nOf m0` bytes, RSP `spAt m0`,
the frame at `frm m0`): what every state after the prologue keeps (`Frame`: the hasher and buffer
pointers, RSP, the pushed registers in the frame, memory as `m0`'s but in the hasher and the stack
below RSP (`Chg`), every mapped byte); the loop head `.LUpdate_1` having absorbed the input's first
`c` bytes (`Inv`); `.LUpdate_5` after a turn that took `t` more (`Mid`). `UpdatePre`'s addresses as
numbers (`Geo`, `geo_of`); the input and the round constants as at the entry (`input_same`,
`rc_same`). The blocks' places and labels (`hb<k>`, `lbl_*`).
-/

namespace NativeRustcX64.Hasher.Update

open NativeRustc NativeRustc.Keccak NativeRustcX64.Sym NativeRustcX64.Common.Update
open NativeRustcX64.KeccakF NativeRustcX64.Hasher

@[expose] public section

/-- The hasher's address at the entry. -/
def hAt (m : MachineData) : BitVec 64 := reg m .rdi
/-- The input's address at the entry. -/
def dAt (m : MachineData) : BitVec 64 := reg m .rsi
/-- The input's length at the entry. -/
def nOf (m : MachineData) : Nat := (reg m .rdx).toNat
/-- RSP at the entry. -/
def spAt (m : MachineData) : BitVec 64 := rspOf m
/-- The frame: 112 bytes below the entry's RSP. -/
def frm (m : MachineData) : BitVec 64 := spAt m - 112#64

/-- The input. -/
def input (m0 : MachineData) : List UInt8 := bytesOf m0.dmem (dAt m0) (nOf m0)

/-- The hasher's bytes in `m`. -/
def hasher (m0 m : MachineData) : List UInt8 := bytesOf m.dmem (hAt m0) 344

/-- What `update` changes: the hasher and the stack below RSP. -/
def Chg (m0 : MachineData) (p : BitVec 64) : Prop :=
  InRange (hAt m0) 344 p ∨ InRange (stackBelow m0 updateStack) updateStack p

/-- What the loop changes: the hasher and the stack below the pushed registers. -/
def ChgL (m0 : MachineData) (p : BitVec 64) : Prop :=
  InRange (hAt m0) 344 p ∨ InRange (stackBelow m0 updateStack) 304 p

/-- The bytes `H` have absorbed the input's first `c` bytes after whatever the entry's had. -/
def Holds (m0 : MachineData) (H : List UInt8) (c : Nat) : Prop :=
  ∀ a, HasherHolds (hasher m0 m0) a → HasherHolds H (a ++ (input m0).take c)

/-- The frame's slots of the pushed registers. -/
def pushSlots : List (Nat × Reg64) :=
  [(64, .rbx), (72, .r12), (80, .r13), (88, .r14), (96, .r15), (104, .rbp)]

/-- What every state after the prologue keeps. -/
structure Frame (m0 m : MachineData) : Prop where
  r14 : reg m .r14 = hAt m0
  r13 : reg m .r13 = hAt m0 + 200#64
  rsp : rspOf m = frm m0 + 8#64
  saved : AllOf (fun p : Nat × Reg64 =>
    WordAt m.dmem (frm m0 + BitVec.ofNat 64 p.1) (reg m0 p.2)) pushSlots
  same : SameOutside m0.dmem m.dmem (Chg m0)
  kept : Kept m0.dmem m.dmem

/-- **The loop head** `.LUpdate_1`, the input's first `c` bytes absorbed. -/
structure Inv (m0 : MachineData) (c : Nat) (m : MachineData) : Prop where
  frame : Frame m0 m
  le : c ≤ nOf m0
  rbx : reg m .rbx = BitVec.ofNat 64 (nOf m0 - c)
  r15 : reg m .r15 = dAt m0 + BitVec.ofNat 64 c
  rdi : (reg m .rdi).toNat = bufLen (hasher m0 m)
  holds : Holds m0 (hasher m0 m) c

/-- **`.LUpdate_5`**, after a turn from `c` absorbed bytes that took `t` more. -/
structure Mid (m0 : MachineData) (c t : Nat) (m : MachineData) : Prop where
  frame : Frame m0 m
  le : c + t ≤ nOf m0
  pos : 0 < t ∨ c = nOf m0
  rbx : reg m .rbx = BitVec.ofNat 64 (nOf m0 - c)
  r15 : reg m .r15 = dAt m0 + BitVec.ofNat 64 c
  r12 : reg m .r12 = BitVec.ofNat 64 t
  rdi : (reg m .rdi).toNat = bufLen (hasher m0 m)
  holds : Holds m0 (hasher m0 m) (c + t)

/-- `UpdatePre`'s addresses as numbers. -/
structure Geo (m0 : MachineData) : Prop where
  h : (hAt m0).toNat + 344 ≤ 2 ^ 64
  d : (dAt m0).toNat + nOf m0 ≤ 2 ^ 64
  s : 352 ≤ (spAt m0).toNat
  s8 : (spAt m0).toNat + 8 ≤ 2 ^ 64
  hd : (hAt m0).toNat + 344 ≤ (dAt m0).toNat ∨ (dAt m0).toNat + nOf m0 ≤ (hAt m0).toNat
  hs : (hAt m0).toNat + 344 ≤ (spAt m0).toNat - 352 ∨ (spAt m0).toNat + 8 ≤ (hAt m0).toNat
  ds : (dAt m0).toNat + nOf m0 ≤ (spAt m0).toNat - 352 ∨ (spAt m0).toNat + 8 ≤ (dAt m0).toNat

/-- The round constants' place, as numbers. -/
structure GeoRc [Labels] (m0 : MachineData) : Prop where
  nw : rcAddr.toNat + 192 ≤ 2 ^ 64
  rs : rcAddr.toNat + 192 ≤ (spAt m0).toNat - 352 ∨ (spAt m0).toNat + 8 ≤ rcAddr.toNat
  hr : (hAt m0).toNat + 344 ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ (hAt m0).toNat

end

public section

theorem toNat_sub_ofNat {a : BitVec 64} {j : Nat} (h : j ≤ a.toNat) :
    (a - BitVec.ofNat 64 j).toNat = a.toNat - j := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := a.isLt
  omega

theorem stackBelow_toNat {m : MachineData} {n : Nat} (h : n ≤ (rspOf m).toNat) :
    (stackBelow m n).toNat = (rspOf m).toNat - n :=
  toNat_sub_ofNat h

theorem geo_of {m0 : MachineData} [Labels] (hpre : UpdatePre m0) : Geo m0 := by
  obtain ⟨⟨hs, hs8, -⟩, -, -, -, hh, -, hd, hhd, hhs, hds, -⟩ := hpre
  have hu : updateStack = 352 := rfl
  have hb : (stackBelow m0 updateStack).toNat = (rspOf m0).toNat - 352 := stackBelow_toNat hs
  unfold Apart at hhs hds
  rw [hb, hu] at hhs hds
  refine ⟨hh, hd, hs, hs8, hhd, ?_, ?_⟩
  · exact hhs.imp id fun h => by unfold hAt spAt; omega
  · exact hds.imp id fun h => by unfold dAt spAt; omega

theorem geoRc_of {m0 : MachineData} [Labels] (hpre : UpdatePre m0) : GeoRc m0 := by
  obtain ⟨⟨hs, -, -⟩, ⟨-, hnw, hrs⟩, -, -, -, -, -, -, -, -, hhr⟩ := hpre
  have hu : updateStack = 352 := rfl
  have hb : (stackBelow m0 updateStack).toNat = (rspOf m0).toNat - 352 := stackBelow_toNat hs
  unfold Apart at hrs
  rw [hb, hu] at hrs
  exact ⟨hnw, hrs.imp id fun h => by unfold spAt; omega, hhr⟩

theorem frm_toNat {m0 : MachineData} (g : Geo m0) : (frm m0).toNat = (spAt m0).toNat - 112 :=
  toNat_sub_ofNat (by have := g.s; omega)

/-- What `update` changes, as numbers. -/
theorem chg_iff {m0 : MachineData} (g : Geo m0) (p : BitVec 64) :
    Chg m0 p ↔ ((hAt m0).toNat ≤ p.toNat ∧ p.toNat < (hAt m0).toNat + 344) ∨
      ((spAt m0).toNat - 352 ≤ p.toNat ∧ p.toNat < (spAt m0).toNat) := by
  have hb : (stackBelow m0 updateStack).toNat = (spAt m0).toNat - 352 :=
    stackBelow_toNat g.s
  have hu : updateStack = 352 := rfl
  unfold Chg
  rw [hu] at hb ⊢
  rw [inRange_iff g.h, inRange_iff (by rw [hb]; have := g.s8; have := g.s; omega), hb]
  have := g.s
  omega

/-- The stack's bytes from the frame. -/
theorem stack_frm {m0 : MachineData} (g : Geo m0) {i : Nat} (hi : i < 120) :
    rspOf m0 - BitVec.ofNat 64 updateStack + BitVec.ofNat 64 (240 + i) =
      frm m0 + BitVec.ofNat 64 i := by
  have hs := g.s
  have hs8 := g.s8
  have hsb : (rspOf m0 - BitVec.ofNat 64 updateStack).toNat = (spAt m0).toNat - 352 :=
    stackBelow_toNat hs
  have e1 : (rspOf m0 - BitVec.ofNat 64 updateStack + BitVec.ofNat 64 (240 + i)).toNat =
      (spAt m0).toNat - 112 + i := by
    rw [toNat_add_ofNat' (by rw [hsb]; omega), hsb]
    omega
  have e2 : (frm m0 + BitVec.ofNat 64 i).toNat = (spAt m0).toNat - 112 + i := by
    rw [toNat_add_ofNat' (by rw [frm_toNat g]; omega), frm_toNat g]
  exact BitVec.eq_of_toNat_eq (e1.trans e2.symm)

/-- The frame's mapped bytes: the stack's at the entry. -/
theorem frm_mapped {m0 : MachineData} [Labels] (hpre : UpdatePre m0) :
    Mapped m0.dmem (frm m0) 120 := fun i hi => by
  have := hpre.1.2.2 (240 + i) (by show 240 + i < 352 + 8; omega)
  rwa [stack_frm (geo_of hpre) hi] at this

/-- What the loop changes, as numbers. -/
theorem chgL_iff {m0 : MachineData} (g : Geo m0) (p : BitVec 64) :
    ChgL m0 p ↔ ((hAt m0).toNat ≤ p.toNat ∧ p.toNat < (hAt m0).toNat + 344) ∨
      ((spAt m0).toNat - 352 ≤ p.toNat ∧ p.toNat < (spAt m0).toNat - 48) := by
  have hb : (stackBelow m0 updateStack).toNat = (spAt m0).toNat - 352 :=
    stackBelow_toNat g.s
  unfold ChgL
  rw [inRange_iff g.h, inRange_iff (by rw [hb]; have := g.s8; have := g.s; omega), hb]
  have := g.s
  omega

theorem chg_of_chgL {m0 : MachineData} (g : Geo m0) {p : BitVec 64} (h : ChgL m0 p) : Chg m0 p := by
  rw [chgL_iff g] at h
  rw [chg_iff g]
  omega

theorem hasher_congr {m0 m m' : MachineData} (h : ∀ p, m'.dmem.get? p = m.dmem.get? p) :
    hasher m0 m' = hasher m0 m :=
  bytesOf_congr fun _ _ => h _

/-- A pushed register's slot is outside what the loop changes. -/
theorem push_not_chgL {m0 : MachineData} (g : Geo m0) {o i : Nat} (ho : 64 ≤ o) (hoi : o + i < 112) :
    ¬ChgL m0 (frm m0 + BitVec.ofNat 64 o + BitVec.ofNat 64 i) := by
  rw [chgL_iff g, add_ofNat_add, toNat_add_ofNat' (by rw [frm_toNat g]; have := g.s8; omega),
    frm_toNat g]
  have := g.hs
  have := g.s
  omega

/-- `Frame` after a step that keeps R13, R14 and RSP, changes memory only where the loop does and
unmaps nothing. -/
theorem Frame.update {m0 m m' : MachineData} (g : Geo m0) (hf : Frame m0 m)
    (h13 : reg m' .r13 = reg m .r13) (h14 : reg m' .r14 = reg m .r14) (hsp : rspOf m' = rspOf m)
    (hd : ∀ p, ¬ChgL m0 p → m'.dmem.get? p = m.dmem.get? p) (hk : Kept m.dmem m'.dmem) :
    Frame m0 m' where
  r14 := h14.trans hf.r14
  r13 := h13.trans hf.r13
  rsp := hsp.trans hf.rsp
  saved := by
    have hs := hf.saved
    simp only [AllOf, pushSlots] at hs ⊢
    obtain ⟨s0, s1, s2, s3, s4, s5, -⟩ := hs
    have key : ∀ {o : Nat} {w : BitVec 64}, 64 ≤ o → o + 8 ≤ 112 →
        WordAt m.dmem (frm m0 + BitVec.ofNat 64 o) w →
        WordAt m'.dmem (frm m0 + BitVec.ofNat 64 o) w := fun ho ho8 hw i hi => by
      simp only [List.length_map, List.length_range] at hi
      rw [hd _ (push_not_chgL g ho (by omega))]
      exact hw i (by simp [hi])
    exact ⟨key (by decide) (by decide) s0, key (by decide) (by decide) s1,
      key (by decide) (by decide) s2, key (by decide) (by decide) s3,
      key (by decide) (by decide) s4, key (by decide) (by decide) s5, trivial⟩
  same p hp := by
    rw [hd p fun h => hp (chg_of_chgL g h)]
    exact hf.same p hp
  kept p hp := hk p (hf.kept p hp)

/-- **The input is as at the entry** in any state of the loop. -/
theorem input_same {m0 m : MachineData} (g : Geo m0) (hfr : Frame m0 m) {i : Nat}
    (hi : i < nOf m0) :
    m.dmem.get? (dAt m0 + BitVec.ofNat 64 i) = m0.dmem.get? (dAt m0 + BitVec.ofNat 64 i) := by
  have ht := toNat_add_ofNat' (a := dAt m0) (i := i) (by have := g.d; omega)
  rw [hfr.same _ (by rw [chg_iff g, ht]; have := g.hd; have := g.ds; omega)]

/-- **The round constants are as at the entry** in any state of the loop. -/
theorem rc_same {m0 m : MachineData} [Labels] (g : Geo m0) (gr : GeoRc m0) (hfr : Frame m0 m)
    {i : Nat} (hi : i < 192) :
    m.dmem.get? (rcAddr + BitVec.ofNat 64 i) = m0.dmem.get? (rcAddr + BitVec.ofNat 64 i) := by
  have ht := toNat_add_ofNat' (a := rcAddr) (i := i) (by have := gr.nw; omega)
  rw [hfr.same _ (by rw [chg_iff g, ht]; have := gr.hr; have := gr.rs; omega)]

/-- The environment of a loop state: the hasher, region 0, and the frame, region 1. -/
theorem wf_head {m0 m : MachineData} [Labels] (hpre : UpdatePre m0) (hfr : Frame m0 m)
    {vs : Nat → BitVec 64} {ret : BitVec 64} :
    (Env.ofMachine m [(hAt m0, 344), (frm m0, 120)] vs ret).WF := by
  have g := geo_of hpre
  refine Env.wf_of ⟨⟨fun i hi => hfr.kept _ (hpre.2.2.2.1 i hi), g.h⟩,
    ⟨fun i hi => hfr.kept _ (frm_mapped hpre i hi), ?_⟩, trivial⟩ (List.pairwise_pair.mpr ?_)
  · show (frm m0).toNat + 120 ≤ _
    rw [frm_toNat g]
    have := g.s8
    have := g.s
    omega
  · show (hAt m0).toNat + 344 ≤ (frm m0).toNat ∨ (frm m0).toNat + 120 ≤ (hAt m0).toNat
    rw [frm_toNat g]
    have := g.hs
    have := g.s
    omega

/-- `headS` describes a loop state. -/
theorem match_headS {m0 m : MachineData} [Labels] (hfr : Frame m0 m) {vs : Nat → BitVec 64}
    {ret : BitVec 64} : Match (Env.ofMachine m [(hAt m0, 344), (frm m0, 120)] vs ret) headS m :=
  match_ofMachine ⟨rfl, rfl, trivial⟩
    ⟨hfr.r14.trans (BitVec.add_zero _).symm, hfr.r13.trans rfl, hfr.rsp.trans rfl, trivial⟩
    trivial trivial trivial

/-! ## Places -/

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + 0) :=
  b0_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + 16) :=
  b2_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + 21) :=
  b3_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb4 (hp : Placed code k) : b4.IsInfixAt Host.prog (k + 29) :=
  b4_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + 31) :=
  b5_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb6 (hp : Placed code k) : b6.IsInfixAt Host.prog (k + 35) :=
  b6_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb7 (hp : Placed code k) : b7.IsInfixAt Host.prog (k + 40) :=
  b7_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb8 (hp : Placed code k) : b8.IsInfixAt Host.prog (k + 92) :=
  b8_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb9 (hp : Placed code k) : b9.IsInfixAt Host.prog (k + 95) :=
  b9_in_code.trans hp.1 (List.cons_ne_nil _ _)

theorem lbl_entry (hp : Placed code k) :
    Labels.label "_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update" = Host.addrOf (k + 0) :=
  hp.label (j := 0) rfl
theorem lbl_5 (hp : Placed code k) : Labels.label ".LUpdate_5" = Host.addrOf (k + 16) :=
  hp.label (j := 16) rfl
theorem lbl_1 (hp : Placed code k) : Labels.label ".LUpdate_1" = Host.addrOf (k + 21) :=
  hp.label (j := 21) rfl
theorem lbl_6 (hp : Placed code k) : Labels.label ".LUpdate_6" = Host.addrOf (k + 95) :=
  hp.label (j := 95) rfl

end

end NativeRustcX64.Hasher.Update
