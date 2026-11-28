/-
  LeanVM.Guest.Program.FiatShamir

  The guest's section "Fiat-Shamir".
-/

module

public import LeanVM.Guest.Program.FieldPacking

/-!
# Fiat-Shamir

A duplex sponge over Keccak-f in overwrite mode (fiat_shamir::FiatShamirState). The sponge is the 13-cell output `sp` of its last permutation, whose last FS_CELLS cells, the capacity, are all the next permutation keeps: between functions and loop frames those cells are all that travels, `fs0 .. fs4`. Scalars absorbed since wait in an eight-cell `rate` run, two cells a scalar, at most four. How many wait is a compile-time count at every call site, `k`. A fifth scalar, or a challenge, permutes; every challenge is a permutation of its own.
-/

namespace LeanVM.Guest.Program

open LeanVM.Parameters LeanVM.Core LeanVM.Dsl

set_option linter.unusedVariables false

@[expose] public section

/-- Scalar x as lanes (c0, c1, 0, tag) over rate cells 2k and 2k + 1: x itself, then a constant. -/
def fsPack (rate : List V) (k : Nat) (x : FW) (tag : Nat) : B Unit := B.inline "fs_pack" do
  rate[2 * k] := x
  rate[2 * k + 1] := Y_TOWER * tag

/-- The permutation taking the k waiting scalars: they overwrite the rate, zero past them. -/
def fsPerm (sp : List V) (rate : List V) (k : Nat) : B (List V) := B.inline "fs_perm" do
  let nxt ← B.stackBuf KECCAK_STATE
  if k = 0 then
    B.keccakDuplex (a := .words [.zero, .zero]) (b := .words [.zero, .zero]) (cap := .frame sp) (out := .frame nxt)
  if k = 1 then
    B.keccakDuplex (a := .cells (.frame rate[0:2])) (b := .words [.zero, .zero]) (cap := .frame sp) (out := .frame nxt)
  if k = 2 then
    B.keccakDuplex (a := .cells (.frame rate[0:2])) (b := .cells (.frame rate[2:4])) (cap := .frame sp) (out := .frame nxt)
  if k = 3 then
    rate[6] := 0
    rate[7] := 0
    B.keccakDuplex (a := .cells (.frame rate[0:2])) (b := .cells (.frame rate[2:4])) (tail := some (.cells (.frame rate[4:8]))) (cap := .frame sp) (out := .frame nxt)
  if k = 4 then
    B.keccakDuplex (a := .cells (.frame rate[0:2])) (b := .cells (.frame rate[2:4])) (tail := some (.cells (.frame rate[4:8]))) (cap := .frame sp) (out := .frame nxt)
  return nxt

/-- A grinding nonce as waiting scalar k (k < 4), with its own tag, then the permutation that draws the next challenge, its first cell, and carries the proof of work, the first lane of its second cell (`grind_check`). -/
def fsAbsorbNonce (sp : List V) (rate : List V) (k : Nat) (nonce : Word) : B (List V) := B.inline "fs_absorb_nonce" do
  fsPack rate k (FW.w nonce) DS_POW_NONCE
  let nxt ← fsPerm sp rate (k + 1)
  return nxt

/-- A challenge after a grind of `bits`, k scalars waiting (k <= 4): the nonce under `cursor` joins them, a fifth permuting the four first, and its permutation draws the challenge. A grind of zero bits is no nonce, a plain squeeze. Returns the new sponge, the challenge and the cursor. -/
def fsGrindSqueeze (sp : List V) (rate : List V) (k : Nat) (cursor : Shifted) (tabs : Shifted) (bits : Nat) : B (List V × Word × Shifted) := B.inline "fs_grind_squeeze" do
  let mut nxt : List V := default
  let mut cur : Shifted := default
  if bits = 0 then
    nxt ← fsPerm sp rate k
    cur := cursor
  else if k = 4 then
    let full ← fsPerm sp rate 4
    let nonceRate ← B.stackBuf 8
    nxt ← fsAbsorbNonce full nonceRate 0 (← val cursor[GEN ^ 0])
    call (instName "grind_check" [.L bits]) [nxt[1], tabs]
    cur := ⟨cursor.base, cursor.exp + 1⟩
  else
    nxt ← fsAbsorbNonce sp rate k (← val cursor[GEN ^ 0])
    call (instName "grind_check" [.L bits]) [nxt[1], tabs]
    cur := ⟨cursor.base, cursor.exp + 1⟩
  return (nxt, nxt[0], cur)

/-- The permutation taking a full rate held in the record cells at..at+8. -/
def fsPermPending (cap : List V) (rec' : Word) (at' : Nat) : B (List V) := B.inline "fs_perm_pending" do
  let nxt ← B.stackBuf KECCAK_STATE
  B.keccakDuplex (a := .words [.cell (← val rec'[GEN ^ at']).v, .cell (← val rec'[GEN ^ (at' + 1)]).v]) (b := .words [.cell (← val rec'[GEN ^ (at' + 2)]).v, .cell (← val rec'[GEN ^ (at' + 3)]).v]) (tail := some (.words [.cell (← val rec'[GEN ^ (at' + 4)]).v, .cell (← val rec'[GEN ^ (at' + 5)]).v, .cell (← val rec'[GEN ^ (at' + 6)]).v, .cell (← val rec'[GEN ^ (at' + 7)]).v])) (cap := .frame cap) (out := .frame nxt)
  return nxt

/-- A carried capacity as the run a permutation reads. -/
def fsCap (fs0 : Word) (fs1 : Word) (fs2 : Word) (fs3 : Word) (fs4 : Word) : B (List V) := B.inline "fs_cap" do
  let t0 ← B.stackBuf 5
  t0[0] := fs0
  t0[1] := fs1
  t0[2] := fs2
  t0[3] := fs3
  t0[4] := fs4
  let sp := t0
  return sp

/-- A record's carried capacity, its cells `stride` fields apart from `field` on. -/
def fsLoad (rec' : Word) (field : Nat) (stride : Nat) : B (List V) := B.inline "fs_load" do
  let t0 ← B.stackBuf 5
  t0[0] := rec'[GEN ^ (field * stride)]
  t0[1] := rec'[GEN ^ ((field + 1) * stride)]
  t0[2] := rec'[GEN ^ ((field + 2) * stride)]
  t0[3] := rec'[GEN ^ ((field + 3) * stride)]
  t0[4] := rec'[GEN ^ ((field + 4) * stride)]
  let sp := t0
  return sp

/-- Store the capacity of permutation output `sp` as fs_load reads it. -/
def fsStore (rec' : Shifted) (field : Nat) (stride : Nat) (sp : List V) : B Unit := B.inline "fs_store" do
  for j in [0:FS_CELLS] do
    rec'[GEN ^ ((field + j) * stride)] := sp[KECCAK_STATE - FS_CELLS + j]

/-- Fetch and absorb in one act: the word under `cursor` becomes waiting scalar k (k < 4), and the cursor steps one word on. Reading and absorbing are inseparable, so no proof-stream word can enter the computation unbound: the soundness invariant the whole guest rests on. -/
def fsNext (rate : List V) (k : Nat) (cursor : Shifted) : B (Word × Shifted) := B.inline "fs_next" do
  let x ← val cursor[GEN ^ 0]
  fsPack rate k (FW.w x) DS_OBSERVE
  return (x, ⟨cursor.base, cursor.exp + 1⟩)

/-- A challenge: the permutation taking the k waiting scalars, read off its first two lanes. Returns the new sponge and the challenge. -/
def squeeze (sp : List V) (rate : List V) (k : Nat) : B (List V × Word) := B.inline "squeeze" do
  let nxt ← fsPerm sp rate k
  let challenge ← challengeFromState nxt
  return (nxt, challenge)

end
end LeanVM.Guest.Program
