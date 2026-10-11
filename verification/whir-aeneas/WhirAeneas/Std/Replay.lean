module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std Result

/- Nonopaque logical-content models of the standard-library operations the
   generic WHIR replay reaches. Vec content only: capacity and allocator state are
   erased, as everywhere else in the Aeneas library. -/

/-- `usize::trailing_zeros`: the number of low zero bits, the width for zero. -/
@[rust_fun "core::num::{usize}::trailing_zeros"]
def core.num.Usize.trailing_zeros (x : Usize) : Result U32 :=
  let n := if x.val = 0 then 64 else
    (List.range 64).find? (fun i => x.val.testBit i) |>.getD 64
  .ok ⟨BitVec.ofNat 32 n⟩

/-- `usize::div_ceil`, which panics on a zero divisor. -/
@[rust_fun "core::num::{usize}::div_ceil"]
def core.num.Usize.div_ceil (a b : Usize) : Result Usize :=
  if b.val = 0 then .fail .panic
  else .ok ⟨BitVec.ofNat _ ((a.val + b.val - 1) / b.val)⟩

/-- `Vec::remove`, which panics past the end. -/
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::remove"]
def alloc.vec.Vec.remove {T : Type} (_A : Type) (v : alloc.vec.Vec T) (i : Usize) :
    Result (T × alloc.vec.Vec T) :=
  if h : i.val < v.val.length then
    .ok (v.val[i.val], .from (v.val.eraseIdx i.val) (by
      have := v.property
      rw [List.length_eraseIdx_of_lt h]
      omega))
  else .fail .panic
