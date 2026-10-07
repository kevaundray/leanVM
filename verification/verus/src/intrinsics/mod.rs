//! Specifications of the `core::arch` intrinsics the SIMD kernels call: the trust base of their proofs.
//!
//! Verus cannot see into an intrinsic, so each one used by a verified kernel gets an `assume_specification`
//! stating its lane-level semantics. A vector register is viewed as the array of words a `transmute` gives
//! (`__m512i` as `[u64; 8]`, `uint8x16_t` as `[u8; 16]`, ...): [`transmuted`] is that value, and the view
//! functions in [`x86`] and [`aarch64`] name it per type. Every specification is written as an open spec
//! function on those arrays (`spec_<intrinsic>`), with an executable twin (`model_<intrinsic>`) that Verus
//! proves equal to it. `tests/intrinsics/` runs each real intrinsic on random and edge inputs and compares its
//! result, read through `transmute`, with the twin: that is what ties each assumption to the hardware.
//!
//! The other assumptions are the layout facts in this file and in the per-architecture modules (`axiom_*`):
//! reinterpreting a register as another array type or integer is the little-endian split of the same bits.
//! The tests check those too.
//!
//! Loads and stores through raw pointers are not specified: Verus has no way to tie a pointer an intrinsic
//! reads to the slice it came from. Where a kernel moves whole arrays between memory and registers, its
//! verified copy calls a helper (e.g. `load512`) with a trusted specification, whose body is the production
//! expression, and which `tests/intrinsics/` checks like an intrinsic.
use vstd::prelude::*;

#[cfg(target_arch = "aarch64")]
pub mod aarch64;
#[cfg(target_arch = "aarch64")]
pub mod aarch64_gfneon;
#[cfg(target_arch = "x86_64")]
pub mod x86;
#[cfg(target_arch = "x86_64")]
pub mod x86_gfneon;

verus! {

/// The value `core::mem::transmute::<S, D>(s)` returns: the bits of `s`, read as a `D`.
///
/// Uninterpreted: what it is for each pair of types is given by the view functions and the layout axioms.
pub uninterp spec fn transmuted<S, D>(s: S) -> D;

/// `transmute` returns [`transmuted`].
pub assume_specification<S, D>[ core::mem::transmute::<S, D> ](s: S) -> (d: D)
    ensures
        d == transmuted::<S, D>(s),
;

} // verus!
