//! The proving arena as a [`std::alloc::Allocator`], and [`ArenaVec`], the `Vec` over it. Size arena-backed buffers up front anyway: growing copies, and the old allocation is only recycled if it clears the arena's reuse floor.

use std::alloc::{AllocError, Allocator, Layout};
use std::mem::MaybeUninit;
use std::ptr::{self, NonNull};

use crate::{raw_alloc, raw_dealloc};

/// The proving arena: this thread's slab inside a phase, the system allocator otherwise.
///
/// Zero-sized, so an [`ArenaVec`] is the size of a `Vec`. Which side a block came from is decided on release by
/// address range, so one handle serves both.
#[derive(Clone, Copy, Debug, Default)]
pub struct Arena;

// SAFETY: `raw_alloc` returns a block valid for `layout.size()` bytes at `layout.align()` (it only ever raises the
// alignment), or null, reported as `AllocError`; `raw_dealloc` takes back exactly what `raw_alloc` handed out. The
// block stays valid until it is released or the next phase opens, which the crate's phase rule forbids any live
// `ArenaVec` to see. Zero-sized requests never reach the arena.
unsafe impl Allocator for Arena {
    #[inline(always)]
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        if layout.size() == 0 {
            // SAFETY: an alignment is nonzero.
            let dangling = unsafe { NonNull::new_unchecked(ptr::without_provenance_mut(layout.align())) };
            return Ok(NonNull::slice_from_raw_parts(dangling, 0));
        }
        // SAFETY: `layout` has a power-of-two alignment and a nonzero size.
        let p = unsafe { raw_alloc(layout.size(), layout.align()) };
        NonNull::new(p)
            .map(|p| NonNull::slice_from_raw_parts(p, layout.size()))
            .ok_or(AllocError)
    }

    #[inline(always)]
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        if layout.size() != 0 {
            // SAFETY: the caller guarantees `ptr` came from `allocate` with this layout.
            unsafe { raw_dealloc(ptr.as_ptr(), layout.size(), layout.align()) };
        }
    }
}

/// An owning, growable buffer allocated from the proving arena.
pub type ArenaVec<T> = Vec<T, Arena>;

/// The constructors `Vec` defines for the global allocator only, for [`ArenaVec`].
pub trait ArenaVecExt<T>: Sized {
    /// An empty buffer. Allocates nothing.
    fn new() -> Self;

    /// An empty buffer with room for `cap` elements.
    fn with_capacity(cap: usize) -> Self;

    /// `n` elements, each a clone of `value`, the arena's `vec![value; n]`. Prefer [`zeroed`](Self::zeroed) when
    /// the value is all-zero bytes.
    fn filled(value: T, n: usize) -> Self
    where
        T: Clone;

    /// `n` zero-filled elements.
    ///
    /// # Safety
    /// The all-zero bit pattern must be a valid, fully initialized `T`, true of the field types here and their SIMD
    /// packings, whose zero is all-zero bytes.
    unsafe fn zeroed(n: usize) -> Self;

    /// The arena's `slice.to_vec()`.
    fn from_slice(slice: &[T]) -> Self
    where
        T: Clone;

    /// `len` slots of uninitialized memory, ready to be filled in place (in parallel, typically).
    ///
    /// # Safety
    /// Every one of the `len` elements must be written before it is read.
    unsafe fn uninitialized(len: usize) -> Self;

    /// The arena's `collect()`.
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self;
}

impl<T> ArenaVecExt<T> for ArenaVec<T> {
    #[inline]
    fn new() -> Self {
        Vec::new_in(Arena)
    }

    #[inline]
    fn with_capacity(cap: usize) -> Self {
        Vec::with_capacity_in(cap, Arena)
    }

    #[inline]
    fn filled(value: T, n: usize) -> Self
    where
        T: Clone,
    {
        let mut v = Self::with_capacity(n);
        v.resize(n, value);
        v
    }

    #[inline]
    unsafe fn zeroed(n: usize) -> Self {
        let mut v = Self::with_capacity(n);
        // SAFETY: `v` has room for `n`, and the caller guarantees all-zero is a valid `T`.
        unsafe {
            ptr::write_bytes(v.as_mut_ptr(), 0u8, n);
            v.set_len(n);
        }
        v
    }

    #[inline]
    fn from_slice(slice: &[T]) -> Self
    where
        T: Clone,
    {
        let mut v = Self::with_capacity(slice.len());
        v.extend_from_slice(slice);
        v
    }

    #[inline]
    #[expect(
        clippy::uninit_vec,
        reason = "the caller's contract: every slot is written before it is read"
    )]
    unsafe fn uninitialized(len: usize) -> Self {
        let mut v = Self::with_capacity(len);
        // SAFETY: the caller guarantees all `len` slots are written before read.
        unsafe { v.set_len(len) };
        v
    }

    #[inline]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut v = Self::new();
        v.extend(iter);
        v
    }
}

/// `n` arena-backed slots to be initialized in place, one element at a time.
///
/// The `MaybeUninit` element type is what makes a partial fill expressible: write through the slice, then
/// [`assume_init`] once every slot is set. Prefer [`ArenaVecExt::uninitialized`] when the fill is a bulk write over
/// `&mut [T]`.
#[inline]
#[must_use]
pub fn alloc_uninit<T>(n: usize) -> ArenaVec<MaybeUninit<T>> {
    // SAFETY: `MaybeUninit<T>` is valid uninitialized.
    unsafe { ArenaVec::uninitialized(n) }
}

/// Reinterpret a fully written [`alloc_uninit`] buffer as its element type.
///
/// # Safety
/// Every element of `v` must hold an initialized `T`.
#[inline]
#[must_use]
pub unsafe fn assume_init<T>(v: ArenaVec<MaybeUninit<T>>) -> ArenaVec<T> {
    let (ptr, len, cap, alloc) = v.into_parts_with_allocator();
    // SAFETY: `MaybeUninit<T>` has the layout of `T`, so the allocation matches; the caller guarantees every slot is
    // initialized, and `into_parts_with_allocator` transferred sole ownership.
    unsafe { Vec::from_parts_in(ptr.cast::<T>(), len, cap, alloc) }
}
