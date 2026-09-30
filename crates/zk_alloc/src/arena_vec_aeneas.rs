//! [`ArenaVec`] as a plain `Vec`, what the Lean extraction (`--cfg aeneas`) reads: the
//! arena only decides where the bytes live, never what they hold, and its raw
//! pointers are nothing Aeneas translates. Same API as `arena_vec.rs`.

use std::fmt;
use std::mem::{ManuallyDrop, MaybeUninit};
use std::ops::{Deref, DerefMut};
use std::ptr;

pub struct ArenaVec<T>(Vec<T>);

impl<T> ArenaVec<T> {
    #[must_use]
    pub const fn new() -> Self {
        Self(Vec::new())
    }

    #[must_use]
    pub fn with_capacity(cap: usize) -> Self {
        Self(Vec::with_capacity(cap))
    }

    #[must_use]
    pub fn filled(value: T, n: usize) -> Self
    where
        T: Clone,
    {
        let mut v = Self::with_capacity(n);
        v.resize(n, value);
        v
    }

    /// # Safety
    /// The all-zero bit pattern must be a valid, fully initialized `T`.
    #[must_use]
    pub unsafe fn zeroed(n: usize) -> Self {
        // SAFETY: every slot is written below before any read.
        let mut v = unsafe { Self::uninitialized(n) };
        // SAFETY: `v` owns `n` slots; the caller guarantees all-zero is a valid `T`.
        unsafe { ptr::write_bytes(v.as_mut_ptr(), 0u8, n) };
        v
    }

    #[must_use]
    pub fn from_slice(slice: &[T]) -> Self
    where
        T: Clone,
    {
        Self(slice.to_vec())
    }

    /// # Safety
    /// Every one of the `len` elements must be written before it is read.
    #[must_use]
    pub unsafe fn uninitialized(len: usize) -> Self {
        let mut v = Self::with_capacity(len);
        // SAFETY: the caller guarantees all `len` slots are written before read.
        unsafe { v.set_len(len) };
        v
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[must_use]
    pub fn capacity(&self) -> usize {
        self.0.capacity()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    #[must_use]
    pub fn as_ptr(&self) -> *const T {
        self.0.as_ptr()
    }

    pub fn as_mut_ptr(&mut self) -> *mut T {
        self.0.as_mut_ptr()
    }

    #[must_use]
    pub fn as_slice(&self) -> &[T] {
        &self.0
    }

    /// # Safety
    /// `new_len <= capacity()`, and every element below `new_len` must be
    /// initialized.
    pub unsafe fn set_len(&mut self, new_len: usize) {
        // SAFETY: the caller's guarantee is `Vec::set_len`'s.
        unsafe { self.0.set_len(new_len) };
    }

    pub fn reserve(&mut self, additional: usize) {
        self.0.reserve(additional);
    }

    pub fn push(&mut self, value: T) {
        self.0.push(value);
    }

    pub fn extend_from_slice(&mut self, other: &[T])
    where
        T: Clone,
    {
        self.0.extend_from_slice(other);
    }

    pub fn resize(&mut self, new_len: usize, value: T)
    where
        T: Clone,
    {
        self.0.resize(new_len, value);
    }

    pub fn truncate(&mut self, len: usize) {
        self.0.truncate(len);
    }
}

#[must_use]
pub fn alloc_uninit<T>(n: usize) -> ArenaVec<MaybeUninit<T>> {
    // SAFETY: `MaybeUninit<T>` is valid uninitialized.
    unsafe { ArenaVec::uninitialized(n) }
}

/// # Safety
/// Every element of `v` must hold an initialized `T`.
#[must_use]
pub unsafe fn assume_init<T>(v: ArenaVec<MaybeUninit<T>>) -> ArenaVec<T> {
    let mut v = ManuallyDrop::new(v.0);
    // SAFETY: `MaybeUninit<T>` has `T`'s layout, the caller guarantees every slot is
    // initialized, and `ManuallyDrop` gave up the old vector's ownership.
    ArenaVec(unsafe { Vec::from_raw_parts(v.as_mut_ptr().cast::<T>(), v.len(), v.capacity()) })
}

impl<T> Deref for ArenaVec<T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        &self.0
    }
}

impl<T> DerefMut for ArenaVec<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        &mut self.0
    }
}

impl<T> Default for ArenaVec<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone> Clone for ArenaVec<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T: fmt::Debug> fmt::Debug for ArenaVec<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.0, f)
    }
}

impl<T: PartialEq> PartialEq for ArenaVec<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T: PartialEq> PartialEq<[T]> for ArenaVec<T> {
    fn eq(&self, other: &[T]) -> bool {
        *self.0 == *other
    }
}

impl<T: PartialEq> PartialEq<Vec<T>> for ArenaVec<T> {
    fn eq(&self, other: &Vec<T>) -> bool {
        self.0 == *other
    }
}

impl<T: PartialEq> PartialEq<ArenaVec<T>> for Vec<T> {
    fn eq(&self, other: &ArenaVec<T>) -> bool {
        *self == other.0
    }
}

impl<T: Eq> Eq for ArenaVec<T> {}

impl<T> Extend<T> for ArenaVec<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.0.extend(iter);
    }
}

impl<T> FromIterator<T> for ArenaVec<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self(Vec::from_iter(iter))
    }
}

impl<'a, T> IntoIterator for &'a ArenaVec<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut ArenaVec<T> {
    type Item = &'a mut T;
    type IntoIter = std::slice::IterMut<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter_mut()
    }
}
