//! The native verifier is portable and single-threaded: it runs on the calling thread, with no SIMD intrinsic, no
//! inline assembly and no pool dispatch, so that it computes the same way on every target.
//!
//! Its arithmetic is the `*_portable` field methods and its hashing [`crate::hash::portable`].
//! Each of its entry points holds a [`Section`] while it runs, which refuses what it must not reach:
//!
//! - a pool dispatch panics, always ([`parallel::serial`]);
//! - with the `guard` feature, which the workspace's tests enable, so does every SIMD or assembly kernel of this crate.

use std::marker::PhantomData;

#[cfg(feature = "guard")]
use std::cell::Cell;

#[cfg(feature = "guard")]
thread_local! {
    /// Whether this thread holds a [`Section`].
    static INSIDE: Cell<bool> = const { Cell::new(false) };
}

/// Run as the verifier runs until the returned guard drops: on this thread, refusing pool dispatch, and under `guard`
/// every kernel.
#[must_use = "the section lasts only while the guard lives"]
pub fn enter() -> Section {
    Section {
        _serial: parallel::serial(),
        #[cfg(feature = "guard")]
        previous: INSIDE.replace(true),
        _thread: PhantomData,
    }
}

/// A portable section: dropping it restores what was refused before, on return and on unwinding alike.
pub struct Section {
    _serial: parallel::Serial,
    #[cfg(feature = "guard")]
    previous: bool,
    /// The section is this thread's, so the guard stays on it.
    _thread: PhantomData<*const ()>,
}

#[cfg(feature = "guard")]
impl Drop for Section {
    fn drop(&mut self) {
        INSIDE.set(self.previous);
    }
}

/// A SIMD or assembly kernel is about to run: under `guard`, a panic inside a [`Section`].
#[inline(always)]
pub(crate) fn kernel() {
    #[cfg(feature = "guard")]
    assert!(!INSIDE.get(), "a SIMD or assembly kernel inside the portable verifier");
}
