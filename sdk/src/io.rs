//! What a guest reads and what it proves: `read` takes values from the advice, in place,
//! and `commit` makes values public. There are no system calls: the advice is memory the
//! prover fills before the run, at the addresses `link.ld` fixes, and the run's output is
//! the BLAKE2s digest of everything committed, in order, which the verifier recomputes from
//! the public values.

use crate::Blake2s;

/// A type made of 64-bit words and nothing else, so that any words are one.
///
/// # Safety
///
/// The type is `repr(C)` (or an array), its size a multiple of 8 and its alignment 8, it
/// has no padding, and every bit pattern of its words is a valid value: integers and arrays
/// of them, never a `bool`, an enum, a reference or a pointer.
pub unsafe trait Words: Sized + 'static {}

// SAFETY: a word is a word.
unsafe impl Words for u64 {}
// SAFETY: an array of word types is its elements' words, back to back.
unsafe impl<T: Words, const N: usize> Words for [T; N] {}

/// A value of a type from another crate as its words, for a host laying out advice that
/// the guest reads with `read_unchecked`.
///
/// # Safety
///
/// `T` is words only, as [`Words`] says.
pub unsafe fn as_words_unchecked<T>(value: &T) -> &[u64] {
    const { assert_words::<T>() };
    // SAFETY: `T` is its words with no padding (the caller's).
    unsafe { core::slice::from_raw_parts((value as *const T).cast(), size_of::<T>() / 8) }
}

/// That `T` is whole, aligned words, at compile time.
const fn assert_words<T>() {
    assert!(
        size_of::<T>().is_multiple_of(8) && align_of::<T>() == 8,
        "a type of whole words"
    );
}

/// The public values a run commits, and the output they make: their BLAKE2s digest.
///
/// On the VM, `commit` feeds the run's own; off it, this is how a host computes the output
/// a guest must give.
pub struct PublicValues(Blake2s);

impl Default for PublicValues {
    fn default() -> Self {
        Self::new()
    }
}

impl PublicValues {
    pub const fn new() -> Self {
        Self(Blake2s::new())
    }

    /// Commit a value.
    #[inline(always)]
    pub fn commit<T: Words>(&mut self, value: &T) -> &mut Self {
        // SAFETY: `T` is words only (`Words`).
        self.0.update_words(unsafe { as_words_unchecked(value) });
        self
    }

    /// The output: the digest of everything committed.
    pub fn digest(self) -> [u64; 4] {
        self.0.finalize_words()
    }
}

#[cfg(all(target_arch = "riscv64", target_os = "none"))]
pub use vm::{commit, read, read_slice, read_unchecked};

#[cfg(all(target_arch = "riscv64", target_os = "none"))]
pub(crate) mod vm {
    use super::{Words, as_words_unchecked, assert_words};
    use crate::blake2s::{Block, IV};
    use core::mem::MaybeUninit;

    /// The output `_start` loads into `a0..a3` when the run ends.
    pub(crate) static mut OUTPUT: [u64; 4] = [0; 4];
    /// What the run has committed so far: BLAKE2s streamed through the instruction's own block.
    static mut PUBLIC: Public = Public {
        block: Block {
            h: IV,
            out: MaybeUninit::uninit(),
            m: [0; 8],
        },
        // SAFETY: the message is in the static.
        next: unsafe { (&raw mut PUBLIC.block.m).cast() },
        done: 0,
    };
    /// The advice words read so far.
    static mut READ: usize = 0;

    /// The committed words' BLAKE2s, in progress: the block the instruction reads, the message word the next
    /// committed word goes to, and the bytes compressed before the message.
    ///
    /// A word is one store and a pointer bump, and a full block is compressed where it is, only once a word is known
    /// to follow it: the last block is the one compressed as last.
    struct Public {
        block: Block,
        next: *mut u64,
        done: u64,
    }

    impl Public {
        #[inline(always)]
        fn message(&mut self) -> *mut u64 {
            (&raw mut self.block.m).cast()
        }

        #[inline(always)]
        fn commit(&mut self, words: &[u64]) {
            let (start, mut next) = (self.message(), self.next);
            // SAFETY: the message's eight words.
            let end = unsafe { start.add(8) };
            for &word in words {
                if next == end {
                    self.absorb();
                    next = start;
                }
                // SAFETY: `next` is a word of the message, below `end`.
                unsafe {
                    next.write(word);
                    next = next.add(1);
                }
            }
            self.next = next;
        }

        /// Compress the full message, which more words follow: the compression becomes the chaining value.
        fn absorb(&mut self) {
            self.done += 64;
            // SAFETY: the block is the static's, its chaining value and message initialized.
            unsafe {
                crate::precompile::blake2s_compress_in_place(&mut self.block, self.done, false);
                self.block.h = self.block.out.assume_init();
            }
        }

        /// The digest: the last block zero-padded, the counter every byte committed.
        fn finish(&mut self) -> [u64; 4] {
            // SAFETY: `next` and the message's end are in the message.
            let filled = unsafe { self.next.offset_from(self.message()) } as usize;
            self.block.m[filled..].fill(0);
            // SAFETY: as in `absorb`.
            unsafe {
                crate::precompile::blake2s_compress_in_place(&mut self.block, self.done + 8 * filled as u64, true);
                self.block.out.assume_init()
            }
        }
    }

    unsafe extern "C" {
        /// The advice region's bounds (`link.ld`).
        static __advice: u64;
        static __advice_top: u64;
    }

    /// The advice: words the prover supplies, which the statement says nothing about.
    fn advice() -> &'static [u64] {
        // The two symbols bound the region without belonging to one object, so the length
        // is address arithmetic rather than `offset_from`, which asks for one allocation.
        let (start, end) = (&raw const __advice, &raw const __advice_top);
        let words = (end as usize - start as usize) / size_of::<u64>();
        // SAFETY: the linker script reserves the region, it holds whole words, and nothing
        // in this crate writes it.
        unsafe { core::slice::from_raw_parts(start, words) }
    }

    /// The next value of the advice, in place: nothing is copied or decoded.
    ///
    /// The prover chose it, so the guest has to check it. Reading past the advice panics,
    /// so the run has no proof.
    #[inline(always)]
    pub fn read<T: Words>() -> &'static T {
        &read_slice::<T>(1)[0]
    }

    /// The next `n` values of the advice, in place.
    #[inline(always)]
    pub fn read_slice<T: Words>(n: usize) -> &'static [T] {
        // SAFETY: any words are a `T` (`Words`).
        unsafe { take(n) }
    }

    /// The next value of the advice as a type from another crate, in place: how a guest's
    /// `main` reads its library's types, which need not know the VM.
    ///
    /// # Safety
    ///
    /// `T` is words only, as [`Words`] says.
    #[inline(always)]
    pub unsafe fn read_unchecked<T>() -> &'static T {
        // SAFETY: the caller's.
        unsafe { &take::<T>(1)[0] }
    }

    /// # Safety
    ///
    /// `T` is words only, as [`Words`] says.
    #[inline(always)]
    unsafe fn take<T>(n: usize) -> &'static [T] {
        const { assert_words::<T>() };
        let words = n.checked_mul(size_of::<T>() / 8).expect("the values fit the advice");
        // SAFETY: one hart, no interrupts: nothing else touches `READ`.
        let start = unsafe { READ };
        let end = start.checked_add(words).expect("the values fit the advice");
        let taken = advice().get(start..end).expect("the values fit the advice");
        // SAFETY: as above.
        unsafe { READ = end };
        // SAFETY: the words are aligned to 8, as `T` is, and any words are a `T` (the caller's).
        unsafe { core::slice::from_raw_parts(taken.as_ptr().cast(), n) }
    }

    /// Make a value public: the run's output is the digest of everything committed, in order.
    #[inline(always)]
    pub fn commit<T: Words>(value: &T) {
        // SAFETY: one hart, no interrupts: nothing else touches `PUBLIC`; `T` is words only (`Words`).
        unsafe { (*(&raw mut PUBLIC)).commit(as_words_unchecked(value)) }
    }

    /// Called by `_start` once `main` returns: the output is the digest of what was committed.
    pub(crate) extern "C" fn finish() {
        // SAFETY: the run is over, so nothing touches `PUBLIC` after.
        let digest = unsafe { (*(&raw mut PUBLIC)).finish() };
        // SAFETY: as above, for `OUTPUT`.
        unsafe { core::ptr::write_volatile(&raw mut OUTPUT, digest) }
    }
}

// TODO: remove this macro by making the advice region's size per proof rather than per program:
// the prover announces a power of two, bound into the transcript before any challenge and range
// checked by both verifiers (at most `MAX_LOG_ADVICE`, inside the advice window). That is sound,
// the advice being the prover's anyway: a region too small traps the read past its end, one too
// large only costs the prover. `read` would then drop its bounds check against `__advice_top` and
// rely on that trap.
/// Size the guest's advice region, in words: a power of two.
///
/// A guest that names none gets 8192 words.
///
/// The prover commits to the whole region, so a guest sizes it to what it reads.
///
/// ```ignore
/// leanvm_guest::advice_words!(1 << 16);
/// ```
#[macro_export]
macro_rules! advice_words {
    ($words:expr) => {
        // The loader takes a region's size to be a power of two.
        const _: () = assert!(($words as u64).is_power_of_two(), "the advice region is a power of two");
        // An absolute symbol: the linker script places the region's end at the base plus its value.
        core::arch::global_asm!(
            ".globl __advice_bytes",
            ".set __advice_bytes, {bytes}",
            bytes = const 8 * ($words as u64),
        );
    };
}
