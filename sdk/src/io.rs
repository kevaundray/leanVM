//! A run's input and output: the public input, the advice and the public output, all
//! plain memory at addresses `link.ld` fixes. There are no system calls: the machine
//! seeds the input and the advice before the run, and `_start` returns the output.

/// The output `_start` loads into `a0..a3` when `main` returns.
pub(crate) static mut OUTPUT: [u64; 4] = [0; 4];

unsafe extern "C" {
    /// RAM's first four words, and the advice region's bounds (`link.ld`).
    static __input: [u64; 4];
    static __advice: u64;
    static __advice_top: u64;
}

/// The run's public input.
pub fn input() -> [u64; 4] {
    // SAFETY: the linker script reserves these words, and nothing writes them.
    unsafe { core::ptr::read_volatile(&raw const __input) }
}

/// The advice: words the prover supplies, which the statement says nothing about, so
/// a guest has to check what it reads here.
pub fn advice() -> &'static [u64] {
    // The two symbols bound the region without belonging to one object, so the length
    // is address arithmetic rather than `offset_from`, which asks for one allocation.
    let (start, end) = (&raw const __advice, &raw const __advice_top);
    let words = (end as usize - start as usize) / size_of::<u64>();
    // SAFETY: the linker script reserves the region, it holds whole words, and nothing
    // in this crate writes it.
    unsafe { core::slice::from_raw_parts(start, words) }
}

/// Set the run's public output, which the run returns in `a0..a3` when `main` does.
pub fn output(words: [u64; 4]) {
    // SAFETY: one hart, no interrupts: nothing else touches `OUTPUT`.
    unsafe { core::ptr::write_volatile(&raw mut OUTPUT, words) }
}

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
