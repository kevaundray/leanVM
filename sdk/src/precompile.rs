//! The machine's custom instructions, the precompiles: each proven as one row rather than
//! as the RISC-V instructions it replaces. They exist on the VM only.

use crate::blake2s::Block;

/// The BLAKE2s compression of message block `m` onto chaining value `h`, `t` bytes into
/// the message, `last` on the final block: one `blake2s` instruction (custom-0, opcode
/// `0x0b`, `funct3` the finalization flag, the counter in `rs2`).
#[inline(always)]
pub fn blake2s_compress(h: &[u64; 4], m: &[u64; 8], t: u64, last: bool) -> [u64; 4] {
    // Built here and nowhere else: a block kept in the hasher is copied whenever the hasher moves.
    let mut block = core::mem::MaybeUninit::<Block>::uninit();
    let base = block.as_mut_ptr();
    // SAFETY: the chaining value and the message are written before the instruction reads
    // them, and it writes the compression before it is read.
    // The block is this frame's, and nothing else holds it.
    unsafe {
        (&raw mut (*base).h).write(*h);
        (&raw mut (*base).m).write(*m);
        blake2s_compress_in_place(base, t, last);
        (&raw const (*base).out).read().assume_init()
    }
}

/// The `blake2s` instruction on the block at `base`: its `out` becomes the compression of its `m` onto its `h`.
///
/// # Safety
///
/// `base` points to a block whose `h` and `m` are initialized and whose `out` is writable.
#[inline(always)]
pub(crate) unsafe fn blake2s_compress_in_place(base: *mut Block, t: u64, last: bool) {
    // SAFETY: the caller's; the instruction reads `h` and `m` and writes `out`.
    unsafe {
        if last {
            core::arch::asm!(".insn r 0x0b, 1, 0, x0, {0}, {1}", in(reg) base, in(reg) t, options(nostack));
        } else {
            core::arch::asm!(".insn r 0x0b, 0, 0, x0, {0}, {1}", in(reg) base, in(reg) t, options(nostack));
        }
    }
}
