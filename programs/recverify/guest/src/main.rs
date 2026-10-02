//! The leanVM verifier as a leanVM guest.
//!
//! The advice holds an inner program, the output its run claims and a proof of that run (`cpu::Proof`'s bytes, no
//! magic or version); the guest rebuilds the program (and so its digest), verifies the proof, and commits the inner
//! statement: the program's digest and the output. In mode 0 it runs `Program::verify`, the native verifier
//! unchanged. In mode 1 it runs `Program::verify_core` alone and commits the claims it leaves to the program and the
//! circuits too, as their hash (`claim_words`), for whoever holds the program to settle.
//!
//! ```text
//!     mode, n_text, text (two instructions a word), entry_pc, n_image, image, log_ram, log_advice,
//!     output[4], n_bytes, proof bytes (padded to words)
//! ```
//!
//! It builds `std` for a custom target (`riscv64im-leanvm-zkvm.json`, `os = "zkvm"`), whose platform layer calls
//! the `sys_*` functions below; the heap is a bump allocator. An advice starting `u64::MAX, op, n` runs `n` of one
//! primitive instead (`primitive`), to price it.
#![no_main]

use core::arch::global_asm;
use std::alloc::{GlobalAlloc, Layout};

use leanvm_core::cpu::{DeferredClaims, Program, Proof};
use leanvm_guest::PublicValues;

core::arch::global_asm!(".globl __advice_bytes", ".set __advice_bytes, {bytes}", bytes = const 8u64 << 23);

global_asm!(
    ".section .text._start",
    ".globl _start",
    "_start:",
    ".option push",
    ".option norelax",
    "la sp, __stack_top",
    ".option pop",
    "call {main}",
    "la t0, {output}",
    "ld a0, 0(t0)",
    "ld a1, 8(t0)",
    "ld a2, 16(t0)",
    "ld a3, 24(t0)",
    "li a7, 93",
    "ecall",
    main = sym guest_main,
    output = sym OUTPUT,
);

static mut OUTPUT: [u64; 4] = [0; 4];
static mut READ: usize = 0;

unsafe extern "C" {
    static __advice: u64;
    static __advice_top: u64;
    static __heap_start: u8;
    static __heap_end: u8;
}

fn take(n: usize) -> &'static [u64] {
    let (start, end) = (&raw const __advice, &raw const __advice_top);
    let words = (end as usize - start as usize) / 8;
    // SAFETY: the linker script reserves the region; one hart.
    unsafe {
        let advice = core::slice::from_raw_parts(start, words);
        let taken = advice.get(READ..READ + n).expect("the values fit the advice");
        READ += n;
        taken
    }
}

fn word() -> u64 {
    take(1)[0]
}

fn bytes(n: usize) -> &'static [u8] {
    let words = take(n.div_ceil(8));
    // SAFETY: words are bytes.
    unsafe { core::slice::from_raw_parts(words.as_ptr().cast(), n) }
}

extern "C" fn guest_main() {
    let mode = word();
    if mode == u64::MAX {
        let (op, n) = (word(), word());
        // SAFETY: one hart, the run is over.
        unsafe { core::ptr::write_volatile(&raw mut OUTPUT, primitive(op, n)) };
        return;
    }
    let n_text = word() as usize;
    let text: Vec<u32> = bytes(4 * n_text)
        .as_chunks::<4>()
        .0
        .iter()
        .map(|b| u32::from_le_bytes(*b))
        .collect();
    let entry_pc = word();
    let n_image = word() as usize;
    let image = take(n_image).to_vec();
    let (log_ram, log_advice) = (word() as usize, word() as usize);
    let output: [u64; 4] = take(4).try_into().unwrap();
    let n_bytes = word() as usize;
    let proof_bytes = bytes(n_bytes);

    let program = Program::new(&text, entry_pc, image, log_ram, log_advice).expect("a program");
    let digest: [u64; 4] =
        std::array::from_fn(|i| u64::from_le_bytes(program.digest()[8 * i..8 * i + 8].try_into().unwrap()));
    let mut public = PublicValues::new();
    public.commit(&digest).commit(&output);
    let proof = Proof::from_bytes(proof_bytes).expect("a proof");
    if mode == 0 {
        program.verify(&output, &proof).expect("the proof verifies");
    } else {
        let claims = program.verify_core(&output, &proof).expect("the proof's core verifies");
        public.commit(&claims_hash(&claims));
    }
    // SAFETY: one hart, the run is over.
    unsafe { core::ptr::write_volatile(&raw mut OUTPUT, public.digest()) };
}

/// The deferred claims as words, every `F192` its three coefficients, in field order. Their shapes are the
/// program's and the circuits', so no length rides along. The host has the same function.
fn claim_words(claims: &DeferredClaims) -> Vec<u64> {
    use primitives::field::F192;
    let mut words = Vec::new();
    let mut put = |xs: &[F192]| words.extend(xs.iter().flat_map(|x| [x.c0, x.c1, x.c2]));
    for (c, p) in &claims.program.terms {
        put(&[*c]);
        put(&p.bytecode);
        put(&p.twist);
        put(&[p.image_weight]);
        put(&p.image_point);
    }
    put(&[claims.program.value]);
    for claim in &claims.circuits {
        for (c, form) in &claim.terms {
            put(&[*c, form.alpha, form.z_skip]);
            put(&form.x_inner_rest);
            put(&form.r_inner_rest);
            put(&form.s_hat_v);
        }
        put(&[claim.value]);
    }
    words
}

/// The claims' BLAKE2s digest, by the machine's compression (`primitives::hash`).
fn claims_hash(claims: &DeferredClaims) -> [u64; 4] {
    let bytes: Vec<u8> = claim_words(claims).iter().flat_map(|w| w.to_le_bytes()).collect();
    let h = primitives::hash::hash(&bytes);
    std::array::from_fn(|i| u64::from_le_bytes(h[8 * i..8 * i + 8].try_into().unwrap()))
}

/// `n` chained runs of one primitive, on values the compiler cannot fold: 0 F64 product, 1 F192 product,
/// 2 F192 square, 3 F192 times F64, 4 F192 inverse, 5 the 64x64 carry-less product, 6 BLAKE2s compression,
/// anything else nothing (the loop alone).
fn primitive(op: u64, n: u64) -> [u64; 4] {
    use primitives::field::{F64, F192, gf2_64::mul_wide};
    let seed = core::hint::black_box([
        0x950e87d7f5606615u64,
        0x2c61275c9e6b6cf8,
        0x1f00bca0042db923,
        0x6dbca290a9eab706,
    ]);
    let mut x = F192 {
        c0: seed[0],
        c1: seed[1],
        c2: seed[2],
    };
    let y = F192 {
        c0: seed[3],
        c1: seed[2],
        c2: seed[1],
    };
    let mut k = F64(seed[0]);
    let mut w = 0u128;
    let mut h = [seed[0] as u32; 8];
    let m = [seed[1] as u32; 16];
    for i in 0..n {
        match op {
            0 => k = k * F64(seed[3] ^ i),
            1 => x = x * y,
            2 => x = x.square(),
            3 => x = x.mul_base(F64(seed[3] ^ i)),
            4 => x = x.inv(),
            5 => w ^= mul_wide(seed[0] ^ (w as u64), seed[3] ^ i),
            6 => primitives::hash::compress(&mut h, &m, i, false),
            _ => k = F64(k.0 ^ i),
        }
        core::hint::black_box((&x, &k, &w, &h));
    }
    [x.c0 ^ k.0, x.c1 ^ w as u64, x.c2 ^ (w >> 64) as u64, h[0] as u64]
}

/// The bump allocator: a release of the latest block pops the cursor, and nothing else is reclaimed.
struct Bump;

static mut CURSOR: usize = 0;

#[global_allocator]
static HEAP: Bump = Bump;

fn bump(layout: Layout) -> *mut u8 {
    // SAFETY: one hart; the symbols bound the heap.
    unsafe {
        if CURSOR == 0 {
            CURSOR = &raw const __heap_start as usize;
        }
        let start = CURSOR.next_multiple_of(layout.align());
        let end = start + layout.size();
        if end > &raw const __heap_end as usize {
            core::arch::asm!("unimp", options(noreturn));
        }
        CURSOR = end;
        start as *mut u8
    }
}

unsafe impl GlobalAlloc for Bump {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        bump(layout)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // SAFETY: one hart.
        unsafe {
            if ptr as usize + layout.size() == CURSOR {
                CURSOR = ptr as usize;
            }
        }
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        // SAFETY: one hart; a block ending at the cursor grows in place.
        unsafe {
            if ptr as usize + layout.size() == CURSOR && ptr as usize + new_size <= &raw const __heap_end as usize {
                CURSOR = ptr as usize + new_size;
                return ptr;
            }
            let new = bump(Layout::from_size_align_unchecked(new_size, layout.align()));
            core::ptr::copy_nonoverlapping(ptr, new, layout.size().min(new_size));
            new
        }
    }
}

// The platform layer std's zkvm target calls (`std::sys::pal::zkvm::abi`).
#[unsafe(no_mangle)]
extern "C" fn sys_alloc_aligned(bytes: usize, align: usize) -> *mut u8 {
    // SAFETY: std passes a valid layout.
    bump(unsafe { Layout::from_size_align_unchecked(bytes, align) })
}
#[unsafe(no_mangle)]
extern "C" fn sys_alloc_words(words: usize) -> *mut u32 {
    sys_alloc_aligned(4 * words, 4).cast()
}
#[unsafe(no_mangle)]
extern "C" fn sys_getenv(_: *mut u32, _: usize, _: *const u8, _: usize) -> usize {
    usize::MAX
}
#[unsafe(no_mangle)]
extern "C" fn sys_argc() -> usize {
    0
}
#[unsafe(no_mangle)]
extern "C" fn sys_argv(_: *mut u32, _: usize, _: usize) -> usize {
    0
}
#[unsafe(no_mangle)]
extern "C" fn sys_rand(buf: *mut u32, words: usize) {
    // SAFETY: std's buffer. Nothing in the verifier wants entropy; zeros keep the run deterministic.
    unsafe { core::ptr::write_bytes(buf, 0, words) }
}
#[unsafe(no_mangle)]
extern "C" fn sys_write(_: u32, _: *const u8, _: usize) {}
#[unsafe(no_mangle)]
extern "C" fn sys_log(_: *const u8, _: usize) {}
#[unsafe(no_mangle)]
extern "C" fn sys_read(_: u32, _: *mut u8, _: usize) -> usize {
    0
}
#[unsafe(no_mangle)]
extern "C" fn sys_cycle_count() -> usize {
    0
}
#[unsafe(no_mangle)]
extern "C" fn sys_output(_: u32, _: u32) {}
#[unsafe(no_mangle)]
extern "C" fn sys_halt() {
    // SAFETY: an illegal instruction: no proof.
    unsafe { core::arch::asm!("unimp", options(noreturn)) }
}
#[unsafe(no_mangle)]
extern "C" fn sys_panic(_: *const u8, _: usize) -> ! {
    // SAFETY: as above.
    unsafe { core::arch::asm!("unimp", options(noreturn)) }
}

// `+forced-atomics` lowers an atomic read-modify-write to a `__sync_*` call; one hart, so plain memory ops.
macro_rules! sync_ops {
    ($t:ty, $cas:ident, $swap:ident, $($name:ident: $op:expr),*) => {
        #[unsafe(no_mangle)]
        unsafe extern "C" fn $cas(ptr: *mut $t, old: $t, new: $t) -> $t {
            // SAFETY: the caller's atomic; one hart.
            unsafe {
                let seen = ptr.read_volatile();
                if seen == old {
                    ptr.write_volatile(new);
                }
                seen
            }
        }
        #[unsafe(no_mangle)]
        unsafe extern "C" fn $swap(ptr: *mut $t, new: $t) -> $t {
            // SAFETY: as above.
            unsafe {
                let seen = ptr.read_volatile();
                ptr.write_volatile(new);
                seen
            }
        }
        $(
            #[unsafe(no_mangle)]
            unsafe extern "C" fn $name(ptr: *mut $t, v: $t) -> $t {
                let op: fn($t, $t) -> $t = $op;
                // SAFETY: as above.
                unsafe {
                    let seen = ptr.read_volatile();
                    ptr.write_volatile(op(seen, v));
                    seen
                }
            }
        )*
    };
}
sync_ops!(u8, __sync_val_compare_and_swap_1, __sync_lock_test_and_set_1,
    __sync_fetch_and_add_1: u8::wrapping_add, __sync_fetch_and_sub_1: u8::wrapping_sub,
    __sync_fetch_and_or_1: |a, b| a | b, __sync_fetch_and_and_1: |a, b| a & b, __sync_fetch_and_xor_1: |a, b| a ^ b);
sync_ops!(u16, __sync_val_compare_and_swap_2, __sync_lock_test_and_set_2,
    __sync_fetch_and_add_2: u16::wrapping_add, __sync_fetch_and_sub_2: u16::wrapping_sub,
    __sync_fetch_and_or_2: |a, b| a | b, __sync_fetch_and_and_2: |a, b| a & b, __sync_fetch_and_xor_2: |a, b| a ^ b);
sync_ops!(u32, __sync_val_compare_and_swap_4, __sync_lock_test_and_set_4,
    __sync_fetch_and_add_4: u32::wrapping_add, __sync_fetch_and_sub_4: u32::wrapping_sub,
    __sync_fetch_and_or_4: |a, b| a | b, __sync_fetch_and_and_4: |a, b| a & b, __sync_fetch_and_xor_4: |a, b| a ^ b);
sync_ops!(u64, __sync_val_compare_and_swap_8, __sync_lock_test_and_set_8,
    __sync_fetch_and_add_8: u64::wrapping_add, __sync_fetch_and_sub_8: u64::wrapping_sub,
    __sync_fetch_and_or_8: |a, b| a | b, __sync_fetch_and_and_8: |a, b| a & b, __sync_fetch_and_xor_8: |a, b| a ^ b);
