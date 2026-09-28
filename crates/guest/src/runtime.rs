//! Single-hart RV64IM startup and allocator, enabled only for guest executables.
//!
//! link.x defines a monotonic heap [__heap_start, __heap_end) followed by a
//! separate 16 MiB stack [__stack_bottom, __stack_top). The stack grows down from
//! 0x100000000; allocation never enters that reservation. Guest code must stay
//! within the stack reservation. The ELF loader zeroes all PT_LOAD tails.
//! Allocations are bounded, aligned, and never reclaimed before EXIT; dropping
//! a Vec does not recover heap space. Exhaustion returns null to alloc's OOM
//! path, which panics and exits failure. No atomics, locks, interrupts or
//! multiple harts are part of this execution environment.

use core::alloc::{GlobalAlloc, Layout};
use core::cell::UnsafeCell;
use core::ptr;

core::arch::global_asm!(
    r#"
    .section .text._start,"ax",@progbits
    .globl _start
    .type _start,@function
    .balign 4
_start:
    .option push
    .option norvc
    .option norelax
    la gp, __global_pointer$
    la t0, __stack_top_value
    ld sp, 0(t0)
    la t0, __bss_start
    la t1, __bss_end
1:
    beq t0, t1, 2f
    sb zero, 0(t0)
    addi t0, t0, 1
    j 1b
2:
    call __leanvm_guest_main
    li a7, {exit}
    ecall
    .option pop
    .size _start, . - _start
"#,
    exit = const crate::ECALL_EXIT,
);

// Misaligned word accesses are native to this VM. Comparison checks a short
// prefix first so unequal keys do not fetch an unnecessary whole word.
core::arch::global_asm!(include_str!("memory.S"));

unsafe extern "C" {
    static __heap_start: u8;
    static __heap_end_value: usize;
}

struct BumpAllocator(UnsafeCell<usize>);

// SAFETY: the guest machine executes one hart and has no interrupts or threads;
// no allocator call can race or reenter another allocator call.
unsafe impl Sync for BumpAllocator {}

unsafe impl GlobalAlloc for BumpAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // SAFETY: only this allocator accesses its cursor, sequentially.
        let cursor = unsafe { &mut *self.0.get() };
        let start = ptr::addr_of!(__heap_start) as usize;
        // SAFETY: the linker emits an aligned, immutable pointer-sized value.
        let limit = unsafe { __heap_end_value };
        let current = if *cursor == 0 { start } else { *cursor };
        let Some(aligned) = current
            .checked_add(layout.align() - 1)
            .map(|value| value & !(layout.align() - 1))
        else {
            return ptr::null_mut();
        };
        let Some(end) = aligned.checked_add(layout.size().max(1)) else {
            return ptr::null_mut();
        };
        if end > limit {
            return ptr::null_mut();
        }
        *cursor = end;
        aligned as *mut u8
    }

    unsafe fn dealloc(&self, _pointer: *mut u8, _layout: Layout) {
        // The heap's lifetime is one execution. Reclaim it at EXIT, not on drop.
    }
}

#[global_allocator]
static ALLOCATOR: BumpAllocator = BumpAllocator(UnsafeCell::new(0));

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo<'_>) -> ! {
    crate::exit(1)
}
