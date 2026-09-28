#![cfg_attr(all(target_arch = "riscv64", target_os = "none"), no_std)]
#![cfg_attr(all(target_arch = "riscv64", target_os = "none"), no_main)]

#[cfg(all(target_arch = "riscv64", target_os = "none"))]
leanvm_guest::entry!(guest_main);

#[cfg(all(target_arch = "riscv64", target_os = "none"))]
fn guest_main() -> u64 {
    unsafe extern "C" {
        fn memcpy(dst: *mut u8, src: *const u8, count: usize) -> *mut u8;
        fn memcmp(left: *const u8, right: *const u8, count: usize) -> i32;
    }
    let mut header = [0u8; 4];
    let mut left = [0u8; 64];
    leanvm_guest::read_witness_exact(&mut header);
    leanvm_guest::read_witness_exact(&mut left);
    let _ = leanvm_guest::read_witness_vec(0).unwrap();
    let right = leanvm_guest::read_witness_vec(64).unwrap();
    let [source, destination, count, ordering] = header.map(usize::from);
    if source + count > left.len() || destination + count > right.len() {
        return 1;
    }
    let mut copied = [0xa5u8; 64];
    // SAFETY: bounds were checked, the arrays are disjoint, and byte pointers
    // permit every tested alignment. Opaque calls exercise the linked ABI.
    let (returned, comparison) = unsafe {
        let copy = core::hint::black_box(memcpy as unsafe extern "C" fn(*mut u8, *const u8, usize) -> *mut u8);
        let compare = core::hint::black_box(memcmp as unsafe extern "C" fn(*const u8, *const u8, usize) -> i32);
        (
            copy(copied.as_mut_ptr().add(destination), left.as_ptr().add(source), count),
            compare(left.as_ptr().add(source), right.as_ptr().add(destination), count),
        )
    };
    if returned != copied.as_mut_ptr().wrapping_add(destination) || (comparison.signum() + 1) as usize != ordering {
        return 2;
    }
    for (index, &byte) in copied.iter().enumerate() {
        let expected = if (destination..destination + count).contains(&index) {
            left[source + index - destination]
        } else {
            0xa5
        };
        if byte != expected {
            return 3;
        }
    }
    0
}

#[cfg(not(all(target_arch = "riscv64", target_os = "none")))]
fn main() {
    panic!("build memory_contracts for riscv64im-unknown-none-elf to execute it");
}
