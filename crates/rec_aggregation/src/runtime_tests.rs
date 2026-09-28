#[test]
fn compiled_memory_intrinsics_preserve_bounds_and_unsigned_order() {
    let elf = include_bytes!(concat!(env!("OUT_DIR"), "/memory_contracts.elf"));
    let program = riscv::Program::from_elf(elf).unwrap();
    let run = |source: usize, destination: usize, count: usize, mismatch: Option<usize>| {
        let left: [u8; 64] = std::array::from_fn(|i| (i as u8).wrapping_mul(37).wrapping_add(128));
        let mut right = [0u8; 64];
        right[destination..destination + count].copy_from_slice(&left[source..source + count]);
        if let Some(index) = mismatch {
            right[destination + index] ^= 0x80;
        }
        let ordering = match left[source..source + count].cmp(&right[destination..destination + count]) {
            std::cmp::Ordering::Less => 0,
            std::cmp::Ordering::Equal => 1,
            std::cmp::Ordering::Greater => 2,
        };
        let mut witness = vec![source as u8, destination as u8, count as u8, ordering];
        witness.extend_from_slice(&left);
        witness.extend_from_slice(&right);
        let execution = program.execute([0; 32], &witness, 20_000).unwrap_or_else(|error| {
            panic!("source={source} destination={destination} count={count} mismatch={mismatch:?}: {error}")
        });
        assert_eq!(execution.witness_consumed, witness.len() as u64);
        if source == 0 && destination == 0 && count == 0 {
            assert!(program.execute([0; 32], &witness[..witness.len() - 1], 20_000).is_err());
        }
    };
    run(64, 64, 0, None);
    for count in [0, 1, 2, 7, 8, 9, 15, 16, 17, 31, 32, 33] {
        for source in 0..8 {
            for destination in 0..8 {
                run(source, destination, count, None);
                for index in 0..count {
                    if index == 0 || index == count / 2 || index == count - 1 {
                        run(source, destination, count, Some(index));
                    }
                }
            }
        }
    }
}
