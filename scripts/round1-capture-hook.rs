    if let Some(root) = std::env::var_os("ARM_ATTRIBUTION_INPUT_DIR") {
        let root = std::path::PathBuf::from(root);
        for (class, input) in inputs.iter().enumerate() {
            let dir = root.join(format!("class{class}"));
            std::fs::create_dir_all(&dir).expect("create Round1 capture directory");
            std::fs::write(dir.join("shape.txt"), format!("{} {} {} {}\n",
                input.m, input.padding.k_log, input.padding.useful_bits_per_block, input.padding.live_blocks,
            )).expect("write Round1 capture shape");
            for (name, bytes) in [("a.bin", input.bits.a), ("b.bin", input.bits.b), ("c.bin", input.c)] {
                std::fs::write(dir.join(name), bytes).expect("write Round1 packed capture");
            }
            let mut challenges = Vec::with_capacity((input.m - K_SKIP) * 24);
            for value in &r_rest[..input.m - K_SKIP] {
                for limb in [value.c0, value.c1, value.c2] {
                    challenges.extend_from_slice(&limb.to_le_bytes());
                }
            }
            std::fs::write(dir.join("r.bin"), challenges).expect("write Round1 challenge capture");
        }
    }
