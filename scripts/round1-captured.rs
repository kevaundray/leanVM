    // Temporary attribution harness. ROUND1_INPUT_DIR replays captured witness
    // bytes and challenges; otherwise required shape fields select synthetic data.
    // Component working sets are deliberately separate; their timings must not
    // be subtracted from or added up to predict the fused production sweep.
    #[test]
    #[ignore = "temporary native-hardware Round1 attribution; requires captured input or traced shape"]
    fn diagnostic_round1_components() {
        use std::hint::black_box;
        use std::time::Instant;

        let required = |name: &str| -> usize {
            std::env::var(name).unwrap_or_else(|_| panic!("set {name} from a Round1 class trace")).parse().unwrap()
        };
        let optional = |name: &str, default: usize| -> usize {
            std::env::var(name).map_or(default, |v| v.parse().unwrap())
        };
        let input_dir = std::env::var_os("ROUND1_INPUT_DIR").map(std::path::PathBuf::from);
        let (m, padding) = if let Some(dir) = &input_dir {
            let shape = std::fs::read_to_string(dir.join("shape.txt")).expect("read captured shape");
            let shape: Vec<usize> = shape.split_whitespace().map(|v| v.parse().unwrap()).collect();
            assert_eq!(shape.len(), 4, "capture shape is m k_log useful_bits live_blocks");
            (shape[0], PaddingSpec { k_log: shape[1], useful_bits_per_block: shape[2], live_blocks: shape[3] })
        } else {
            (required("ROUND1_M"), PaddingSpec {
                k_log: required("ROUND1_K_LOG"),
                useful_bits_per_block: required("ROUND1_USEFUL_BITS"),
                live_blocks: required("ROUND1_LIVE_BLOCKS"),
            })
        };
        let repeats = optional("ROUND1_REPEATS", 5);
        let sample_limit = optional("ROUND1_SAMPLE_WINDOWS", 256);
        assert!(m >= K_SKIP + N_INNER && padding.k_log <= m);
        assert!(padding.useful_bits_per_block <= 1 << padding.k_log);
        assert!(repeats > 0 && sample_limit > 0);
        let bytes = (1usize << m) / 8;
        let (a, b, c, r) = if let Some(dir) = &input_dir {
            let load = |name| std::fs::read(dir.join(name)).expect("read Round1 capture");
            let raw_r = load("r.bin");
            assert_eq!(raw_r.len(), (m - K_SKIP) * 24, "captured challenge length");
            let r: Vec<_> = raw_r.chunks_exact(24).map(|bytes| {
                let limb = |i| u64::from_le_bytes(bytes[i..i + 8].try_into().unwrap());
                F192::new(limb(0), limb(8), limb(16))
            }).collect();
            (load("a.bin"), load("b.bin"), load("c.bin"), r)
        } else {
            let mut rng = Rng::new(0x524f_554e_4431);
            let block_bytes = (1usize << padding.k_log) / 8;
            assert!(block_bytes > 0);
            let mut a = pack_bits(&rng.bits(1 << m));
            let mut b = pack_bits(&rng.bits(1 << m));
            for packed in [&mut a, &mut b] {
                for block in packed.chunks_exact_mut(block_bytes) {
                    let full = padding.useful_bits_per_block / 8;
                    let bits = padding.useful_bits_per_block % 8;
                    if bits > 0 {
                        block[full] &= (1u8 << bits) - 1;
                    }
                    block[full + usize::from(bits > 0)..].fill(0);
                }
                if padding.live_blocks < bytes / block_bytes {
                    let tail_start = padding.live_blocks * block_bytes;
                    for start in ((tail_start + block_bytes)..bytes).step_by(block_bytes) {
                        packed.copy_within(tail_start..tail_start + block_bytes, start);
                    }
                }
            }
            let c: Vec<u8> = a.iter().zip(&b).map(|(a, b)| a & b).collect();
            let r = build_protocol_r_rest(m, &rng.ext_vec(m - K_SKIP - N_INNER));
            (a, b, c, r)
        };
        for input in [&a, &b, &c] {
            assert_eq!(input.len(), bytes, "packed input length");
        }
        let table = make_inv_table();
        let tail = padding.tail(m, K_SKIP + N_INNER, K_SKIP + N_INNER, &r);
        let windows = tail.map_or(1 << (m - K_SKIP - N_INNER), |t| t.head >> (K_SKIP + N_INNER));
        let (mask, counts) = build_b_med_counts(&padding);
        let eq = SplitEq::with_high_vars(&r[N_INNER..], EQ_HIGH_VARS);
        let eq_lo: Vec<_> = eq.low.iter().map(|v| *v * d_inv()).collect();
        let samples = windows.min(sample_limit);
        assert!(samples > 0, "class has no head windows; benchmark its traced tail cube instead");
        let weights: Vec<_> = (0..samples).map(|w| eq_lo[w % eq_lo.len()]).collect();
        let nmedium: Vec<_> = (0..samples).map(|w| counts[w & mask] as usize).collect();
        let medium_count: usize = nmedium.iter().sum();
        let mut expanded = Vec::with_capacity(medium_count);
        let mut ab_rows = vec![[[0u8; ELL]; N_MEDIUM_VALUES]; samples];
        let mut c_rows = ab_rows.clone();
        for w in 0..samples {
            for med in 0..nmedium[w] {
                let offset = w * 1024 + med * 64;
                let mut columns = [[[F8::ZERO; ELL]; 8]; 2];
                for (input, cols) in [&a, &b].into_iter().zip(&mut columns) {
                    for (k, col) in cols.iter_mut().enumerate() {
                        let row = &input[offset + 8 * k..offset + 8 * k + 8];
                        table.apply(row, col);
                        let mut oracle = [F8::ZERO; ELL];
                        table.apply_scalar(row, &mut oracle);
                        assert_eq!(*col, oracle, "NTT w={w} med={med} k={k}");
                    }
                }
                let mut scalar = [0; ELL];
                shift_reduce_inner_ab_scalar(&a, &b, &table, w * 1024, med, &mut scalar);
                shift_reduce_inner_ab(&a, &b, &table, w * 1024, med, &mut ab_rows[w][med]);
                assert_eq!(ab_rows[w][med], scalar, "fused AB w={w} med={med}");
                assert_eq!(diagnostic_gf8_shift(&columns), scalar, "isolated GF8 w={w} med={med}");
                expanded.push(columns);
                let input: &[u8; 64] = c[offset..offset + 64].try_into().unwrap();
                bit_transpose_64bytes(input, &mut c_rows[w][med]);
                for lane in 0..ELL {
                    let expected = (0..8).fold(0, |acc, k| acc | (((input[k * 8 + lane / 8] >> (lane % 8)) & 1) << k));
                    assert_eq!(c_rows[w][med][lane], expected, "C extract");
                }
            }
        }
        let mut converted = Convert::new();
        let mut oracle = [[F192::ZERO; ELL]; 2];
        for w in 0..samples {
            converted.accumulate(&ab_rows[w][..nmedium[w]], &c_rows[w][..nmedium[w]], weights[w]);
            for lane in 0..ELL {
                for med in 0..nmedium[w] {
                    oracle[0][lane] += gamma_powers()[med] * phi8_192(F8(ab_rows[w][med][lane])) * weights[w];
                }
            }
            for lane in 0..ELL {
                for med in 0..nmedium[w] {
                    oracle[1][lane] += gamma_powers()[med] * phi8_192(F8(c_rows[w][med][lane])) * weights[w];
                }
            }
        }
        assert_eq!(converted.values(), (oracle[0], oracle[1]), "medium conversion plus eq_lo");
        let reference = diagnostic_round1_reference([&a, &b, &c], m, &r, &table, &padding);
        assert_eq!(
            round1_shift_reduce_extract_c_packed_padded(&a, &b, &c, m, &r, &table, &padding),
            reference,
            "full production sweep including tail and C extension",
        );
        let measure = |label: &str, units: usize, f: &mut dyn FnMut()| {
            f(); // warm caches and lazy tables outside the timed interval
            let start = Instant::now();
            for _ in 0..repeats {
                f();
            }
            eprintln!("round1_diag component={label} units_per_repeat={units} repeats={repeats} elapsed_ns={}", start.elapsed().as_nanos());
        };
        eprintln!("round1_diag m={m} k_log={} useful_bits={} live_blocks={} head_windows={windows} sample_windows={samples} sample_medium={medium_count} worker_bytes={} synthetic={} neon_tiled={}",
            padding.k_log, padding.useful_bits_per_block, padding.live_blocks, core::mem::size_of::<WorkerState>(),
            input_dir.is_none(), false);
        measure("production_round1", windows, &mut || {
            black_box(round1_shift_reduce_extract_c_packed_padded(black_box(&a), black_box(&b), black_box(&c), m, &r, &table, &padding));
        });
        measure("ntt_lookup", medium_count * 16, &mut || {
            let mut out = [F8::ZERO; ELL];
            for (w, &n) in nmedium.iter().enumerate() {
                for med in 0..n {
                    for input in [&a, &b] {
                        for k in 0..8 {
                            let off = w * 1024 + med * 64 + k * 8;
                            table.apply(black_box(&input[off..off + 8]), &mut out);
                            black_box(&out);
                        }
                    }
                }
            }
        });
        measure("gf8_multiply_shift_reduce", medium_count, &mut || {
            for cols in &expanded {
                black_box(diagnostic_gf8_shift(black_box(cols)));
            }
        });
        measure("fused_ab", medium_count, &mut || {
            let mut out = [0; ELL];
            for (w, &n) in nmedium.iter().enumerate() {
                for med in 0..n {
                    shift_reduce_inner_ab(black_box(&a), black_box(&b), &table, w * 1024, med, &mut out);
                    black_box(&out);
                }
            }
        });
        measure("c_extract", medium_count, &mut || {
            let mut out = [0; ELL];
            for (w, &n) in nmedium.iter().enumerate() {
                for med in 0..n {
                    let off = w * 1024 + med * 64;
                    bit_transpose_64bytes(black_box(c[off..off + 64].try_into().unwrap()), &mut out);
                    black_box(&out);
                }
            }
        });
        measure("medium_convert_eq_lo", nmedium.iter().filter(|&&n| n > 0).count(), &mut || {
            let mut out = Convert::new();
            for w in 0..samples {
                if nmedium[w] == 0 {
                    continue;
                }
                out.accumulate(black_box(&ab_rows[w][..nmedium[w]]), black_box(&c_rows[w][..nmedium[w]]), black_box(weights[w]));
            }
            black_box(out.values());
        });
        measure("outer_reduce", windows.div_ceil(eq_lo.len()), &mut || {
            let mut out = [[F192::ZERO; ELL]; 2];
            for &hi in eq.high.iter().take(windows.div_ceil(eq_lo.len())) {
                let (partial_ab, partial_c) = black_box(&converted).values();
                for lane in 0..ELL {
                    out[0][lane] += black_box(hi) * black_box(partial_ab[lane]);
                    out[1][lane] += black_box(hi) * black_box(partial_c[lane]);
                }
            }
            black_box(out);
        });
        measure("c_extension", 192, &mut || {
            black_box(ntt_extend_vec(black_box(&oracle[1]), &table));
        });
    }

    // Independent scalar medium conversion and direct eq_lo*eq_hi weighting.
    // Reuses the already scalar-checked NTT table and the existing C extension,
    // but not WorkerState, Convert, process_one_x_hi or the fused AB kernel.
    fn diagnostic_round1_reference(
        packed: [&[u8]; 3],
        m: usize,
        r: &[F192],
        table: &InvNttTableByteSingleGf8,
        padding: &PaddingSpec,
    ) -> (Vec<F192>, Vec<F192>) {
        let tail = padding.tail(m, K_SKIP + N_INNER, K_SKIP + N_INNER, r);
        let windows = tail.map_or(1 << (m - K_SKIP - N_INNER), |t| t.head >> (K_SKIP + N_INNER));
        let (mask, counts) = build_b_med_counts(padding);
        let eq = SplitEq::with_high_vars(&r[N_INNER..], EQ_HIGH_VARS);
        let mut ab = vec![F192::ZERO; ELL];
        let mut c = vec![F192::ZERO; ELL];
        for w in 0..windows {
            let weight = eq.low[w % eq.low.len()] * eq.high[w / eq.low.len()] * d_inv();
            let mut medium_ab = [F192::ZERO; ELL];
            let mut medium_c = [F192::ZERO; ELL];
            for med in 0..counts[w & mask] as usize {
                let mut row_ab = [0; ELL];
                shift_reduce_inner_ab_scalar(packed[0], packed[1], table, w * 1024, med, &mut row_ab);
                let input = &packed[2][w * 1024 + med * 64..w * 1024 + med * 64 + 64];
                for lane in 0..ELL {
                    let byte = (0..8).fold(0, |acc, k| acc | (((input[k * 8 + lane / 8] >> (lane % 8)) & 1) << k));
                    medium_ab[lane] += gamma_powers()[med] * phi8_192(F8(row_ab[lane]));
                    medium_c[lane] += gamma_powers()[med] * phi8_192(F8(byte));
                }
            }
            for lane in 0..ELL {
                ab[lane] += weight * medium_ab[lane];
                c[lane] += weight * medium_c[lane];
            }
        }
        let mut c = ntt_extend_vec(&c, table);
        if let Some(tail) = tail {
            let (tail_ab, tail_c) = diagnostic_round1_reference(
                packed.map(|p| tail.group(p)), tail.group_log, &r[..tail.r_inner], table, &padding.without_tail(),
            );
            for lane in 0..ELL {
                ab[lane] += tail.weight * tail_ab[lane];
                c[lane] += tail.weight * tail_c[lane];
            }
        }
        (ab, c)
    }

    /// Same GF8 multiply/widen/shift/reduce arithmetic with already-expanded
    /// columns. The input traffic and register schedule differ from fusion.
    #[inline(never)]
    fn diagnostic_gf8_shift(columns: &[[[F8; ELL]; 8]; 2]) -> [u8; ELL] {
        let mut out = [0; ELL];
        #[cfg(target_arch = "aarch64")]
        {
            // SAFETY: NEON is baseline and each column contains 64 bytes.
            unsafe {
                let mut acc = [[vdupq_n_u16(0); 2]; 4];
                macro_rules! step {
                    ($k:literal) => {
                        for (h, [lo, hi]) in acc.iter_mut().enumerate() {
                            let a = vld1q_u8(columns[0][$k].as_ptr().cast::<u8>().add(16 * h));
                            let b = vld1q_u8(columns[1][$k].as_ptr().cast::<u8>().add(16 * h));
                            let y = gf8_mul_vec16(a, b);
                            *lo = veorq_u16(*lo, vshll_n_u8::<$k>(vget_low_u8(y)));
                            *hi = veorq_u16(*hi, vshll_n_u8::<$k>(vget_high_u8(y)));
                        }
                    };
                }
                step!(0); step!(1); step!(2); step!(3);
                step!(4); step!(5); step!(6); step!(7);
                for (h, [lo, hi]) in acc.into_iter().enumerate() {
                    vst1q_u8(out.as_mut_ptr().add(16 * h), primitives::field::gf2_8::neon::gf8_reduce_vec16(vreinterpretq_u8_u16(lo), vreinterpretq_u8_u16(hi)));
                }
            }
        }
        #[cfg(all(target_arch = "x86_64", target_feature = "gfni", target_feature = "avx512bw"))]
        {
            // SAFETY: features are enabled at compile time; all loads/stores
            // cover exactly one 64-byte column.
            unsafe {
                let (mut lo, mut hi) = (_mm512_setzero_si512(), _mm512_setzero_si512());
                let zero = _mm512_setzero_si512();
                for k in 0..8 {
                    let y = _mm512_gf2p8mul_epi8(
                        _mm512_loadu_si512(columns[0][k].as_ptr().cast()),
                        _mm512_loadu_si512(columns[1][k].as_ptr().cast()),
                    );
                    let shift = _mm_cvtsi32_si128(k as i32);
                    lo = _mm512_xor_si512(lo, _mm512_sll_epi16(_mm512_unpacklo_epi8(y, zero), shift));
                    hi = _mm512_xor_si512(hi, _mm512_sll_epi16(_mm512_unpackhi_epi8(y, zero), shift));
                }
                let mask = _mm512_set1_epi16(255);
                let fold = |p: __m512i| {
                    let h = _mm512_srli_epi16::<8>(p);
                    _mm512_xor_si512(_mm512_and_si512(p, mask), _mm512_xor_si512(
                        _mm512_xor_si512(h, _mm512_slli_epi16::<1>(h)),
                        _mm512_xor_si512(_mm512_slli_epi16::<3>(h), _mm512_slli_epi16::<4>(h))))
                };
                let reduce = |p| _mm512_and_si512(fold(fold(p)), mask);
                _mm512_storeu_si512(out.as_mut_ptr().cast(), _mm512_packus_epi16(reduce(lo), reduce(hi)));
            }
        }
        #[cfg(not(any(target_arch = "aarch64", all(target_arch = "x86_64", target_feature = "gfni", target_feature = "avx512bw"))))]
        {
            for lane in 0..ELL {
                let acc = (0..8).fold(0u16, |acc, k| acc ^ (((columns[0][k][lane] * columns[1][k][lane]).0 as u16) << k));
                out[lane] = gf8_reduce(acc);
            }
        }
        out
    }
