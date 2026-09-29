//! The programs tracked in CI (`.github/workflows/bench.yml`), reported on stdout as
//! Bencher Metric Format JSON.

use bench::{Metric, Plan, bencher_json};
use leanvm::{Program, prove, verify};

use crate::guest::refuse;
use crate::workload::Workload;
use crate::{da, fibonacci, signatures};

struct Case {
    /// The benchmark's Bencher history: renaming it, or changing its input, starts a new one.
    name: String,
    program: Program,
    input: [u64; 4],
    advice: Vec<u64>,
    /// The native reference's output, where there is one.
    expected: Option<[u64; 4]>,
}

impl Case {
    fn workload(name: &str, workload: Workload) -> Self {
        Self {
            name: name.to_string(),
            program: workload.program(),
            input: workload.input,
            advice: workload.advice,
            expected: Some(workload.expected),
        }
    }
}

/// The README's benchmarks, at its sizes.
fn cases() -> Vec<Case> {
    let (fibonacci, fibonacci_output) = fibonacci::fibonacci_program(2_000_000);
    vec![
        Case {
            name: "fibonacci-asm-2000000".into(),
            program: fibonacci,
            input: [0; 4],
            advice: vec![],
            expected: Some(fibonacci_output),
        },
        Case {
            name: "hash-50000".into(),
            program: Program::from_elf(include_bytes!("../../../guests/elf/hash.elf")).expect("a checked-in guest"),
            input: [50_000, 0, 0, 0],
            advice: vec![],
            expected: None,
        },
        Case::workload("leanxmss-400", signatures::leanxmss(400)),
        Case::workload("leansphincs-104", signatures::leansphincs(104)),
        Case::workload("leanda-1", da::leanda(1)),
    ]
}

/// Every case's metrics: `cycles` (the program's own instructions), `proven-rows` (the
/// tables' heights once padded to powers of two) and `committed` (the witness words)
/// always; with a proof, also the proof's size in bytes and the proving time.
pub fn run_bench(cycles_only: bool, log_inv_rate: usize, plan: Plan) {
    let mut report = Vec::new();
    for case in cases() {
        let metrics = if cycles_only {
            let stats = leanvm_core::cpu::measure(&case.program, case.input, &case.advice)
                .unwrap_or_else(|trap| refuse(format_args!("{}: {trap}", case.name)));
            vec![
                ("cycles", Metric::exact(stats.base_counts.iter().sum())),
                ("proven-rows", Metric::exact(stats.cycles)),
                ("committed", Metric::exact(stats.committed)),
            ]
        } else {
            eprintln!("{}", case.name);
            let ((proof, output, stats), time) = plan.warm_then_measure(|_| {
                prove(&case.program, case.input, &case.advice, log_inv_rate)
                    .unwrap_or_else(|trap| refuse(format_args!("{}: {trap}", case.name)))
            });
            if let Some(expected) = case.expected {
                assert_eq!(output, expected, "{}: the output is the native reference's", case.name);
            }
            verify(&case.program, &case.input, &output, &proof).expect("an honest proof verifies");
            let proof_bytes = bincode::serialized_size(&proof).expect("proof is serializable");
            vec![
                ("cycles", Metric::exact(stats.base_counts.iter().sum())),
                ("proven-rows", Metric::exact(stats.cycles)),
                ("committed", Metric::exact(stats.committed)),
                ("proof-size", Metric::exact(proof_bytes as usize)),
                ("latency", Metric::nanoseconds(&time)),
            ]
        };
        report.push((case.name, metrics));
    }
    println!("{}", bencher_json(&report));
}
