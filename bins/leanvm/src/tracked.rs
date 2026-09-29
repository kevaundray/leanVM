//! The programs tracked in CI (`.github/workflows/bench.yml`), reported as Bencher
//! Metric Format JSON or, counted without a proof, as a markdown table.

use bench::{Metric, Plan, bencher_json};
use leanvm::{Program, Stats, prove, verify};
use primitives::pretty_integer;

use crate::guest::refuse;
use crate::workload::Workload;
use crate::{da, fibonacci, signatures};

struct Case {
    /// The benchmark's Bencher history: renaming it, or changing its input, starts a new one.
    name: &'static str,
    /// What the markdown table calls it.
    title: String,
    program: Program,
    input: [u64; 4],
    advice: Vec<u64>,
    /// The native reference's output, where there is one.
    expected: Option<[u64; 4]>,
    items: usize,
    item: &'static str,
}

impl Case {
    fn workload(name: &'static str, workload: Workload) -> Self {
        Self {
            name,
            program: workload.program(),
            title: workload.title,
            input: workload.input,
            advice: workload.advice,
            expected: Some(workload.expected),
            items: workload.items,
            item: workload.item,
        }
    }

    /// The run's exact counts, without a proof.
    fn measure(&self) -> Stats {
        leanvm_core::cpu::measure(&self.program, self.input, &self.advice)
            .unwrap_or_else(|trap| refuse(format_args!("{}: {trap}", self.name)))
    }
}

/// The README's benchmarks, at its sizes.
fn cases() -> Vec<Case> {
    const FIBONACCI: usize = 2_000_000;
    const HASHED: usize = 50_000;
    let (fibonacci, fibonacci_output) = fibonacci::fibonacci_program(FIBONACCI);
    vec![
        Case {
            name: "fibonacci-asm-2000000",
            title: format!("Fibonacci modulo 2^64, {} steps", pretty_integer(FIBONACCI)),
            program: fibonacci,
            input: [0; 4],
            advice: vec![],
            expected: Some(fibonacci_output),
            items: FIBONACCI,
            item: "step",
        },
        Case {
            name: "hash-50000",
            title: format!("BLAKE2s of {} bytes", pretty_integer(HASHED)),
            program: Program::from_elf(include_bytes!("../../../guests/elf/hash.elf")).expect("a checked-in guest"),
            input: [HASHED as u64, 0, 0, 0],
            advice: vec![],
            expected: None,
            items: HASHED,
            item: "byte",
        },
        Case::workload("leanxmss-400", signatures::leanxmss(400)),
        Case::workload("leansphincs-104", signatures::leansphincs(104)),
        Case::workload("leanda-1", da::leanda(1)),
    ]
}

/// Report every case: with `cycles_only`, the exact counts without a proof, as JSON or
/// with `markdown` as a table; otherwise proven, verified and timed, as JSON.
pub fn run(cycles_only: bool, markdown: bool, log_inv_rate: usize, plan: Plan) {
    let cases = cases();
    if markdown {
        return table(&cases);
    }
    let report: Vec<_> = cases
        .iter()
        .map(|case| {
            let metrics = if cycles_only {
                counts(&case.measure())
            } else {
                proven(case, log_inv_rate, plan)
            };
            (case.name.to_string(), metrics)
        })
        .collect();
    println!("{}", bencher_json(&report));
}

/// `cycles` (the program's own instructions), `proven-rows` (the tables' heights once
/// padded to powers of two) and `committed` (the witness words): exact, the same on every machine.
fn counts(stats: &Stats) -> Vec<(&'static str, Metric)> {
    vec![
        ("cycles", Metric::exact(stats.base_counts.iter().sum())),
        ("proven-rows", Metric::exact(stats.cycles)),
        ("committed", Metric::exact(stats.committed)),
    ]
}

/// The counts, then the proof's size in bytes and the proving time.
fn proven(case: &Case, log_inv_rate: usize, plan: Plan) -> Vec<(&'static str, Metric)> {
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
    let mut metrics = counts(&stats);
    metrics.push(("proof-size", Metric::exact(proof_bytes as usize)));
    metrics.push(("latency", Metric::nanoseconds(&time)));
    metrics
}

/// The counts as a markdown table, with the rows per table: what CI puts in each run's summary.
fn table(cases: &[Case]) {
    println!("| program | RISC-V cycles | per item | committed words | tables |");
    println!("|---|---:|---:|---:|---|");
    for case in cases {
        let stats = case.measure();
        let cycles: usize = stats.base_counts.iter().sum();
        println!(
            "| {} | {} | {} / {} | 2^{:.2} | {} |",
            case.title,
            pretty_integer(cycles),
            pretty_integer(cycles / case.items),
            case.item,
            (stats.committed as f64).log2(),
            stats.details()
        );
    }
}
