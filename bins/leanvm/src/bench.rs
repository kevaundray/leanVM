//! The guests tracked in CI (`.github/workflows/bench.yml`), reported on stdout as
//! Bencher Metric Format JSON: <https://bencher.dev/docs/reference/bencher-metric-format/>.

use leanvm::{Program, prove, verify};
use primitives::bench::{Plan, Timing};

struct Case {
    name: &'static str,
    elf: &'static [u8],
    input: [u64; 4],
    advice: Vec<u64>,
}

/// The bytes `0, 1, 2, ...` (mod 251) the hashing guests digest.
fn message(length: usize) -> Vec<u8> {
    (0..length).map(|i| (i % 251) as u8).collect()
}

fn cases() -> Vec<Case> {
    let preimage = {
        let message = message(20_000);
        let mut advice = vec![message.len() as u64];
        advice.extend(message.chunks(8).map(|chunk| {
            let mut word = [0u8; 8];
            word[..chunk.len()].copy_from_slice(chunk);
            u64::from_le_bytes(word)
        }));
        advice
    };
    vec![
        Case {
            name: "fibonacci-500000",
            elf: include_bytes!("../../../guests/elf/fibonacci.elf"),
            input: [500_000, 0, 0, 0],
            advice: vec![],
        },
        Case {
            name: "hash-50000",
            elf: include_bytes!("../../../guests/elf/hash.elf"),
            input: [50_000, 0, 0, 0],
            advice: vec![],
        },
        Case {
            name: "blake2s-5000",
            elf: include_bytes!("../../../guests/elf/blake2s.elf"),
            input: [5_000, 0, 0, 0],
            advice: vec![],
        },
        Case {
            name: "preimage-20000",
            elf: include_bytes!("../../../guests/elf/preimage.elf"),
            input: [0; 4],
            advice: preimage,
        },
        Case {
            name: "numbers",
            elf: include_bytes!("../../../guests/elf/numbers.elf"),
            input: [0x1234_5678_9abc_def1, 65_537, 0xffff_ffff_0000_0001, 0],
            advice: vec![],
        },
    ]
}

/// One measure of one benchmark: a value, and for a timing the fastest and slowest pass.
struct Metric {
    value: f64,
    bounds: Option<(f64, f64)>,
}

impl Metric {
    fn exact(value: usize) -> Self {
        Self {
            value: value as f64,
            bounds: None,
        }
    }

    /// Bencher's built-in `latency` measure is in nanoseconds.
    fn nanoseconds(timing: &Timing) -> Self {
        let ns = |secs: f64| (secs * 1e9).round();
        let samples = timing.samples();
        Self {
            value: ns(timing.mean()),
            bounds: Some((
                ns(samples.iter().copied().fold(f64::INFINITY, f64::min)),
                ns(samples.iter().copied().fold(0.0, f64::max)),
            )),
        }
    }
}

/// Every case's metrics: `cycles` (instructions executed) and `proven-rows` (the
/// tables' heights once padded to powers of two) always; with a proof, also the
/// committed witness size, the proof's size in bytes, and the proving time.
pub fn run_bench(cycles_only: bool, log_inv_rate: usize, plan: Plan) {
    let mut report = Vec::new();
    for case in cases() {
        let program = Program::from_elf(case.elf).expect("a checked-in guest");
        let metrics = if cycles_only {
            let run = program
                .execute(case.input, &case.advice)
                .unwrap_or_else(|trap| panic!("{}: {trap}", case.name));
            vec![
                ("cycles", Metric::exact(run.base_counts.iter().sum())),
                ("proven-rows", Metric::exact(run.cycles)),
            ]
        } else {
            eprintln!("{}", case.name);
            let ((proof, output, stats), time) = plan.warm_then_measure(|_| {
                prove(&program, case.input, &case.advice, log_inv_rate)
                    .unwrap_or_else(|trap| panic!("{}: {trap}", case.name))
            });
            verify(&program, &case.input, &output, &proof).expect("an honest proof verifies");
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
    println!("{}", to_json(&report));
}

fn to_json(report: &[(&str, Vec<(&str, Metric)>)]) -> String {
    let benchmarks: Vec<String> = report
        .iter()
        .map(|(name, metrics)| {
            let measures: Vec<String> = metrics
                .iter()
                .map(|(measure, m)| match m.bounds {
                    None => format!("\"{measure}\": {{\"value\": {}}}", m.value),
                    Some((lo, hi)) => format!(
                        "\"{measure}\": {{\"value\": {}, \"lower_value\": {lo}, \"upper_value\": {hi}}}",
                        m.value
                    ),
                })
                .collect();
            format!("  \"{name}\": {{{}}}", measures.join(", "))
        })
        .collect();
    format!("{{\n{}\n}}", benchmarks.join(",\n"))
}
