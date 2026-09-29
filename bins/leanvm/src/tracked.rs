//! The programs tracked in CI (`.github/workflows/bench.yml`): the guests, and the
//! hand-written Fibonacci the README quotes, reported on stdout as Bencher Metric Format JSON.

use bench::{Metric, Plan, bencher_json};
use leanvm::{Program, prove, verify};

struct Case {
    name: &'static str,
    program: Program,
    input: [u64; 4],
    advice: Vec<u64>,
}

/// The bytes `0, 1, 2, ...` (mod 251) the hashing guests digest.
fn message(length: usize) -> Vec<u8> {
    (0..length).map(|i| (i % 251) as u8).collect()
}

fn guest(elf: &[u8]) -> Program {
    Program::from_elf(elf).expect("a checked-in guest")
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
            name: "fibonacci-asm-2000000",
            program: crate::fibonacci::fibonacci_program(2_000_000).0,
            input: [0; 4],
            advice: vec![],
        },
        Case {
            name: "fibonacci-guest-500000",
            program: guest(include_bytes!("../../../guests/elf/fibonacci.elf")),
            input: [500_000, 0, 0, 0],
            advice: vec![],
        },
        Case {
            name: "hash-50000",
            program: guest(include_bytes!("../../../guests/elf/hash.elf")),
            input: [50_000, 0, 0, 0],
            advice: vec![],
        },
        Case {
            name: "blake2s-5000",
            program: guest(include_bytes!("../../../guests/elf/blake2s.elf")),
            input: [5_000, 0, 0, 0],
            advice: vec![],
        },
        Case {
            name: "preimage-20000",
            program: guest(include_bytes!("../../../guests/elf/preimage.elf")),
            input: [0; 4],
            advice: preimage,
        },
        Case {
            name: "numbers",
            program: guest(include_bytes!("../../../guests/elf/numbers.elf")),
            input: [0x1234_5678_9abc_def1, 65_537, 0xffff_ffff_0000_0001, 0],
            advice: vec![],
        },
    ]
}

/// Every case's metrics: `cycles` (instructions executed) and `proven-rows` (the
/// tables' heights once padded to powers of two) always; with a proof, also the
/// committed witness size, the proof's size in bytes, and the proving time.
pub fn run_bench(cycles_only: bool, log_inv_rate: usize, plan: Plan) {
    let mut report = Vec::new();
    for case in cases() {
        let metrics = if cycles_only {
            let run = case
                .program
                .execute(case.input, &case.advice)
                .unwrap_or_else(|trap| panic!("{}: {trap}", case.name));
            vec![
                ("cycles", Metric::exact(run.base_counts.iter().sum())),
                ("proven-rows", Metric::exact(run.cycles)),
            ]
        } else {
            eprintln!("{}", case.name);
            let ((proof, output, stats), time) = plan.warm_then_measure(|_| {
                prove(&case.program, case.input, &case.advice, log_inv_rate)
                    .unwrap_or_else(|trap| panic!("{}: {trap}", case.name))
            });
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
        report.push((case.name.to_string(), metrics));
    }
    println!("{}", bencher_json(&report));
}
