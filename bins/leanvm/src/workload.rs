//! A guest workload, proven and verified the way the benchmarks report it.

use bench::Plan;
use leanvm::{Program, prove, verify};
use primitives::{pretty_f64, pretty_integer};

use crate::guest::{INPUT, refuse};

/// One run of a guest (`programs/`): what it is given and what it must output.
pub struct Workload {
    /// What the report calls the run.
    pub title: String,
    /// The guest's ELF file.
    pub elf: &'static [u8],
    /// What the guest checks, which the statement does not cover.
    pub advice: Vec<u64>,
    /// The output the native reference computed, so a proof of anything else fails.
    pub expected: [u64; 4],
    /// How many items the run covers.
    pub items: usize,
    /// What one item is called.
    pub item: &'static str,
}

impl Workload {
    /// The guest, loaded.
    pub fn program(&self) -> Program {
        Program::from_elf(self.elf).expect("a guest's ELF file")
    }
}

/// The programs with a host (`programs/<name>/host`), which builds their advice and output.
#[derive(Clone, Copy, clap::ValueEnum)]
pub enum Hosted {
    /// Verify leanXMSS signatures, one key each.
    Leanxmss,
    /// Verify leanSPHINCS signatures, one key each.
    Leansphincs,
    /// Check leanDA blobs of 128 KiB and compute their commitment.
    Leanda,
}

impl Hosted {
    /// The items a run covers when none is named: a quick run, not the benchmark's.
    pub fn default_items(self) -> usize {
        match self {
            Self::Leanxmss => 64,
            Self::Leansphincs => 16,
            Self::Leanda => 1,
        }
    }

    /// A run over `n` items: signatures, or blobs.
    pub fn workload(self, n: usize) -> Workload {
        let (title, elf, run, item) = match self {
            Self::Leanxmss => {
                let run = leanxmss_host::batch(n);
                (
                    format!("leanXMSS verification, {n} signatures"),
                    leanxmss_host::ELF,
                    (run.advice, run.expected),
                    "signature",
                )
            }
            Self::Leansphincs => {
                let run = leansphincs_host::batch(n);
                (
                    format!("leanSPHINCS verification, {n} signatures"),
                    leansphincs_host::ELF,
                    (run.advice, run.expected),
                    "signature",
                )
            }
            Self::Leanda => {
                let run = leanda_host::blobs(n);
                (
                    format!("leanDA check, {n} blobs of 128 KiB"),
                    leanda_host::ELF,
                    (run.advice, run.expected),
                    "blob",
                )
            }
        };
        let (advice, expected) = run;
        Workload {
            title,
            elf,
            advice,
            expected,
            items: n,
            item,
        }
    }
}

/// Prove and verify a workload, and print the report.
///
/// Proving runs one discarded warmup pass, then `plan.repeat` measured passes.
pub fn run(workload: &Workload, log_inv_rate: usize, plan: Plan) {
    let program = workload.program();
    // More items than the guest's advice region holds is the user's mistake, not a bug.
    let region = 1usize << program.rv.log_advice;
    if workload.advice.len() > region {
        refuse(format_args!(
            "{} {}s take {} advice words, and the guest's region holds {region}",
            workload.items,
            workload.item,
            workload.advice.len()
        ));
    }
    // Only the final measured pass is traced.
    let (result, prove_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        prove(&program, INPUT, &workload.advice, log_inv_rate)
    });
    // A run too long for one proof has none: continuations are not implemented.
    let (proof, output, stats) = result.unwrap_or_else(|trap| refuse(format_args!("the run has no proof: {trap}")));
    assert_eq!(
        output, workload.expected,
        "the guest's output is the native reference's"
    );
    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        verify(&program, &INPUT, &output, &proof).expect("the proof verifies")
    });

    // The proven rows include padding: the guest's own cycles are the per-table base counts.
    let cycles: usize = stats.base_counts.iter().sum();
    println!("{}", workload.title);
    println!(
        "  cycles (RISC-V)             : {}   {} per {}",
        pretty_integer(cycles),
        pretty_f64(cycles as f64 / workload.items as f64),
        workload.item
    );
    println!("  proven rows                 : {}", pretty_integer(stats.cycles));
    // Rows per table, then the committed witness: what the prover pays for.
    println!("    details                   : {}", stats.details());
    let proof_bytes = bincode::serialized_size(&proof).expect("proof is serializable");
    println!("  proof size                  : {:.1} KiB", proof_bytes as f64 / 1024.0);
    println!(
        "  proving                     : {} s{}   {} {}s/s      peak memory {} GiB",
        pretty_f64(prove_time.mean()),
        prove_time.spread(),
        pretty_f64(workload.items as f64 / prove_time.mean()),
        workload.item,
        pretty_f64(bench::peak_rss_bytes() as f64 / (1u64 << 30) as f64)
    );
    println!(
        "  verifying                   : {} ms",
        pretty_f64(verify_time.mean() * 1000.0)
    );
}

#[cfg(test)]
mod tests {
    #[test]
    fn the_signature_workloads_prove() {
        // End to end: proven, verified, and the output the native digest.
        for workload in [
            super::Hosted::Leanxmss.workload(2),
            super::Hosted::Leansphincs.workload(1),
        ] {
            super::run(&workload, leanvm_core::pcs::TEST_LOG_INV_RATE, bench::Plan::default());
        }
    }
}
