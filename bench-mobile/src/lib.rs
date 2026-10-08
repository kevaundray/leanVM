//! Fixed shielded workloads, timed by mobench without a nested benchmark harness.

use leanvm::aggregate::{Leaf, LeafShape, Tree, TreeProof, TreeShape};
use leanvm::{Output, Program, ProvenRun, Prover, Rate};
use mobench_sdk::registry::BenchFunction;
use mobench_sdk::timing::{BenchReport, BenchSpec, TimingError};
use std::cell::RefCell;
use std::fmt::Display;
use std::hint::black_box;
use std::num::NonZeroUsize;

pub const THREADS: usize = 1;
pub const SPENDS_PER_LEAF: usize = 1;
pub const AGGREGATION_LEAVES: usize = 2;
pub const LEAF_LOG_INV_RATE: u8 = 2;
pub const TREE_LOG_INV_RATE: u8 = 1;
pub const DEFAULT_WARMUP: u32 = 1;
pub const DEFAULT_ITERATIONS: u32 = 3;
pub const PROVE_BENCHMARK: &str = "leanvm_mobile_bench::shielded_prove";
pub const AGGREGATE_BENCHMARK: &str = "leanvm_mobile_bench::shielded_aggregate";

inventory::submit! {
    BenchFunction { name: PROVE_BENCHMARK, runner: shielded_prove }
}

inventory::submit! {
    BenchFunction { name: AGGREGATE_BENCHMARK, runner: shielded_aggregate }
}

mobench_sdk::export_native_c_abi!();

struct Shielded {
    program: Program,
    advice: Vec<u64>,
    expected: Output,
    prover: Prover,
}

impl Shielded {
    fn new() -> Result<Self, TimingError> {
        parallel::init_with_threads(NonZeroUsize::new(THREADS).expect("positive thread count")).map_err(
            |topology| TimingError::Execution(format!("benchmark requires {THREADS} thread, got {topology:?}")),
        )?;
        let run = shielded_host::spends(SPENDS_PER_LEAF);
        Ok(Self {
            program: Program::from_elf(shielded_host::ELF).map_err(execution_error)?,
            advice: run.advice,
            expected: Output::new(run.expected),
            prover: Prover::new(Rate::new(LEAF_LOG_INV_RATE).map_err(execution_error)?),
        })
    }

    fn prove(&self) -> Result<ProvenRun, TimingError> {
        self.prover.prove(&self.program, &self.advice).map_err(execution_error)
    }

    fn verify(&self, run: &ProvenRun) -> Result<(), TimingError> {
        if run.output != self.expected {
            return Err(TimingError::Execution(format!(
                "shielded output {} differs from native reference {}",
                run.output, self.expected
            )));
        }
        self.program.verify(self.expected, &run.proof).map_err(execution_error)
    }
}

fn execution_error(error: impl Display) -> TimingError {
    TimingError::Execution(error.to_string())
}

fn record_workload(leaves: usize) {
    mobench_sdk::record_run_u64("threads", THREADS as u64);
    mobench_sdk::record_run_u64("spends_per_leaf", SPENDS_PER_LEAF as u64);
    mobench_sdk::record_run_u64("aggregation_leaves", leaves as u64);
    mobench_sdk::record_run_u64("leaf_log_inv_rate", u64::from(LEAF_LOG_INV_RATE));
    mobench_sdk::record_run_u64("tree_log_inv_rate", u64::from(TREE_LOG_INV_RATE));
}

/// Time one shielded proof per invocation; verify and drop every retained result in teardown.
pub fn shielded_prove(spec: BenchSpec) -> Result<BenchReport, TimingError> {
    let spec = BenchSpec::new(spec.name, spec.iterations, spec.warmup)?;
    let fixture = Shielded::new()?;
    let count = spec.warmup as usize + spec.iterations as usize;
    record_workload(0);
    let mut verified: Result<(), TimingError> = Ok(());
    let report = mobench_sdk::timing::run_closure_with_setup_teardown(
        spec,
        || RefCell::new(Vec::with_capacity(count)),
        |proofs| {
            let run = fixture.prove()?;
            proofs.borrow_mut().push(black_box(run));
            Ok(())
        },
        |proofs| {
            verified = (|| {
                let proofs = proofs.into_inner();
                let produced = proofs.len();
                for run in proofs {
                    fixture.verify(&run)?;
                    black_box(run);
                }
                mobench_sdk::record_run_u64("verified_proofs", produced as u64);
                Ok(())
            })();
        },
    );
    verified?;
    report
}

/// Time aggregation of two pre-proven copies of the one-spend fixture, excluding tree setup and root verification.
pub fn shielded_aggregate(spec: BenchSpec) -> Result<BenchReport, TimingError> {
    let spec = BenchSpec::new(spec.name, spec.iterations, spec.warmup)?;
    let fixture = Shielded::new()?;
    let runs = (0..AGGREGATION_LEAVES)
        .map(|_| {
            let run = fixture.prove()?;
            fixture.verify(&run)?;
            Ok(run)
        })
        .collect::<Result<Vec<_>, TimingError>>()?;
    let tree = Tree::new(
        &fixture.program,
        TreeShape {
            leaf: LeafShape::of(&runs[0].proof).map_err(execution_error)?,
            arity_0: AGGREGATION_LEAVES,
            arity: 2,
            rate: Rate::new(TREE_LOG_INV_RATE).map_err(execution_error)?,
        },
    )
    .map_err(execution_error)?;
    let leaves: Vec<Leaf<'_>> = runs.iter().map(Leaf::from).collect();
    let expected = [fixture.expected; AGGREGATION_LEAVES];
    let count = spec.warmup as usize + spec.iterations as usize;
    record_workload(AGGREGATION_LEAVES);
    mobench_sdk::record_run_u64("verified_setup_leaves", runs.len() as u64);
    let mut verified: Result<(), TimingError> = Ok(());
    let report = mobench_sdk::timing::run_closure_with_setup_teardown(
        spec,
        || RefCell::new(Vec::<TreeProof>::with_capacity(count)),
        |proofs| {
            let proof = tree.prove(&leaves).map_err(execution_error)?;
            proofs.borrow_mut().push(black_box(proof));
            Ok(())
        },
        |proofs| {
            verified = (|| {
                let proofs = proofs.into_inner();
                let produced = proofs.len();
                for proof in proofs {
                    tree.verify(&proof, &expected).map_err(execution_error)?;
                    black_box(proof);
                }
                mobench_sdk::record_run_u64("verified_proofs", produced as u64);
                Ok(())
            })();
        },
    );
    verified?;
    report
}
