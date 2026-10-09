//! Fixed shielded workloads, timed by mobench without a nested benchmark harness.

use leanvm::aggregate::{Leaf, LeafShape, Tree, TreeShape};
use leanvm::{Output, Program, ProvenRun, Prover, Rate};
use mobench_sdk::registry::BenchFunction;
use mobench_sdk::timing::{BenchReport, BenchSpec, TimingError};
use std::cell::RefCell;
use std::fmt::Display;
use std::hint::black_box;
use std::num::NonZeroUsize;
use std::sync::OnceLock;

pub const SPENDS_PER_LEAF: usize = 2;
pub const LEAF_LOG_INV_RATE: u8 = 2;
pub const AGGREGATION_LEAVES: usize = 2;
pub const AGGREGATION_LOG_INV_RATE: u8 = 1;
pub const DEFAULT_WARMUP: u32 = 1;
pub const DEFAULT_ITERATIONS: u32 = 3;
pub const PROVE_BENCHMARK: &str = "leanvm_mobile_bench::shielded_prove";
pub const AGGREGATE_BENCHMARK: &str = "leanvm_mobile_bench::shielded_aggregate";

static AVAILABLE_THREADS: OnceLock<std::io::Result<NonZeroUsize>> = OnceLock::new();

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
        let available = AVAILABLE_THREADS
            .get_or_init(std::thread::available_parallelism)
            .as_ref()
            .map_err(execution_error)?;
        parallel::init_with_threads(*available).map_err(|topology| {
            TimingError::Execution(format!(
                "benchmark requires {available} available threads, got {topology:?}"
            ))
        })?;
        mobench_sdk::record_run_u64("available_parallelism", available.get() as u64);
        mobench_sdk::record_run_u64("threads", parallel::num_threads() as u64);
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

fn record_workload() {
    mobench_sdk::record_run_u64("spends_per_leaf", SPENDS_PER_LEAF as u64);
    mobench_sdk::record_run_u64("leaf_log_inv_rate", u64::from(LEAF_LOG_INV_RATE));
}

/// Time one shielded proof per invocation; verify and drop every retained result in teardown.
pub fn shielded_prove(spec: BenchSpec) -> Result<BenchReport, TimingError> {
    let spec = BenchSpec::new(spec.name, spec.iterations, spec.warmup)?;
    let fixture = Shielded::new()?;
    let count = spec.warmup as usize + spec.iterations as usize;
    record_workload();
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

/// Time 2-to-1 aggregation of two 2-spend leaves; prepare leaves once and verify roots in teardown.
pub fn shielded_aggregate(spec: BenchSpec) -> Result<BenchReport, TimingError> {
    let spec = BenchSpec::new(spec.name, spec.iterations, spec.warmup)?;
    let fixture = Shielded::new()?;
    let stats = fixture.program.measure(&fixture.advice).map_err(execution_error)?;
    let runs = [fixture.prove()?, fixture.prove()?];
    for run in &runs {
        fixture.verify(run)?;
    }
    mobench_sdk::record_run_u64("verified_leaves", runs.len() as u64);
    let tree = Tree::new(
        &fixture.program,
        TreeShape {
            leaf: LeafShape::measured(&stats, fixture.prover.rate()),
            arity_0: AGGREGATION_LEAVES,
            arity: AGGREGATION_LEAVES,
            rate: Rate::new(AGGREGATION_LOG_INV_RATE).map_err(execution_error)?,
        },
    )
    .map_err(execution_error)?;
    let leaves = runs.each_ref().map(|run| Leaf::new(&run.proof, run.output));
    let outputs = [fixture.expected; AGGREGATION_LEAVES];
    let count = spec.warmup as usize + spec.iterations as usize;
    record_workload();
    mobench_sdk::record_run_u64("aggregation_leaves", leaves.len() as u64);
    mobench_sdk::record_run_u64("aggregation_log_inv_rate", u64::from(AGGREGATION_LOG_INV_RATE));
    let mut verified: Result<(), TimingError> = Ok(());
    let report = mobench_sdk::timing::run_closure_with_setup_teardown(
        spec,
        || RefCell::new(Vec::with_capacity(count)),
        |proofs| {
            let root = tree.prove_first(&leaves).map_err(execution_error)?;
            proofs.borrow_mut().push(black_box(root));
            Ok(())
        },
        |proofs| {
            verified = (|| {
                let proofs = proofs.into_inner();
                let produced = proofs.len();
                for root in proofs {
                    tree.verify(&root, &outputs).map_err(execution_error)?;
                    black_box(root);
                }
                mobench_sdk::record_run_u64("verified_proofs", produced as u64);
                Ok(())
            })();
        },
    );
    verified?;
    report
}
