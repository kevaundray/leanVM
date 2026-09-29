//! Benchmark CLI.

use clap::{Parser, Subcommand};

mod fibonacci;
mod guest;
mod tracked;
mod workload;

#[derive(Parser)]
struct Cli {
    /// WHIR inverse-rate logarithm (1 through 4).
    #[arg(
        long,
        global = true,
        default_value_t = 1,
        value_parser = clap::builder::RangedU64ValueParser::<usize>::new().range(1..=4)
    )]
    log_inv_rate: usize,

    /// Enable hierarchical timing traces. Use RUST_LOG to adjust verbosity.
    #[arg(long, global = true)]
    tracing: bool,

    /// Measured proving passes after warmup.
    #[arg(
        long,
        global = true,
        default_value_t = 1,
        value_parser = clap::builder::RangedU64ValueParser::<usize>::new().range(1..)
    )]
    repeat: usize,

    /// Idle seconds before each measured pass.
    #[arg(long, global = true, default_value_t = 2)]
    cooldown: u64,

    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Prove and verify Fibonacci modulo 2^64 in hand-written RISC-V, the README's throughput figure.
    ///
    /// One `add` per step, so every row is ALU. The Rust guest of the same function is
    /// `guest programs/fibonacci/fibonacci.elf --advice N`.
    Fibonacci {
        /// Number of recurrence steps.
        #[arg(long, default_value = "2000000")]
        n: usize,
    },
    /// Prove and verify any guest ELF on advice given by hand (see `programs/`).
    Guest {
        /// The guest's ELF executable.
        elf: std::path::PathBuf,
        /// The advice: the words the guest reads, decimal or 0x-prefixed. The statement does not cover it.
        #[arg(long, value_delimiter = ',', value_parser = guest::parse_word)]
        advice: Vec<u64>,
    },
    /// Prove and verify a program whose host builds its advice (`programs/<name>/host`).
    Run {
        program: workload::Hosted,
        /// Items: signatures for leanxmss and leansphincs, blobs for leanda. A quick run by default.
        #[arg(long, value_parser = clap::builder::RangedU64ValueParser::<usize>::new().range(1..))]
        n: Option<usize>,
    },
    /// Prove the benchmarks CI tracks and print them as Bencher Metric Format JSON.
    ///
    /// The list is `bins/leanvm/src/tracked.rs`: Fibonacci, hash, leanXMSS, leanSPHINCS and leanDA,
    /// at the README's sizes.
    Bench {
        /// Measure without proving: the exact counts only, no proof size or time.
        #[arg(long)]
        cycles_only: bool,
        /// Print the counts as a markdown table rather than JSON.
        #[arg(long, requires = "cycles_only")]
        markdown: bool,
    },
}

fn main() {
    let cli = Cli::parse();
    leanvm_core::init_prover();
    let plan = bench::Plan::new(cli.repeat, cli.cooldown);
    if cli.tracing {
        bench::init_tracing();
    }
    match cli.command {
        Command::Fibonacci { n } => fibonacci::run_fibonacci(n, cli.log_inv_rate, plan),
        Command::Guest { elf, advice } => guest::run_guest(&elf, &advice, cli.log_inv_rate, plan),
        Command::Run { program, n } => {
            let n = n.unwrap_or(program.default_items());
            workload::run(&program.workload(n), cli.log_inv_rate, plan)
        }
        Command::Bench { cycles_only, markdown } => tracked::run(cycles_only, markdown, cli.log_inv_rate, plan),
    }
    if std::env::var_os("ZK_ALLOC_STATS").is_some() {
        eprintln!("{}", zk_alloc::stats());
    }
}
