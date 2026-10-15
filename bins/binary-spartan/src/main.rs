//! `binary-spartan prove <circuit.r1cs> <witness.bin> [--signers <signers.json>] [--spark] [--self-check] [--repeat N]
//! [--cooldown S] [--tracing]`
//!
//! Loads a Clean block R1CS and a batch witness, checks satisfaction, proves and verifies, and prints the shape,
//! the proof size and the prove and verify times (one warmup, then `--repeat` measured passes). `--tracing` prints
//! the final proving pass's span tree. A linked block's statement is its boundary: the batch's own, or with
//! `--signers` the XMSS block's for that signer set (checked canonical, its digest in the last instance's `out`
//! registers, every `in` register of instance 0 zero).
//!
//! `binary-spartan gen-xmss --groups 2,3 --out <dir> [--tamper]` writes deterministic XMSS signatures for the
//! circuit's witness generator (`inputs.json`) and their signer set (`signers.json`).

#[global_allocator]
static ALLOCATOR: bench::Jemalloc = bench::Jemalloc;

mod signers;

use bench::{Plan, Timing};
use binary_spartan::block::BlockR1cs;
use binary_spartan::format::{R1csFile, WitnessFile};
use binary_spartan::proof::{self, Boundary, Mode, Proof};
use binary_spartan::spark;
use signers::SignerSet;
use std::process::ExitCode;
use std::time::Instant;

const USAGE: &str = "usage: binary-spartan prove <circuit.r1cs> <witness.bin> [--signers <signers.json>] [--spark] \
                     [--self-check] [--repeat N] [--cooldown S] [--tracing]\n       \
                     binary-spartan gen-xmss --groups <n,n,...> --out <dir> [--tamper]";

struct ProveArgs {
    circuit: String,
    witness: String,
    signers: Option<String>,
    spark: bool,
    self_check: bool,
    repeat: usize,
    cooldown: u64,
    tracing: bool,
}

struct GenArgs {
    groups: Vec<usize>,
    out: String,
    tamper: bool,
}

enum Command {
    Prove(ProveArgs),
    GenXmss(GenArgs),
}

fn parse_args() -> Result<Command, String> {
    let mut args = std::env::args().skip(1);
    match args.next().as_deref() {
        Some("prove") => parse_prove(args).map(Command::Prove),
        Some("gen-xmss") => parse_gen(args).map(Command::GenXmss),
        _ => Err(USAGE.into()),
    }
}

fn parse_prove(mut args: impl Iterator<Item = String>) -> Result<ProveArgs, String> {
    let mut paths = Vec::new();
    let (mut spark, mut self_check, mut repeat, mut cooldown, mut tracing) = (false, false, 1usize, 2u64, false);
    let mut signers = None;
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--spark" => spark = true,
            "--self-check" => self_check = true,
            "--tracing" => tracing = true,
            "--signers" => signers = Some(args.next().ok_or("--signers takes a path")?),
            "--repeat" => {
                repeat = args
                    .next()
                    .and_then(|n| n.parse().ok())
                    .filter(|&n| n > 0)
                    .ok_or("--repeat takes a positive integer")?;
            }
            "--cooldown" => {
                cooldown = args
                    .next()
                    .and_then(|n| n.parse().ok())
                    .ok_or("--cooldown takes a number of seconds")?;
            }
            _ if arg.starts_with("--") => return Err(format!("unknown flag {arg}\n{USAGE}")),
            _ => paths.push(arg),
        }
    }
    let [circuit, witness] = <[String; 2]>::try_from(paths).map_err(|_| USAGE.to_string())?;
    Ok(ProveArgs {
        circuit,
        witness,
        signers,
        spark,
        self_check,
        repeat,
        cooldown,
        tracing,
    })
}

fn parse_gen(mut args: impl Iterator<Item = String>) -> Result<GenArgs, String> {
    let (mut groups, mut out, mut tamper) = (None, None, false);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--groups" => {
                let list = args.next().ok_or("--groups takes a list of group sizes")?;
                let sizes: Result<Vec<usize>, _> = list.split(',').map(str::parse).collect();
                groups = Some(sizes.map_err(|_| format!("--groups: bad list {list}"))?);
            }
            "--out" => out = Some(args.next().ok_or("--out takes a directory")?),
            "--tamper" => tamper = true,
            _ => return Err(format!("unknown argument {arg}\n{USAGE}")),
        }
    }
    Ok(GenArgs {
        groups: groups.ok_or(USAGE)?,
        out: out.ok_or(USAGE)?,
        tamper,
    })
}

fn ms(timing: &Timing) -> String {
    format!("{:.1} ms{}", timing.mean() * 1e3, timing.spread())
}

fn read(path: &str) -> Result<Vec<u8>, String> {
    std::fs::read(path).map_err(|e| format!("{path}: {e}"))
}

fn gen_xmss(args: &GenArgs) -> Result<(), String> {
    let (inputs, set) = signers::generate(&args.groups, args.tamper)?;
    std::fs::create_dir_all(&args.out).map_err(|e| format!("{}: {e}", args.out))?;
    for (name, json) in [
        ("inputs.json", serde_json::to_string(&inputs)),
        ("signers.json", serde_json::to_string_pretty(&set)),
    ] {
        let path = format!("{}/{name}", args.out);
        std::fs::write(&path, json.map_err(|e| e.to_string())?).map_err(|e| format!("{path}: {e}"))?;
    }
    let digest: String = set.digest().iter().map(|b| format!("{b:02x}")).collect();
    println!(
        "{} groups, {} signatures{}; signer-set digest {digest}",
        set.groups.len(),
        args.groups.iter().sum::<usize>(),
        if args.tamper { ", one chain tip tampered" } else { "" }
    );
    Ok(())
}

fn prove(args: &ProveArgs) -> Result<(), String> {
    leanvm_core::init_prover();
    if args.tracing {
        bench::init_tracing();
    }
    let file = R1csFile::parse(&read(&args.circuit)?).map_err(|e| format!("{}: {e}", args.circuit))?;
    let block = BlockR1cs::new(&file).map_err(|e| format!("{}: {e}", args.circuit))?;
    let batch = WitnessFile::parse(&read(&args.witness)?).map_err(|e| format!("{}: {e}", args.witness))?;
    if batch.n_signals != block.n_signals {
        return Err(format!(
            "witness has {} signals, circuit {}",
            batch.n_signals, block.n_signals
        ));
    }
    let n_link = file.links.len();
    let boundary = match (&args.signers, block.links) {
        (_, None) if args.signers.is_some() => return Err("--signers needs a linked (CLB2) circuit".into()),
        (_, None) => None,
        (None, Some(_)) => Boundary::of(&block, &batch),
        (Some(path), Some(_)) => {
            let set: SignerSet = serde_json::from_slice(&read(path)?).map_err(|e| format!("{path}: {e}"))?;
            set.check_canonical()
                .map_err(|e| format!("{path}: not canonical: {e}"))?;
            let digest: String = set.digest().iter().map(|b| format!("{b:02x}")).collect();
            println!(
                "signer set: {} groups, {} keys, digest {digest}",
                set.groups.len(),
                set.groups.iter().map(|g| g.keys.len()).sum::<usize>()
            );
            Some(set.boundary(n_link)?)
        }
    };

    let k_log = block.k_log();
    let mut z = vec![0u64; (1usize << k_log) / 64];
    for i in 0..batch.n_instances {
        z.fill(0);
        block.layout_instance(batch.instance(i), &mut z);
        if let Some(row) = block.first_violation(&z) {
            return Err(format!("instance {i} violates constraint {row}"));
        }
        if i > 0 && block.link_values(batch.instance(i), false) != block.link_values(batch.instance(i - 1), true) {
            return Err(format!(
                "instance {i}'s link inputs are not instance {}'s outputs",
                i - 1
            ));
        }
    }
    if let Some(boundary) = &boundary
        && *boundary != Boundary::of(&block, &batch).expect("a linked block")
    {
        return Err("the batch's boundary is not the signer set's statement".into());
    }
    let shape = proof::Shape::new(&block, batch.n_instances).map_err(|e| format!("unsupported batch: {e}"))?;
    let m = &block.matrices;
    println!(
        "circuit: {} constraints, {} signals ({} public), {n_link} links, nnz A/B/C = {}/{}/{}",
        block.n_constraints,
        block.n_signals,
        block.n_public,
        m.a.nnz(),
        m.b.nnz(),
        m.c.nnz()
    );
    println!(
        "batch: {} instances, satisfied; k_log = {}, n_log = {}",
        batch.n_instances, shape.k_log, shape.n_log
    );

    let pk = args.spark.then(|| {
        let t = Instant::now();
        let pk = spark::preprocess(m, proof::LOG_INV_RATE);
        println!("spark preprocess: {:.1} ms", t.elapsed().as_secs_f64() * 1e3);
        pk
    });
    let vk = pk.as_ref().map(|pk| pk.verifier_key());
    let prove_mode = pk.as_ref().map_or(Mode::Direct, Mode::Spark);
    let verify_mode = vk.as_ref().map_or(Mode::Direct, Mode::Spark);
    let publics = proof::publics(&block, &batch);

    let plan = Plan::new(args.repeat, args.cooldown);
    let (p, prove_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        proof::prove(&block, &batch, prove_mode)
    });
    let p = p.map_err(|e| format!("prove: {e}"))?;
    let (verdict, verify_time) = Plan::new(args.repeat, 0)
        .measure_quiet(|_| proof::verify(&block, &publics, boundary.as_ref(), &p, verify_mode));
    verdict.map_err(|e| format!("verify: {e}"))?;
    let size = bincode::serialized_size(&p).map_err(|e| e.to_string())?;
    println!(
        "prove {}, verify {}, proof {size} bytes ({} scalars, {} opening phases)",
        ms(&prove_time),
        ms(&verify_time),
        p.stream.len(),
        p.merkle.len()
    );

    if args.self_check {
        let rejects = |publics: &[u64], boundary: Option<&Boundary>, p: &Proof| {
            proof::verify(&block, publics, boundary, p, verify_mode).is_err()
        };
        if block.n_public > 0 {
            let mut flipped = publics.clone();
            flipped[0] ^= 1 << 1;
            check(rejects(&flipped, boundary.as_ref(), &p), "flipped public bit")?;
        }
        if let Some(boundary) = &boundary {
            for (output, what) in [(false, "flipped boundary in bit"), (true, "flipped boundary out bit")] {
                let mut flipped = boundary.clone();
                let side = if output {
                    &mut flipped.output
                } else {
                    &mut flipped.input
                };
                side[0] ^= 1;
                check(rejects(&publics, Some(&flipped), &p), what)?;
            }
        }
        let bytes = bincode::serialize(&p).map_err(|e| e.to_string())?;
        for at in [bytes.len() / 3, bytes.len() / 2, bytes.len() - 1] {
            let mut bad = bytes.clone();
            bad[at] ^= 0x01;
            let rejected =
                bincode::deserialize::<Proof>(&bad).map_or(true, |q| rejects(&publics, boundary.as_ref(), &q));
            check(rejected, &format!("proof byte {at} of {} mutated", bytes.len()))?;
        }
        if args.spark {
            // SPARK runs last, so the final scalar of the stream is its own.
            let mut bad = p.clone();
            bad.stream.last_mut().expect("non-empty stream").c0 ^= 1;
            check(rejects(&publics, boundary.as_ref(), &bad), "SPARK scalar mutated")?;
        }
    }
    Ok(())
}

fn check(rejected: bool, what: &str) -> Result<(), String> {
    if rejected {
        println!("self-check: {what}: rejected");
        Ok(())
    } else {
        Err(format!("self-check: {what}: ACCEPTED"))
    }
}

fn main() -> ExitCode {
    let result = parse_args().and_then(|command| match command {
        Command::Prove(args) => prove(&args),
        Command::GenXmss(args) => gen_xmss(&args),
    });
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("{e}");
            ExitCode::FAILURE
        }
    }
}
