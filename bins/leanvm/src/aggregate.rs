//! Aggregation: prove one leaf once, then a tree over copies of its proof, and report each kind of node and the whole tree.

use crate::refuse;
use crate::workload::Workload;
use bench::{Plan, Timing};
use clap::ValueEnum;
use leanvm::aggregate::{
    CircuitStats, Kind, Leaf, LeafShape, LeafStatement, Leaves, Subtree, Tree, TreeProof, TreeShape,
};
use leanvm::{
    ProvenRun, Prover, Rate, SphincsBatch, SphincsClaim, SphincsProof, SphincsSignature, Stats, XmssBatch, XmssClaim,
    XmssProof, XmssSignature,
};
use primitives::{pretty_f64, pretty_integer};

/// The leaf program.
#[derive(Clone, Copy, Debug, PartialEq, Eq, ValueEnum)]
pub enum LeafProgram {
    /// Fibonacci modulo 2^64, `n` steps.
    Fibonacci,
    /// `n` leanXMSS signatures, checked by a RISC-V guest.
    Leanxmss,
    /// `n` leanSPHINCS signatures, checked by a RISC-V guest.
    Leansphincs,
    /// `n` leanXMSS signatures, checked by one recursion circuit.
    LeanxmssRec,
    /// `n` leanSPHINCS signatures, checked by one recursion circuit.
    LeansphincsRec,
}

/// The tree's leaf family: its key and what each of its leaves proves.
enum Family {
    /// A RISC-V program's runs, and the shape their proofs announce.
    Runs {
        workload: Workload,
        stats: Stats,
        shape: LeafShape,
    },
    /// A leanXMSS batch circuit, and the claims and signatures each leaf proves.
    Xmss {
        batch: XmssBatch,
        claims: Vec<XmssClaim>,
        signatures: Vec<XmssSignature>,
    },
    /// A leanSPHINCS batch circuit, and the claims and signatures each leaf proves.
    Sphincs {
        batch: SphincsBatch,
        claims: Vec<SphincsClaim>,
        signatures: Vec<SphincsSignature>,
    },
}

/// The family's proven leaf.
enum Proven {
    Run(Box<ProvenRun>),
    Xmss(XmssProof),
    Sphincs(SphincsProof),
}

impl Family {
    /// The family of `program` at size `n`, its leaves proven at `rate`.
    fn new(program: LeafProgram, n: usize, rate: Rate) -> Self {
        let runs = |workload: Workload| {
            // The run, measured, gives the shape its proofs announce: the tree is built before anything is proven.
            let stats = workload.measure();
            let shape = LeafShape::measured(&stats, rate);
            Self::Runs { workload, stats, shape }
        };
        match program {
            LeafProgram::Fibonacci => runs(Workload::fibonacci(n)),
            LeafProgram::Leanxmss => runs(Workload::leanxmss(n)),
            LeafProgram::Leansphincs => runs(Workload::leansphincs(n)),
            LeafProgram::LeanxmssRec => {
                let (claims, signatures) = crate::xmss::signed(n);
                Self::Xmss {
                    batch: XmssBatch::new(n, rate).unwrap_or_else(|e| refuse(format_args!("{e}"))),
                    claims,
                    signatures,
                }
            }
            LeafProgram::LeansphincsRec => {
                let (claims, signatures) = crate::sphincs::signed(n);
                Self::Sphincs {
                    batch: SphincsBatch::new(n, rate).unwrap_or_else(|e| refuse(format_args!("{e}"))),
                    claims,
                    signatures,
                }
            }
        }
    }

    fn title(&self) -> String {
        match self {
            Self::Runs { workload, .. } => workload.title.clone(),
            Self::Xmss { batch, .. } => format!(
                "leanXMSS verification on the recursion machine, {} signatures",
                batch.n()
            ),
            Self::Sphincs { batch, .. } => {
                format!(
                    "leanSPHINCS verification on the recursion machine, {} signatures",
                    batch.n()
                )
            }
        }
    }

    const fn leaves(&self) -> Leaves<'_> {
        match self {
            Self::Runs { workload, shape, .. } => Leaves::Runs {
                program: &workload.program,
                shape: *shape,
            },
            Self::Xmss { batch, .. } => batch.leaves(),
            Self::Sphincs { batch, .. } => batch.leaves(),
        }
    }

    fn prove(&self, prover: &Prover) -> Proven {
        match self {
            Self::Runs { workload, .. } => Proven::Run(Box::new(workload.prove(prover))),
            Self::Xmss {
                batch,
                claims,
                signatures,
            } => Proven::Xmss(batch.prove(claims, signatures).expect("honest signatures")),
            Self::Sphincs {
                batch,
                claims,
                signatures,
            } => Proven::Sphincs(batch.prove(claims, signatures).expect("honest signatures")),
        }
    }

    /// The leaf of its proven leaf, and what it states.
    fn leaf<'a>(&'a self, proven: &'a Proven) -> (Leaf<'a>, LeafStatement) {
        let leaf = match (self, proven) {
            (Self::Runs { .. }, Proven::Run(run)) => Leaf::from(&**run),
            (Self::Xmss { batch, claims, .. }, Proven::Xmss(proof)) => batch.leaf(claims, proof).expect("its claims"),
            (Self::Sphincs { batch, claims, .. }, Proven::Sphincs(proof)) => {
                batch.leaf(claims, proof).expect("its claims")
            }
            _ => unreachable!("a family's own proof"),
        };
        let statement = leaf.statement();
        (leaf, statement)
    }

    /// Its circuit's rows per table, if a recursion circuit, and the words a proof commits.
    fn cost(&self) -> (Option<CircuitStats>, usize) {
        match self {
            Self::Runs { stats, .. } => (None, stats.committed),
            Self::Xmss { batch, .. } => {
                let stats = batch.stats();
                let committed = stats.committed;
                (Some(stats), committed)
            }
            Self::Sphincs { batch, .. } => {
                let stats = batch.stats();
                let committed = stats.committed;
                (Some(stats), committed)
            }
        }
    }
}

impl Proven {
    fn bytes(&self) -> usize {
        match self {
            Self::Run(run) => run.proof.to_bytes().len(),
            Self::Xmss(proof) => proof.to_bytes().len(),
            Self::Sphincs(proof) => proof.to_bytes().len(),
        }
    }
}

fn ms(t: &Timing) -> String {
    format!("{} ms{}", pretty_f64(t.mean() * 1000.0), t.spread())
}

fn secs(t: &Timing) -> String {
    format!("{} s{}", pretty_f64(t.mean()), t.spread())
}

/// A circuit's rows per table and padded heights, and the words a proof commits.
fn print_cost(stats: Option<&CircuitStats>, committed: usize) {
    if let Some(stats) = stats {
        let rows: Vec<String> = stats.tables.iter().map(ToString::to_string).collect();
        println!("  rows                        : {}", rows.join("  "));
    }
    println!(
        "  committed words             : {} (2^{:.3})",
        pretty_integer(&committed),
        (committed as f64).log2()
    );
}

/// One kind of node: its circuit, its proof, and its times.
fn report(name: &str, tree: &Tree<'_>, kind: Kind, proof: &TreeProof, prove: &Timing, verify: &Timing) {
    let stats = tree.stats(kind);
    println!("{name}");
    print_cost(Some(&stats), stats.committed);
    println!(
        "  proof size                  : {:.1} KiB",
        proof.to_bytes().len() as f64 / 1024.0
    );
    println!("  proving                     : {}", secs(prove));
    println!("  verifying as a root         : {}", ms(verify));
}

/// Prove one leaf of `program` at size `n` at `leaf_prover`'s rate, then the tree of `leaves` over copies of its proof, every tree proof at `prover`'s rate, and print the report.
///
/// The tree's first level verifies `arity_0` leaves, each node `arity` children.
pub fn run(
    (program, n): (LeafProgram, usize),
    leaves: usize,
    arity_0: usize,
    arity: usize,
    leaf_prover: &Prover,
    prover: &Prover,
    plan: Plan,
) {
    let rate = prover.rate();
    let shape = TreeShape {
        arity_0,
        arity,
        rate,
        claims: None,
    };
    shape.depth(leaves).unwrap_or_else(|e| refuse(format_args!("{e}")));
    let family = Family::new(program, n, leaf_prover.rate());
    let title = family.title();

    let (proven, leaf_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        family.prove(leaf_prover)
    });
    let quiet = Plan::new(plan.repeat, 0);

    let (tree, setup) = Plan::new(1, 0).measure_quiet(|_| {
        let _span = tracing::info_span!("Tree setup").entered();
        Tree::new(family.leaves(), shape).unwrap_or_else(|e| refuse(format_args!("{e}")))
    });
    let (leaf, statement) = family.leaf(&proven);

    println!(
        "Aggregation tree over {leaves} leaves of {title}, first level {arity_0}, arity {arity}, leaves at log-inv-rate {}, tree proofs at {}",
        leaf_prover.rate().log_inv_rate(),
        rate.log_inv_rate()
    );
    println!("leaf: {title}");
    let (stats, committed) = family.cost();
    print_cost(stats.as_ref(), committed);
    println!(
        "  proof size                  : {:.1} KiB",
        proven.bytes() as f64 / 1024.0
    );
    println!("  proving                     : {}", secs(&leaf_time));
    println!("tree setup (both circuits, the fixed polynomials): {}", secs(&setup));

    let firsts = vec![leaf.clone(); arity_0];
    let (first, first_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        tree.prove_first(&firsts).expect("honest leaves")
    });
    let first_level = Subtree::First(vec![statement.clone(); arity_0]);
    let (_, first_verify) = quiet.measure_quiet(|_| tree.verify(&first, &first_level).expect("a first-level root"));
    report(
        &format!("first-level node, {arity_0} x {title}"),
        &tree,
        Kind::First,
        &first,
        &first_time,
        &first_verify,
    );

    if leaves > arity_0 {
        let children = vec![first; arity];
        let (node, node_time) = plan.warm_then_measure(|last| {
            let _quiet = (!last).then(bench::suppress_tracing);
            tree.prove_node(&children).expect("honest children")
        });
        let expected = Subtree::Node(vec![first_level; arity]);
        let (_, node_verify) = quiet.measure_quiet(|_| tree.verify(&node, &expected).expect("a root"));
        report(
            &format!("node, {arity} first-level children"),
            &tree,
            Kind::Node,
            &node,
            &node_time,
            &node_verify,
        );
    }

    let all = vec![leaf; leaves];
    let expected = Subtree::balanced(vec![statement; leaves], &shape).unwrap_or_else(|e| refuse(format_args!("{e}")));
    let (root, whole) = Plan::new(1, 0).measure_quiet(|_| {
        let _span = tracing::info_span!("Prove tree", leaves).entered();
        tree.prove(&all).unwrap_or_else(|e| refuse(format_args!("{e}")))
    });
    let (_, root_verify) = quiet.measure_quiet(|_| tree.verify(&root, &expected).expect("the root verifies"));
    println!("whole tree");
    println!(
        "  proving every node          : {}, after the leaf proofs",
        secs(&whole)
    );
    println!("  verifying the root          : {}", ms(&root_verify));
    println!(
        "  peak memory                 : {} GiB",
        pretty_f64(bench::peak_rss_bytes() as f64 / (1u64 << 30) as f64)
    );
}
