//! Assumptions: prove two runs of the Fibonacci guest and a guest that assumes them (`programs/defer`), check the
//! latter alone, then prove the tree that resolves its assumptions.

use bench::Plan;
use leanvm::aggregate::{AssumedProofs, Kind, Leaf, LeafShape, Tree, TreeShape};
use leanvm::{Assumption, Output, Program, ProvenRun, Prover};
use primitives::pretty_integer;

use crate::aggregate::{report, secs};
use crate::guest::refuse;

/// Prove `F(n + 2)` from proofs of `F(n)` and `F(n + 1)`, resolve the assumptions in a tree, and print the report.
pub fn run(n: u64, prover: &Prover, plan: Plan) {
    let rate = prover.rate();
    let load = |elf| Program::from_elf(elf).unwrap_or_else(|e| refuse(format_args!("{e}")));
    let (fibonacci, outer) = (load(defer_host::FIBONACCI_ELF), load(defer_host::ELF));
    let run = defer_host::run(fibonacci.digest_words(), n);
    let prove = |program: &Program, advice: &[u64], what: &str| {
        plan.warm_then_measure(|last| {
            let _quiet = (!last).then(bench::suppress_tracing);
            (prover.prove(program, advice)).unwrap_or_else(|e| refuse(format_args!("{what} has no proof: {e}")))
        })
    };

    let inner: Vec<ProvenRun> = (0..2)
        .map(|i| {
            let (proved, time) = prove(&fibonacci, &[n + i], "the Fibonacci run");
            assert_eq!(proved.output, run.assumed[i as usize].1, "the assumed run's output");
            println!("Fibonacci, n = {}: proving {}", n + i, secs(&time));
            proved
        })
        .collect();
    let (proved, time) = prove(&outer, &run.advice, "the assuming guest");
    assert_eq!(proved.output, run.expected, "the guest's output is the host's");
    println!(
        "guest assuming both: {} cycles, proving {}",
        pretty_integer(&proved.stats.base_counts.values().sum::<usize>()),
        secs(&time)
    );

    // Alone, the guest's proof shows its committed values only under its assumptions.
    let committed = Output::new(run.committed);
    let assumptions = run
        .assumed
        .map(|(program, output)| Assumption::new(program, Output::new(output)));
    let unresolved = (outer.verify_assuming(committed, &assumptions, &proved.proof))
        .unwrap_or_else(|e| refuse(format_args!("the guest's proof: {e}")));
    println!(
        "native verifier, the guest's proof alone: verifies, {} assumptions unresolved",
        unresolved.len()
    );

    let shape = |proof| LeafShape::of(proof).expect("an honest announcement");
    if shape(&inner[0].proof) != shape(&inner[1].proof) {
        refuse(format_args!(
            "the two Fibonacci runs have proofs of different shapes: pick another n"
        ));
    }
    let tree_shape = TreeShape {
        leaf: shape(&proved.proof),
        arity_0: 1,
        arity: 2,
        rate,
    };
    let tree = Tree::assuming(
        &outer,
        tree_shape,
        AssumedProofs {
            program: &fibonacci,
            leaf: shape(&inner[0].proof),
            count: 2,
        },
    )
    .unwrap_or_else(|e| refuse(format_args!("{e}")));
    let assumed: Vec<Leaf<'_>> = inner.iter().map(Leaf::from).collect();
    let leaf = Leaf::assuming(&proved.proof, committed, &assumed);
    let (root, root_time) = plan.warm_then_measure(|last| {
        let _quiet = (!last).then(bench::suppress_tracing);
        tree.prove_first(&[leaf])
            .unwrap_or_else(|e| refuse(format_args!("{e}")))
    });
    let (_, verify_time) = Plan::new(plan.repeat, 0).measure_quiet(|_| {
        tree.verify(&root, &[committed])
            .unwrap_or_else(|e| refuse(format_args!("the root: {e}")));
    });
    report(
        "first-level node resolving 2 assumptions",
        &tree,
        Kind::First,
        &root,
        &root_time,
        &verify_time,
    );

    // The same guest's proof alone, its assumptions left in its output: what resolving them adds.
    let alone = Tree::new(&outer, tree_shape).unwrap_or_else(|e| refuse(format_args!("{e}")));
    let rows = |tree: &Tree<'_>| -> Vec<(&'static str, i64)> {
        (tree.stats(Kind::First).tables.iter())
            .map(|t| (t.name, i64::try_from(t.rows).expect("rows fit")))
            .collect()
    };
    let added: Vec<String> = (rows(&tree).into_iter().zip(rows(&alone)))
        .map(|((name, with), (_, without))| format!("{name} {}", pretty_integer(&(with - without))))
        .collect();
    println!("rows the 2 assumptions add to a first-level node: {}", added.join("  "));
}
