//! Claim-set trees: proofs anyone combines, each declaring the union of its children's sets or part of it.

use super::design::{Level, NodeInputs};
use super::union::UnionFill;
use super::*;
use crate::cpu::Prover;
use crate::rv::Region;
use crate::rv::asm::*;
use std::sync::LazyLock;

// A program whose output is its four advice words, after a loop that reads every framework block: a leaf that
// publishes whatever set the advice names, which the tree's mechanics need and no more.
static PROGRAM: LazyLock<Program> = LazyLock::new(|| {
    let text = Asm::new()
        .li(Reg::T0, Region::ADVICE.base())
        .load(Ld, Reg::A0, 0, Reg::T0)
        .load(Ld, Reg::A1, 8, Reg::T0)
        .load(Ld, Reg::A2, 16, Reg::T0)
        .load(Ld, Reg::A3, 24, Reg::T0)
        .li(Reg::T1, 9)
        .label("loop")
        .i(Addi, Reg::T1, Reg::T1, -1)
        .branch(Bne, Reg::T1, Reg::ZERO, "loop")
        .exit()
        .finish();
    Program::new(&text, Region::TEXT.base(), vec![3, 5], 2, 2).expect("a valid program")
});

fn program() -> &'static Program {
    &PROGRAM
}

fn member(i: u64) -> [u64; 4] {
    [i, 7 * i + 1, i << 9, 0x5eed ^ i]
}

fn label(tag: u64, word: u64) -> [u64; 6] {
    [tag, word, 0, 0, 0, 1]
}

fn group(tag: u64, word: u64, members: &[u64]) -> ClaimGroup {
    ClaimGroup {
        label: label(tag, word),
        members: members.iter().map(|&i| member(i)).collect(),
    }
}

fn set(groups: Vec<ClaimGroup>) -> ClaimSet {
    ClaimSet { groups }
}

/// Three leaves' sets, overlapping, in the order their programs wrote them (not canonical), of two label tags.
fn sets() -> [ClaimSet; 3] {
    [
        set(vec![group(1, 9, &[3, 1]), group(1, 2, &[1])]),
        set(vec![group(1, 9, &[1, 4]), group(2, 0, &[5])]),
        set(vec![group(1, 8, &[1]), group(2, 0, &[6, 5])]),
    ]
}

const CAPACITY: Capacity = Capacity { claims: 12, groups: 4 };

fn union(sets: &[&ClaimSet]) -> ClaimSet {
    ClaimSet::from_claims(sets.iter().flat_map(|s| s.claims()))
}

struct Fixture {
    tree: Tree<'static>,
    sets: [ClaimSet; 3],
    leaves: Vec<(Proof, Output)>,
    /// Each leaf's first-level proof, declaring its set.
    firsts: Vec<Aggregate>,
    /// The first two firsts' union.
    pair: Aggregate,
}

fn shape(leaf: LeafShape, claims: Option<Capacity>) -> TreeShape {
    TreeShape {
        leaf,
        arity_0: 1,
        arity: 3,
        rate: Rate::MIN,
        claims,
    }
}

fn leaf_proof(set: &ClaimSet) -> (Proof, Output) {
    let run = Prover::new(Rate::MIN)
        .prove(program(), &chain(&set.digest()))
        .expect("the run halts");
    (run.proof, run.output)
}

static FIXTURE: LazyLock<Fixture> = LazyLock::new(|| {
    let sets = sets();
    let leaves: Vec<(Proof, Output)> = sets.iter().map(leaf_proof).collect();
    let leaf = LeafShape::of(&leaves[0].0).expect("a canonical announcement");
    let tree = Tree::new(program(), shape(leaf, Some(CAPACITY))).expect("a tree");
    let firsts: Vec<Aggregate> = (sets.iter().zip(&leaves))
        .map(|(set, (proof, output))| {
            let leaf = ClaimLeaf::new(Leaf::new(proof, *output), set);
            tree.aggregate_leaves(&[leaf], None).expect("an honest leaf")
        })
        .collect();
    let pair = tree
        .aggregate(&[&firsts[0], &firsts[1]], None)
        .expect("honest children");
    Fixture {
        tree,
        sets,
        leaves,
        firsts,
        pair,
    }
});

fn fixture() -> &'static Fixture {
    &FIXTURE
}

#[test]
fn a_tree_has_a_node_circuit_for_each_arity() {
    let f = fixture();
    assert_eq!(f.tree.design.levels, [Level::First, Level::Node(2), Level::Node(3)]);
    assert!(f.tree.node_stats(3).is_some() && f.tree.node_stats(4).is_none());
}

#[test]
fn the_union_of_overlapping_children_of_any_kind_verifies() {
    let f = fixture();
    for (first, set) in f.firsts.iter().zip(&f.sets) {
        assert_eq!(first.claims, union(&[set]), "a leaf's set, made canonical");
        f.tree
            .verify_claims(&first.proof, &first.claims)
            .expect("a first-level root");
    }
    assert_eq!(f.pair.claims, union(&[&f.sets[0], &f.sets[1]]));
    f.tree
        .verify_claims(&f.pair.proof, &f.pair.claims)
        .expect("a root of two");
    // Three children: a node, a first-level proof, and a repeat of claims the node holds.
    let all = (f.tree.aggregate(&[&f.pair, &f.firsts[2], &f.firsts[0]], None)).expect("honest children");
    let expected = union(&[&f.sets[0], &f.sets[1], &f.sets[2]]);
    assert_eq!(all.claims, expected);
    assert!(expected.n_claims() < f.sets.iter().map(ClaimSet::n_claims).sum::<usize>());
    assert_eq!(all.proof.kind(), Kind::Node);
    f.tree
        .verify_claims(&all.proof, &expected)
        .expect("the root of all three");
}

#[test]
fn a_child_given_twice_or_alone_is_its_own_union() {
    let f = fixture();
    let twice = f
        .tree
        .aggregate(&[&f.firsts[1], &f.firsts[1]], None)
        .expect("duplicates");
    assert_eq!(twice.claims, f.firsts[1].claims);
    let alone = f.tree.aggregate(&[&f.pair], None).expect("one child");
    assert_eq!(alone.claims, f.pair.claims);
    f.tree
        .verify_claims(&alone.proof, &alone.claims)
        .expect("a republished root");
}

#[test]
fn a_node_may_omit_groups_and_declare_part_of_one() {
    let f = fixture();
    // Of the pair's groups, one member of (1, 9) only: (1, 2) and (2, 0) are omitted.
    let part = set(vec![group(1, 9, &[4])]);
    let narrowed = f
        .tree
        .aggregate(&[&f.pair], Some(&part))
        .expect("a covered declaration");
    assert_eq!(narrowed.claims, part);
    f.tree.verify_claims(&narrowed.proof, &part).expect("a narrowed root");
    // And nothing at all.
    let empty = f
        .tree
        .aggregate(&[&f.pair], Some(&ClaimSet::new()))
        .expect("an empty declaration");
    f.tree
        .verify_claims(&empty.proof, &ClaimSet::new())
        .expect("an empty root");
}

#[test]
fn an_uncovered_declaration_is_refused() {
    let f = fixture();
    // (1, 8) is the third leaf's, and a member at another label is another claim, of either tag.
    for declared in [
        union(&[&f.sets[2]]),
        set(vec![group(1, 2, &[3])]),
        set(vec![group(2, 1, &[5])]),
    ] {
        assert!(
            matches!(
                f.tree.aggregate(&[&f.firsts[0], &f.firsts[1]], Some(&declared)),
                Err(TreeError::NotCovered(_))
            ),
            "{declared:?}"
        );
    }
    // A member under the other tag.
    let claim = Claim {
        label: label(2, 2),
        member: member(1),
    };
    assert_eq!(
        f.tree.aggregate(&[&f.firsts[0]], Some(&ClaimSet::from_claims([claim]))),
        Err(TreeError::NotCovered(claim))
    );
}

#[test]
fn forged_coverage_is_refused() {
    let f = fixture();
    // In rows: the pair's union and a claim no child holds, the rest selected honestly.
    let d = &f.tree.design;
    let kind = d.node_kind(2).expect("a node of two");
    let mut declared = f.pair.claims.clone();
    declared.groups[0].members.push(member(99));
    let proofs = [&f.firsts[0].proof, &f.firsts[1].proof];
    let statements: Vec<TreeStatement> = (proofs.iter())
        .map(|p| TreeStatement::new(d.statement, p.words.clone()))
        .collect();
    let items = f.tree.child_witnesses(&proofs, &statements).expect("honest children");
    let shape = d.union_shape(Level::Node(2)).expect("a claim-set tree");
    let fill = UnionFill::unbacked(&shape, &[&f.firsts[0].claims, &f.firsts[1].claims], &declared);
    let inputs = NodeInputs::Prove {
        items: &items,
        tables: &f.tree.tables,
        union: Some(&fill),
    };
    let forged = f.tree.prove_rows(d.node(&inputs, kind), kind);
    assert!(
        matches!(&forged, Err(TreeError::Unsatisfied(check)) if check.scope().iter().any(|s| s == "coverage")),
        "{forged:?}"
    );

    // Natively: a child handed with another set than its statement's, a leaf whose output is not its set's.
    let lying = Aggregate {
        proof: f.firsts[0].proof.clone(),
        claims: f.pair.claims.clone(),
    };
    assert_eq!(
        f.tree.aggregate(&[&f.firsts[1], &lying], None),
        Err(TreeError::ChildClaims { index: 1 })
    );
    let (proof, output) = &f.leaves[0];
    let leaf = ClaimLeaf::new(Leaf::new(proof, *output), &f.sets[1]);
    assert_eq!(
        f.tree.aggregate_leaves(&[leaf], None),
        Err(TreeError::LeafClaims { index: 0 })
    );
}

#[test]
fn a_root_with_another_or_noncanonical_set_is_refused() {
    let f = fixture();
    let root = &f.pair;
    // The same claims in another order: not canonical.
    let mut shuffled = root.claims.clone();
    shuffled.groups.reverse();
    assert_eq!(
        f.tree.verify_claims(&root.proof, &shuffled),
        Err(TreeError::ClaimSet(ClaimSetError::UnsortedGroups))
    );
    assert_eq!(
        f.tree.verify_claims(&root.proof, &f.firsts[0].claims),
        Err(TreeError::Claims)
    );
    let mut over = root.claims.clone();
    over.groups.push(group(3, 0, &(0..12).collect::<Vec<_>>()));
    assert!(matches!(
        f.tree.verify_claims(&root.proof, &over),
        Err(TreeError::ClaimSet(ClaimSetError::TooManyClaims { .. }))
    ));
}

#[test]
fn a_narrowed_proof_cannot_be_widened_again() {
    let f = fixture();
    let part = union(&[&f.sets[0]]);
    let narrowed = f
        .tree
        .aggregate(&[&f.pair], Some(&part))
        .expect("a covered declaration");
    // Its parent sees the narrowed set only.
    assert!(matches!(
        f.tree.aggregate(&[&narrowed], Some(&f.pair.claims)),
        Err(TreeError::NotCovered(_))
    ));
    let widened = Aggregate {
        proof: narrowed.proof.clone(),
        claims: f.pair.claims.clone(),
    };
    assert_eq!(
        f.tree.aggregate(&[&widened], None),
        Err(TreeError::ChildClaims { index: 0 })
    );
    assert_eq!(
        f.tree.verify_claims(&narrowed.proof, &f.pair.claims),
        Err(TreeError::Claims)
    );
}

#[test]
fn positional_and_claim_set_proofs_are_not_confused() {
    let f = fixture();
    let leaf = LeafShape::of(&f.leaves[0].0).expect("a canonical announcement");
    let outputs_tree = Tree::new(program(), shape(leaf, None)).expect("a tree of outputs");
    let (proof, output) = &f.leaves[0];
    let positional = outputs_tree
        .prove_first(&[Leaf::new(proof, *output)])
        .expect("an honest leaf");
    outputs_tree.verify(&positional, &[*output]).expect("a positional root");

    // Each tree refuses the other's operations.
    let claims = TreeError::Semantics { claims: true };
    let outputs = TreeError::Semantics { claims: false };
    assert_eq!(f.tree.prove_first(&[Leaf::new(proof, *output)]), Err(claims.clone()));
    assert_eq!(f.tree.verify(&positional, &[*output]), Err(claims));
    let set_leaf = ClaimLeaf::new(Leaf::new(proof, *output), &f.sets[0]);
    assert_eq!(outputs_tree.aggregate_leaves(&[set_leaf], None), Err(outputs.clone()));
    assert_eq!(
        outputs_tree.verify_claims(&f.firsts[0].proof, &f.firsts[0].claims),
        Err(outputs)
    );

    // A positional root's statement read as a claim set: another session, so its proof does not verify.
    let as_claims = Aggregate {
        proof: positional.clone(),
        claims: f.firsts[0].claims.clone(),
    };
    assert!(matches!(
        f.tree.verify_claims(&positional, &f.firsts[0].claims),
        Err(TreeError::Root(_) | TreeError::Circuit(_))
    ));
    assert!(matches!(
        f.tree.aggregate(&[&as_claims], None),
        Err(TreeError::Child { index: 0, .. } | TreeError::Circuit(_))
    ));
    assert!(matches!(
        outputs_tree.verify(&f.firsts[0].proof, &[*output]),
        Err(TreeError::Root(_) | TreeError::Circuit(_))
    ));
}

#[test]
fn aggregates_from_different_provers_combine() {
    let f = fixture();
    // Another party builds the tree from the same program and shape, and proves the third leaf.
    let leaf = LeafShape::of(&f.leaves[0].0).expect("a canonical announcement");
    let theirs = Tree::new(program(), shape(leaf, Some(CAPACITY))).expect("the same tree");
    let (proof, output) = &f.leaves[2];
    let third = (theirs.aggregate_leaves(&[ClaimLeaf::new(Leaf::new(proof, *output), &f.sets[2])], None))
        .expect("an honest leaf");
    let received = Aggregate {
        proof: TreeProof::from_bytes(&third.proof.to_bytes()).expect("a tree proof"),
        claims: ClaimSet::from_bytes(&third.claims.to_bytes()).expect("a set"),
    };
    let combined = f
        .tree
        .aggregate(&[&f.pair, &received], None)
        .expect("their proof is ours");
    theirs
        .verify_claims(&combined.proof, &combined.claims)
        .expect("our root is theirs");
}

#[test]
fn sets_past_the_capacity_are_refused() {
    let f = fixture();
    let big = set(vec![group(1, 1, &(0..11).collect::<Vec<_>>())]);
    let (proof, output) = leaf_proof(&big);
    let first = (f
        .tree
        .aggregate_leaves(&[ClaimLeaf::new(Leaf::new(&proof, output), &big)], None))
    .expect("a set within the capacity");
    assert_eq!(f.tree.aggregate(&[&first, &f.pair], None), Err(TreeError::Capacity));
}
