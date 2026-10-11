//! Claim-set trees: proofs anyone combines, each declaring the union of its children's sets or part of it.

use super::design::{ChildWitness, LARGE, Level, NodeInputs, Place, SMALL};
use super::statement::Section;
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

fn shape(leaf: LeafShape, claims: Option<ClaimShape>) -> TreeShape {
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
    let tree = Tree::new(program(), shape(leaf, Some(ClaimShape::new(CAPACITY)))).expect("a tree");
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
    let nodes = [Level::First, Level::Node(2), Level::Node(3)];
    let places: Vec<Place> = nodes.map(|level| Place { tier: SMALL, level }).into();
    assert_eq!(f.tree.design.places, places);
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
    let kind = d.place(SMALL, Level::Node(2)).expect("a node of two");
    let mut declared = f.pair.claims.clone();
    declared.groups[0].members.push(member(99));
    let proofs = [&f.firsts[0].proof, &f.firsts[1].proof];
    let statements: Vec<TreeStatement> = (proofs.iter())
        .map(|p| TreeStatement::new(d.statement, p.words.clone()))
        .collect();
    let items = f.tree.child_witnesses(SMALL, &proofs, &statements).expect("honest children");
    let shape = d.union_shape(kind).expect("a claim-set tree");
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
    let theirs = Tree::new(program(), shape(leaf, Some(ClaimShape::new(CAPACITY)))).expect("the same tree");
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

/// The small tier of the tiered fixture: nodes of two children declaring fewer than five claims in at most two groups.
const SMALL_TIER: Tier = Tier {
    arity: 2,
    capacity: Capacity { claims: 5, groups: 2 },
};

/// The fixture's leaves in a tree of two tiers.
struct Tiered {
    tree: Tree<'static>,
    /// Each leaf's first-level proof, of the small tier.
    firsts: Vec<Aggregate>,
    /// The first two firsts' union, five claims in three groups: of the large tier.
    pair: Aggregate,
}

fn tiered_tree() -> Tree<'static> {
    let leaf = LeafShape::of(&fixture().leaves[0].0).expect("a canonical announcement");
    let claims = ClaimShape {
        capacity: CAPACITY,
        small: Some(SMALL_TIER),
    };
    Tree::new(program(), shape(leaf, Some(claims))).expect("a tree of two tiers")
}

static TIERED: LazyLock<Tiered> = LazyLock::new(|| {
    let f = fixture();
    let tree = tiered_tree();
    let firsts: Vec<Aggregate> = (f.sets.iter().zip(&f.leaves))
        .map(|(set, (proof, output))| {
            let leaf = ClaimLeaf::new(Leaf::new(proof, *output), set);
            tree.aggregate_leaves(&[leaf], None).expect("an honest leaf")
        })
        .collect();
    let pair = tree
        .aggregate(&[&firsts[0], &firsts[1]], None)
        .expect("honest children");
    Tiered { tree, firsts, pair }
});

fn tiered() -> &'static Tiered {
    &TIERED
}

#[test]
fn a_tree_of_two_tiers_has_a_wrap_and_heights_per_tier() {
    let t = tiered();
    let d = &t.tree.design;
    let small = |level| Place { tier: SMALL, level };
    let large = |level| Place { tier: LARGE, level };
    assert_eq!(
        d.places,
        [
            small(Level::First),
            small(Level::Node(2)),
            small(Level::Wrap),
            large(Level::Node(3)),
        ]
    );
    assert!(t.tree.small_node_stats(3).is_none() && t.tree.wrap_stats().is_some());
    assert!(t.tree.node_stats(3).is_some() && t.tree.node_stats(2).is_none());
    // Each tier's circuits are at its own heights.
    for (p, place) in d.places.iter().enumerate() {
        assert_eq!(t.tree.circuit(p).heights(), d.tiers[place.tier].taus, "{place:?}");
    }
    // A kind names one circuit, whose proofs state it.
    for p in 0..d.places.len() {
        assert_eq!(d.position(d.code(p)), Some(p));
    }
}

#[test]
fn small_unions_stay_small_and_large_proofs_are_wrapped_to_combine() {
    let (t, f) = (tiered(), fixture());
    for first in &t.firsts {
        assert!(!t.tree.is_large(&first.proof));
        (t.tree)
            .verify_claims(&first.proof, &first.claims)
            .expect("a small root");
    }
    assert!(t.tree.is_large(&t.pair.proof));
    assert_eq!(t.pair.claims, union(&[&f.sets[0], &f.sets[1]]));
    (t.tree)
        .verify_claims(&t.pair.proof, &t.pair.claims)
        .expect("a large root");
    let twice = (t.tree.aggregate(&[&t.firsts[2], &t.firsts[2]], None)).expect("duplicates");
    assert!(!t.tree.is_large(&twice.proof));
    assert_eq!(twice.claims, t.firsts[2].claims);

    // Three children, one large: wrapped, then the large tier's node of three.
    let all = (t.tree.aggregate(&[&t.pair, &t.firsts[2], &t.firsts[0]], None)).expect("a large child");
    assert!(t.tree.is_large(&all.proof));
    assert_eq!(all.claims, union(&[&f.sets[0], &f.sets[1], &f.sets[2]]));
    (t.tree)
        .verify_claims(&all.proof, &all.claims)
        .expect("the root of all three");

    // The large pair narrowed to what the small tier holds: wrapped, then a small node; and not widened again.
    let part = set(vec![group(1, 9, &[1, 3, 4])]);
    let narrowed = (t.tree.aggregate(&[&t.pair], Some(&part))).expect("a covered declaration");
    assert!(!t.tree.is_large(&narrowed.proof));
    t.tree.verify_claims(&narrowed.proof, &part).expect("a narrowed root");
    assert!(matches!(
        t.tree.aggregate(&[&narrowed], Some(&t.pair.claims)),
        Err(TreeError::NotCovered(_))
    ));
    let mut shuffled = all.claims.clone();
    shuffled.groups.reverse();
    assert_eq!(
        t.tree.verify_claims(&all.proof, &shuffled),
        Err(TreeError::ClaimSet(ClaimSetError::UnsortedGroups))
    );
}

#[test]
fn a_wrap_states_its_childs_set_only() {
    let t = tiered();
    let d = &t.tree.design;
    // Natively: a large child handed with another set is refused, before its wrap.
    let lying = Aggregate {
        proof: t.pair.proof.clone(),
        claims: t.firsts[0].claims.clone(),
    };
    assert_eq!(
        t.tree.aggregate(&[&t.firsts[2], &lying], None),
        Err(TreeError::ChildClaims { index: 1 })
    );
    // A large proof is no child of a node's rows, which verify small ones.
    let honest = [TreeStatement::new(d.statement, t.pair.proof.words.clone())];
    assert_eq!(
        (t.tree.child_witnesses(SMALL, &[&t.pair.proof], &honest)).err(),
        Some(TreeError::Circuit(t.pair.proof.circuit))
    );

    // In rows: the wrap's child stating another digest than its proof's does not verify.
    let position = d.place(SMALL, Level::Wrap).expect("a wrap");
    let items = (t.tree.child_witnesses(LARGE, &[&t.pair.proof], &honest)).expect("an honest child");
    let mut words = t.pair.proof.words.clone();
    let digest = d.statement.range(Section::Digest).start;
    words[digest] = F192::new(words[digest].c0 ^ 1, words[digest].c1, words[digest].c2);
    let forged = TreeStatement::new(d.statement, words);
    let items = [ChildWitness {
        statement: &forged,
        proof: &t.pair.proof.proof,
        openings: items[0].openings.clone(),
        columns: items[0].columns,
    }];
    let inputs = NodeInputs::Prove {
        items: &items,
        tables: &t.tree.tables,
        union: None,
    };
    let wrapped = t.tree.prove_rows(d.node(&inputs, position), position);
    assert!(matches!(wrapped, Err(TreeError::Unsatisfied(_))), "{wrapped:?}");
}

#[test]
fn a_tiered_first_level_and_union_stay_within_their_capacities() {
    let t = tiered();
    // The first level is the small tier's: a leaf of five claims is past it.
    let five = set(vec![group(1, 1, &[0, 1, 2, 3, 4])]);
    let (proof, output) = leaf_proof(&five);
    assert_eq!(
        t.tree.aggregate_leaves(&[ClaimLeaf::new(Leaf::new(&proof, output), &five)], None),
        Err(TreeError::Capacity)
    );
    // And the large tier's capacity bounds every union.
    let four = set(vec![group(3, 1, &[0, 1, 2, 3])]);
    let (proof, output) = leaf_proof(&four);
    let first = (t.tree.aggregate_leaves(&[ClaimLeaf::new(Leaf::new(&proof, output), &four)], None))
        .expect("a set within the small tier");
    let big = (t.tree.aggregate(&[&first, &t.pair], None)).expect("nine claims within the tree's capacity");
    assert!(t.tree.is_large(&big.proof));
    assert_eq!(t.tree.aggregate(&[&big, &t.firsts[2]], None), Err(TreeError::Capacity));
}

#[test]
fn tiered_aggregates_from_different_provers_combine() {
    let (t, f) = (tiered(), fixture());
    let theirs = tiered_tree();
    let (proof, output) = &f.leaves[2];
    let third = (theirs.aggregate_leaves(&[ClaimLeaf::new(Leaf::new(proof, *output), &f.sets[2])], None))
        .expect("an honest leaf");
    let both = (theirs.aggregate(&[&third, &t.pair], None)).expect("our large proof is theirs");
    let received = Aggregate {
        proof: TreeProof::from_bytes(&both.proof.to_bytes()).expect("a tree proof"),
        claims: ClaimSet::from_bytes(&both.claims.to_bytes()).expect("a set"),
    };
    let again = (t.tree.aggregate(&[&received, &t.firsts[0]], None)).expect("their large proof is ours");
    theirs
        .verify_claims(&again.proof, &again.claims)
        .expect("our root is theirs");
    // A one-tier tree of the same capacity is another tree.
    assert!(matches!(
        f.tree.verify_claims(&t.pair.proof, &t.pair.claims),
        Err(TreeError::Root(_) | TreeError::Circuit(_))
    ));
}
