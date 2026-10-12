//! Aggregation trees: leaf proofs of one family, recursion proofs above them, one root the native verifier checks.
//!
//! ```text
//!                 node                  verifies arity tree proofs of any kind
//!               /      \
//!        first-level   first-level      each verifies arity_0 leaves
//!          /  \          /  \
//!       leaf  leaf    leaf  leaf
//! ```
//!
//! A tree's leaves are of one family: RISC-V proofs of one program, or proofs of one recursion circuit (a batch of
//! signatures, say). The tree's session names the family, so a tree proof verifies under a tree of its own family only.
//!
//! Every tree proof states the same words, whatever the tree's size:
//!
//! - its kind, and a digest;
//! - one claim on each dense polynomial the tree has: the RISC-V program's bytecode table and RAM image, or the leaf circuit's fixed polynomial, and the nodes' fixed polynomial, which holds every circuit's fixed columns;
//! - each flock circuit's two matrices at one row point and one column point.
//!
//! Each node reduces the claims its children leave and carry to one of each, and only the root's verifier evaluates them.
//!
//! A tree has one of two semantics, which its shape fixes:
//!
//! - **Outputs**: the digest is of what the leaves under the proof state, in order, through the tree's fixed shape.
//! - **Claim sets**: the leaves publish claim sets (their output is the hash of their set's digest), and the digest is
//!   of the set the proof declares: by default the union of its children's sets, or any part of it. Each node proves
//!   every claim it declares is one of its children's (`union`), so every claim of the root's set is one a leaf
//!   published, whatever the tree's shape: anyone may combine any proofs of the tree, up to its largest arity, and the
//!   root's verifier needs the set alone. What a claim means is the leaf program's (`multiset`). Its leaves are RISC-V
//!   proofs.
//!
//! A claim-set tree has a node circuit for each arity from two to its largest, all of one height, or two tiers each
//! at heights of its own ([`Tier`]): small proofs then never pay for the largest node's union and children.

use crate::class_flock::FlockId;
use crate::cpu::{Announcement, DecodeError, Output, Program, Proof, ProvenRun, Stats, VerifyError};
use crate::envelope::Envelope;
use crate::pcs::Rate;
use crate::rec::circuit::{Circuit, Finished, Limbs, chain, digest_limbs};
use crate::rec::fixed::FixedColumns;
use crate::rec::layout::RecLayout;
use crate::rec::proof::instance;
use crate::rec::table::{Heights, Table};
use crate::rec::transcript::ProofSource;
use crate::rec::verifier::ProofShape;
use crate::tables::PerTable;
use design::{
    ChildWitness, CircuitFamily, CircuitWitness, Design, Family, LARGE, LeafWitness, Level, NodeInputs, NodeRows, SMALL,
};
use fiat_shamir::{FromNarg, ProofTranscript, ProverState, SessionId};
use pcs::merkle::Openings;
use primitives::field::F192;
use primitives::multilinear::{eq_table, mle_eval_par};
use reduce::DenseTables;
use statement::{Items, TreeStatement};
use thiserror::Error;
use tracing::info_span;
use union::{FillError, UnionFill};

#[cfg(test)]
mod claim_tests;
mod claims;
mod design;
mod fixed;

mod multiset;
mod reduce;
mod statement;
mod stats;
#[cfg(test)]
mod tests;

mod union;

pub use crate::rec::circuit::Unsatisfied;
pub use crate::tables::Part;
pub use claims::DensePoly;
pub use multiset::{Capacity, Claim, ClaimGroup, ClaimSet, ClaimSetError};
pub use statement::Kind;
pub use stats::{CircuitStats, TableStats};

/// The most rounds the search for the nodes' heights takes: each round at least doubles a table.
const MAX_ROUNDS: usize = 8;

/// The shape every RISC-V leaf proof of a tree shares.
///
/// It is each table's height and the commitment's rate, as a proof announces them.
///
/// A tree's circuits are built from it, so they verify leaves of that shape only.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LeafShape {
    /// Each table's base-two logarithm of rows.
    taus: PerTable<usize>,
    /// The commitment's rate.
    rate: Rate,
}

/// A recursion circuit whose proofs are leaves of a tree: its circuit, its fixed columns, its transcript's session and its proofs' rate.
///
/// A batch of signatures gives it (`XmssBatch::leaves`).
#[derive(Clone, Copy)]
pub struct LeafCircuit<'p> {
    /// The circuit.
    pub(crate) circuit: &'p Circuit,
    /// Its fixed columns at its heights.
    pub(crate) columns: &'p FixedColumns,
    /// Its proofs' transcript's session, which names the circuit and its size.
    pub(crate) session: SessionId,
    /// Its proofs' rate.
    pub(crate) rate: Rate,
}

/// A tree's leaf family: what every leaf of the tree is a proof of.
#[derive(Clone, Copy)]
pub enum Leaves<'p> {
    /// RISC-V proofs of one program, of one shape.
    Runs {
        /// The program.
        program: &'p Program,
        /// The proofs' shape.
        shape: LeafShape,
    },
    /// Proofs of one recursion circuit.
    Circuit(LeafCircuit<'p>),
}

/// One leaf of a tree: a proof, and what it proves.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Leaf<'a>(LeafProof<'a>);

/// A leaf's proof and what it proves.
#[derive(Clone, Debug, PartialEq, Eq)]
enum LeafProof<'a> {
    /// A RISC-V proof of a run, and the output it claims.
    Run { proof: &'a Proof, output: Output },
    /// A proof of the recursion circuit of session `session`, and its statement.
    Circuit {
        session: SessionId,
        statement: Vec<Limbs>,
        proof: &'a ProofTranscript,
        rate: Rate,
    },
}

/// What one leaf states, which the root's verifier is given.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeafStatement(Stated);

/// What a leaf states: a run's output, or a recursion circuit's statement.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Stated {
    /// A RISC-V proof's output.
    Run(Output),
    /// The statement of a proof of the recursion circuit of session `session`.
    Circuit { session: SessionId, words: Vec<Limbs> },
}

/// The tree a root is expected to cover: its shape, and what each leaf states.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Subtree {
    /// A first-level node: what its leaves state, in order.
    First(Vec<LeafStatement>),
    /// A node: its children, in order.
    Node(Vec<Self>),
}

/// How a tree is shaped.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TreeShape {
    /// The leaf proofs a first-level node verifies, at least one.
    pub arity_0: usize,
    /// The tree proofs a higher node verifies, at least two: the only arity of a tree of outputs, the largest of a
    /// claim-set tree.
    pub arity: usize,
    /// The commitment rate of every tree proof.
    pub rate: Rate,
    /// A claim-set tree's capacities; none for a tree of outputs.
    pub claims: Option<ClaimShape>,
}

/// The capacities of a claim-set tree.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ClaimShape {
    /// The capacity of the tree's largest nodes and of a root's set: a node's children's sets together and its own set
    /// stay within it.
    pub capacity: Capacity,
    /// The small tier: nodes of at most its arity, whose sets stay within its capacity, at heights of their own. With
    /// none, every circuit is at the largest node's heights.
    pub small: Option<Tier>,
}

/// A claim-set tree's small tier: its first level, its nodes, and the wrap of its large proofs.
///
/// Its circuits have heights of their own, which its nodes' few children and small unions fix, so a proof of a small
/// set never pays for the tree's largest node. The large tier's nodes verify small proofs, and a large proof is
/// combined further once wrapped: one small proof verifying it and stating its set.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Tier {
    /// The most children its nodes verify, at least two and at most the tree's arity.
    pub arity: usize,
    /// The capacity of its nodes' unions and of its first level's, within the tree's.
    pub capacity: Capacity,
}

/// An aggregation tree over leaf proofs of one family.
///
/// It is the tree's verifying key, and what its prover needs.
///
/// It is built from the leaf family and the shape alone, before any proof exists.
pub struct Tree<'p> {
    /// How it is shaped.
    shape: TreeShape,
    /// What fixes the circuits.
    design: Design<'p>,
    /// Each kind's circuit, by its index: the first level's first.
    circuits: Vec<Circuit>,
    /// Each kind's circuit's fixed columns, by its index.
    columns: Vec<FixedColumns>,
    /// The dense polynomials the root's claims are settled against.
    tables: DenseTables,
}

/// A proof made by one node of a tree, the root's included.
///
/// A first-level node's proof covers leaf proofs.
///
/// A higher node's proof covers tree proofs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TreeProof {
    /// The kind of the circuit that made it, its statement's first word: its index within its tier, the tier above.
    circuit: usize,
    /// Its statement's words.
    words: Vec<F192>,
    /// The recursion proof.
    proof: ProofTranscript,
    /// The rate it is proven at.
    rate: Rate,
}

/// A leaf of a claim-set tree: a RISC-V leaf proof, and the claim set whose digest's hash its output is.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClaimLeaf<'a> {
    /// The proof and its output.
    leaf: Leaf<'a>,
    /// The set it publishes.
    claims: &'a ClaimSet,
}

/// A proof of a claim-set tree and the set it declares: what one party hands another to combine.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Aggregate {
    /// The proof.
    pub proof: TreeProof,
    /// The set its statement's digest is of.
    pub claims: ClaimSet,
}

/// A claim of a root's statement that is false.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum FalseClaim {
    /// A claim on a dense polynomial.
    #[error("on {0:?}")]
    Dense(DensePoly),
    /// A claim on a flock circuit's matrices.
    #[error("on the {table} table's {part:?} circuit's matrices")]
    Matrix {
        /// The table.
        table: &'static str,
        /// Which of its circuits.
        part: Part,
    },
}

/// Why a tree cannot be built, a tree proof cannot be made, or a root is refused.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum TreeError {
    /// The arities make no tree: a first level takes at least one leaf, a node at least two children.
    #[error("a first level of {arity_0} leaves and nodes of {arity} children make no tree")]
    Arity {
        /// The leaves a first-level node verifies.
        arity_0: usize,
        /// The children a node verifies.
        arity: usize,
    },
    /// A small tier past the tree's: an arity outside two to the tree's, or a capacity past the tree's.
    #[error("a small tier of {arity} children and {capacity:?} does not fit within the tree's")]
    SmallTier {
        /// Its arity.
        arity: usize,
        /// Its capacity.
        capacity: Capacity,
    },
    /// A claim-set tree whose leaves are proofs of a recursion circuit: a claim-set tree's leaves are RISC-V proofs.
    #[error("a claim-set tree's leaves are RISC-V proofs")]
    CircuitClaims,
    /// No RISC-V proof of the program has the leaves' shape.
    #[error("the leaves' shape: {0}")]
    LeafShape(VerifyError),
    /// No recursion circuit of the shapes fits one commitment.
    #[error("the tree's circuits fit no commitment")]
    TooLarge,
    /// A node is given the wrong number of proofs.
    #[error("a node of {expected} children is given {got}")]
    Children {
        /// The node's arity.
        expected: usize,
        /// How many it is given.
        got: usize,
    },
    /// A number of leaves no balanced tree of these arities has.
    #[error("{leaves} leaves make no tree of a first level of {arity_0} and nodes of {arity}")]
    LeafCount {
        /// How many leaves.
        leaves: usize,
        /// The first level's arity.
        arity_0: usize,
        /// The nodes' arity.
        arity: usize,
    },
    /// A leaf of another family or shape than the tree's.
    #[error("leaf {index} is of another family or shape than the tree's")]
    ForeignLeaf {
        /// The leaf's index among its node's.
        index: usize,
    },
    /// A leaf proof does not verify.
    #[error("leaf {index}: {error}")]
    Leaf {
        /// The leaf's index among its node's.
        index: usize,
        /// Why its verifier refuses it.
        error: VerifyError,
    },
    /// A child proof does not verify.
    #[error("child {index}: {error}")]
    Child {
        /// The child's index among its node's.
        index: usize,
        /// Why its verifier refuses it.
        error: VerifyError,
    },
    /// The circuit's rows do not hold on the prover's values.
    #[error("the circuit does not hold: {0}")]
    Unsatisfied(Unsatisfied),
    /// A proof at another rate than the tree's.
    #[error(
        "a proof at log-inv-rate {}, and the tree's is {}",
        .got.log_inv_rate(),
        .expected.log_inv_rate()
    )]
    Rate {
        /// The tree's.
        expected: Rate,
        /// The proof's.
        got: Rate,
    },
    /// The root is not of the kind the expected tree's top gives.
    #[error("the expected tree has a {expected:?} root, and the proof is a {got:?}")]
    Kind {
        /// The kind the expected tree gives.
        expected: Kind,
        /// The proof's.
        got: Kind,
    },
    /// The root's recursion proof does not verify.
    #[error("the root: {0}")]
    Root(VerifyError),
    /// The root's digest is not that of the expected tree.
    #[error("the root does not state the expected tree's leaves")]
    Digest,
    /// A claim the root carries is false.
    #[error("the root's claim {0} is false")]
    Claim(FalseClaim),
    /// An operation of the other semantics: positional proving or verifying on a claim-set tree, or the reverse.
    #[error("the tree is {}", if *.claims { "a claim-set tree" } else { "a tree of outputs" })]
    Semantics {
        /// Whether the tree is a claim-set tree.
        claims: bool,
    },
    /// A proof of no circuit of the tree.
    #[error("a proof of kind {0}, which the tree has no circuit of")]
    Circuit(usize),
    /// A leaf's output is not the hash of its claim set's digest.
    #[error("leaf {index}'s output is not its claim set's")]
    LeafClaims {
        /// The leaf's index among its node's.
        index: usize,
    },
    /// A child's statement is not of the claim set given with it.
    #[error("child {index}'s statement is not of its claim set")]
    ChildClaims {
        /// The child's index among its node's.
        index: usize,
    },
    /// The children's sets, or the declared set, do not fit the tree's capacity.
    #[error("the claim sets do not fit the tree's capacity")]
    Capacity,
    /// A declared claim no child carries.
    #[error("the declared claim {0:?} is not covered by the children")]
    NotCovered(Claim),
    /// A declared or root set that is not canonical, or past the capacity.
    #[error("the claim set: {0}")]
    ClaimSet(ClaimSetError),
    /// The root does not state this claim set.
    #[error("the root does not state this claim set")]
    Claims,
}

impl LeafShape {
    /// The shape of proofs with these table heights at this rate.
    pub(crate) const fn new(taus: PerTable<usize>, rate: Rate) -> Self {
        Self { taus, rate }
    }

    /// The shape a proof announces.
    ///
    /// # Errors
    ///
    /// A proof whose announcement is not valid.
    pub fn of(proof: &Proof) -> Result<Self, DecodeError> {
        Self::announced(proof).ok_or(DecodeError::Malformed)
    }

    /// The shape a proof of a run would announce, from the run's measured cost.
    ///
    /// So a tree's key is built before any leaf is proven.
    #[must_use]
    pub fn measured(stats: &Stats, rate: Rate) -> Self {
        // Every proven table height is a power of two, so its logarithm is exact.
        Self::new(stats.counts.map(|rows| rows.ilog2() as usize), rate)
    }

    /// The shape a proof's first scalars announce, if they are a valid announcement.
    fn announced(proof: &Proof) -> Option<Self> {
        let mut narg = proof.0.narg.as_slice();
        let scalars: [F192; Announcement::LEN] =
            std::array::from_fn(|_| F192::from_narg(&mut narg).unwrap_or_default());
        let announcement = Announcement::decode(&scalars).ok()?;
        Some(Self::new(announcement.taus, announcement.rate))
    }
}

/// The digest a first-level node binds a leaf circuit's statement by: the first 32 bytes its proof's transcript would squeeze after the session and the instance.
///
/// A leaf's verifier rows draw it from their transcript once it has absorbed the instance (`Transcript::digest_so_far`).
fn instance_digest(session: &SessionId, statement: &[Limbs]) -> Limbs {
    let mut ps = ProverState::new(session, &instance(statement));
    digest_limbs(&ps.verifier_message::<[u8; 32]>())
}

impl<'p> LeafCircuit<'p> {
    /// The leaf circuit of a circuit, its fixed columns at its heights, its proofs' session and rate.
    pub(crate) const fn new(circuit: &'p Circuit, columns: &'p FixedColumns, session: SessionId, rate: Rate) -> Self {
        Self {
            circuit,
            columns,
            session,
            rate,
        }
    }

    /// Its session, as words.
    pub(crate) fn seed(&self) -> Limbs {
        digest_limbs(&self.session.0)
    }
}

impl TreeShape {
    /// The levels of nodes of the balanced tree over this many leaves: zero for a first-level node over `n_0`, `d` over `n_0 n^d`.
    ///
    /// # Errors
    ///
    /// A number of leaves no tree of these arities has.
    pub fn depth(&self, leaves: usize) -> Result<usize, TreeError> {
        let Self { arity_0, arity, .. } = *self;
        let count = TreeError::LeafCount { leaves, arity_0, arity };
        if leaves == 0 || arity_0 == 0 || arity < 2 || !leaves.is_multiple_of(arity_0) {
            return Err(count);
        }
        let (mut nodes, mut depth) = (leaves / arity_0, 0);
        while nodes > 1 && nodes.is_multiple_of(arity) {
            nodes /= arity;
            depth += 1;
        }
        if nodes == 1 { Ok(depth) } else { Err(count) }
    }
}

impl ClaimShape {
    /// One tier at the tree's capacity: every circuit at the largest node's heights.
    #[must_use]
    pub const fn new(capacity: Capacity) -> Self {
        Self { capacity, small: None }
    }

    /// The capacity of a tier's unions.
    pub(crate) const fn tier_capacity(&self, tier: usize) -> Capacity {
        match (tier, self.small) {
            (design::SMALL, Some(small)) => small.capacity,
            _ => self.capacity,
        }
    }

    /// The tiers it has.
    const fn tiers(&self) -> usize {
        if self.small.is_some() { 2 } else { 1 }
    }
}

impl<'a> Leaf<'a> {
    /// The leaf of a RISC-V proof and the output it proves.
    #[must_use]
    pub const fn new(proof: &'a Proof, output: Output) -> Self {
        Self(LeafProof::Run { proof, output })
    }

    /// The leaf of a proof of a leaf circuit at `rate`, and the statement it proves.
    pub(crate) const fn circuit(
        leaf: &LeafCircuit<'_>,
        statement: Vec<Limbs>,
        proof: &'a ProofTranscript,
        rate: Rate,
    ) -> Self {
        Self(LeafProof::Circuit {
            session: leaf.session,
            statement,
            proof,
            rate,
        })
    }

    /// What it states.
    #[must_use]
    pub fn statement(&self) -> LeafStatement {
        LeafStatement(match &self.0 {
            LeafProof::Run { output, .. } => Stated::Run(*output),
            LeafProof::Circuit { session, statement, .. } => Stated::Circuit {
                session: *session,
                words: statement.clone(),
            },
        })
    }
}

impl<'a> From<&'a ProvenRun> for Leaf<'a> {
    fn from(run: &'a ProvenRun) -> Self {
        Self::new(&run.proof, run.output)
    }
}

impl LeafStatement {
    /// The statement of a proof of a leaf circuit.
    pub(crate) const fn circuit(leaf: &LeafCircuit<'_>, words: Vec<Limbs>) -> Self {
        Self(Stated::Circuit {
            session: leaf.session,
            words,
        })
    }
}

impl From<Output> for LeafStatement {
    fn from(output: Output) -> Self {
        Self(Stated::Run(output))
    }
}

impl Subtree {
    /// The balanced tree over these leaves, in order: first-level nodes of `arity_0` consecutive leaves, then nodes of `arity` consecutive children up to one root.
    ///
    /// # Errors
    ///
    /// A number of leaves no tree of the shape's arities has.
    pub fn balanced(leaves: Vec<LeafStatement>, shape: &TreeShape) -> Result<Self, TreeError> {
        shape.depth(leaves.len())?;
        let mut level: Vec<Self> = groups(leaves, shape.arity_0).into_iter().map(Self::First).collect();
        while level.len() > 1 {
            level = groups(level, shape.arity).into_iter().map(Self::Node).collect();
        }
        Ok(level.pop().expect("one root"))
    }
}

/// The items in consecutive groups of `n`, the last one shorter if they do not divide.
fn groups<T>(items: Vec<T>, n: usize) -> Vec<Vec<T>> {
    let mut items = items.into_iter().peekable();
    let mut out = Vec::new();
    while items.peek().is_some() {
        out.push(items.by_ref().take(n).collect());
    }
    out
}

impl TreeProof {
    /// The header of a tree proof's bytes: the magic `LVMT`, then the tree protocol's version.
    ///
    /// The version is bumped by every change to what a tree proof says.
    const ENVELOPE: Envelope = Envelope::new(*b"LVMT", 19);

    /// The kind of node that made the proof.
    #[must_use]
    pub const fn kind(&self) -> Kind {
        if self.circuit == 0 { Kind::First } else { Kind::Node }
    }

    /// The proof's bytes.
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        Self::ENVELOPE.seal(&self.body())
    }

    /// The tree proof these bytes encode.
    ///
    /// # Errors
    ///
    /// - Bytes that are no tree proof.
    /// - A tree proof of another protocol version.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        // The header first: a foreign version is refused before its body is read.
        let body = Self::ENVELOPE.open(bytes)?;
        Self::from_body(body).ok_or(DecodeError::Malformed)
    }

    /// The body behind the header: its rate, its statement's words, then the recursion proof.
    ///
    /// ```text
    /// | log_inv_rate: u8 | n_words: u32 | words: 24 bytes each | proof |
    /// ```
    fn body(&self) -> Vec<u8> {
        let n_words = u32::try_from(self.words.len()).expect("a statement of a few hundred words");
        let mut bytes = vec![self.rate.log_inv_rate()];
        bytes.extend(n_words.to_le_bytes());
        for w in &self.words {
            bytes.extend([w.c0, w.c1, w.c2].iter().flat_map(|l| l.to_le_bytes()));
        }
        bytes.extend(self.proof.to_bytes());
        bytes
    }

    /// The tree proof a body encodes, if it encodes one and nothing more.
    fn from_body(bytes: &[u8]) -> Option<Self> {
        let (&rate, rest) = bytes.split_first()?;
        let (n_words, rest) = rest.split_first_chunk::<4>()?;
        let n_words = usize::try_from(u32::from_le_bytes(*n_words)).ok()?;
        let (words, proof) = rest.split_at_checked(n_words.checked_mul(24)?)?;
        let words: Vec<F192> = (words.as_chunks::<24>().0.iter())
            .map(|w| {
                let limb = |i: usize| u64::from_le_bytes(w[8 * i..8 * i + 8].try_into().expect("eight bytes"));
                F192::new(limb(0), limb(1), limb(2))
            })
            .collect();
        let first = words.first()?;
        if (first.c1, first.c2) != (0, 0) {
            return None;
        }
        Some(Self {
            circuit: usize::try_from(first.c0).ok()?,
            words,
            proof: ProofTranscript::from_bytes(proof)?,
            rate: Rate::new(rate).ok()?,
        })
    }
}

impl<'a> ClaimLeaf<'a> {
    /// The leaf of a proof whose output is the hash of this set's digest, as a guest that commits the digest gives.
    #[must_use]
    pub const fn new(leaf: Leaf<'a>, claims: &'a ClaimSet) -> Self {
        Self { leaf, claims }
    }
}

impl<'p> Tree<'p> {
    /// The tree over leaves of this family, shaped as given.
    ///
    /// The circuits are built from the family and the shape alone, so a verifier needs no proof to build its key.
    ///
    /// # Errors
    ///
    /// - Arities that make no tree: a first level of no leaf, or nodes of fewer than two children.
    /// - A small tier past the tree's.
    /// - A claim-set tree over proofs of a recursion circuit.
    /// - A leaf shape no proof of the program has.
    /// - Circuits that fit no commitment.
    pub fn new(leaves: Leaves<'p>, shape: TreeShape) -> Result<Self, TreeError> {
        let TreeShape {
            arity_0,
            arity,
            rate,
            claims,
        } = shape;
        if arity_0 == 0 || arity < 2 {
            return Err(TreeError::Arity { arity_0, arity });
        }
        if let Some(ClaimShape {
            capacity: large,
            small: Some(Tier { arity: a, capacity }),
        }) = claims
            && (!(2..=arity).contains(&a) || capacity.claims > large.claims || capacity.groups > large.groups)
        {
            return Err(TreeError::SmallTier { arity: a, capacity });
        }
        if claims.is_some() && matches!(leaves, Leaves::Circuit(_)) {
            return Err(TreeError::CircuitClaims);
        }
        let tiers = claims.map_or(1, |c| c.tiers());
        let family = || match leaves {
            Leaves::Runs { program, shape } => ProofShape::new(program, shape.taus, shape.rate)
                .map(Family::Runs)
                .map_err(|e| TreeError::LeafShape(e.into())),
            Leaves::Circuit(c) => CircuitFamily::new(c).map(Family::Circuit),
        };
        let design = |taus: &[Heights]| Design::new(family()?, arity_0, arity, rate, claims, taus);
        let (design, circuits) = Self::converge(tiers, design)?;
        let columns: Vec<FixedColumns> = (circuits.iter().zip(&design.places))
            .map(|(c, p)| FixedColumns::of(c, &design.tiers[p.tier].taus))
            .collect();
        let tables = design.tables(&columns);
        Ok(Self {
            shape,
            design,
            circuits,
            columns,
            tables,
        })
    }

    /// Each tier's heights, which its circuits share, and the circuits at them, by their position.
    ///
    /// They are the least fixed point of `tau -> max(tau, each of a tier's circuits' heights at tau)`, every tier
    /// from the first-level circuit's own heights: a small tier's wrap verifies the large tier's proofs, and the large
    /// tier's nodes the small tier's, so the tiers' heights are found together. A table is absent from a tier's
    /// heights, its height none, only while all the tier's circuits lack it.
    ///
    /// Each round only raises heights, and a node's rows grow with the logarithm of its children's, so few rounds reach it.
    fn converge(
        tiers: usize,
        design: impl Fn(&[Heights]) -> Result<Design<'p>, TreeError>,
    ) -> Result<(Design<'p>, Vec<Circuit>), TreeError> {
        let max = |taus: Heights, built: &[Circuit]| {
            Heights::from_fn(|t| built.iter().map(|c| c.heights()[t]).fold(taus[t], Option::max))
        };
        // The first-level circuit does not depend on the heights: those of a circuit of no rows build it.
        let empty = Heights::from_fn(|t: Table| t.height_log(0));
        let start = design(&vec![empty; tiers])?.shape(0).circuit.heights();
        let mut taus = vec![start; tiers];
        for _ in 0..MAX_ROUNDS {
            let d = design(&taus)?;
            let built: Vec<Circuit> = (0..d.places.len()).map(|p| d.shape(p).circuit).collect();
            let next: Vec<Heights> = (d.tiers.iter().zip(&taus))
                .map(|(tier, &taus)| max(taus, &built[tier.places.clone()]))
                .collect();
            if next == taus {
                let circuits = (built.into_iter().zip(&d.places))
                    .map(|(mut c, p)| {
                        c.floor = taus[p.tier];
                        c
                    })
                    .collect();
                for &t in &taus {
                    RecLayout::from_taus(t).map_err(|_| TreeError::TooLarge)?;
                }
                return Ok((d, circuits));
            }
            taus = next;
        }
        Err(TreeError::TooLarge)
    }

    /// The circuit at this position.
    pub(crate) fn circuit(&self, position: usize) -> &Circuit {
        &self.circuits[position]
    }

    /// The position of the circuit of a kind: the first level's, or of a claim-set tree's nodes, the one of the largest
    /// arity.
    const fn position_of(&self, kind: Kind) -> usize {
        match kind {
            Kind::First => 0,
            Kind::Node => self.design.places.len() - 1,
        }
    }

    /// The circuit of a kind as `CheckRec` reads it: the builder calls that make it, one per line, then `circuit` and the circuit's dump, then `next` and the bus's `next` key of every slot of the circuit's rows, per table, row-major.
    ///
    /// # Panics
    ///
    /// Panics if building the circuit again gives another circuit.
    #[cfg(feature = "circuit-trace")]
    pub fn circuit_dump(&self, kind: Kind) -> String {
        let position = self.position_of(kind);
        let (finished, calls) = crate::rec::circuit::traced(|| self.design.shape(position));
        let mut circuit = finished.circuit;
        circuit.floor = self.circuit(position).floor;
        assert_eq!(
            &circuit,
            self.circuit(position),
            "a circuit is built the same every time"
        );
        calls + "circuit\n" + &circuit.dump() + &self.columns[position].dump_next(&circuit)
    }

    /// The capacity of a claim-set tree's largest nodes and roots, or why this tree has none.
    fn capacity(&self) -> Result<Capacity, TreeError> {
        (self.design.claims.map(|c| c.capacity)).ok_or(TreeError::Semantics { claims: false })
    }

    /// Nothing, if this is a tree of outputs.
    const fn outputs(&self) -> Result<(), TreeError> {
        match self.design.claims {
            Some(_) => Err(TreeError::Semantics { claims: true }),
            None => Ok(()),
        }
    }

    /// The position of a proof's circuit, if it is of one of the tree's circuits and states as many words as its
    /// statements have.
    fn known(&self, p: &TreeProof) -> Result<usize, TreeError> {
        match self.design.position(p.circuit) {
            Some(position) if p.words.len() == self.design.statement.len() => Ok(position),
            _ => Err(TreeError::Circuit(p.circuit)),
        }
    }

    /// Prove a first-level node over its leaves, in order.
    ///
    /// # Errors
    ///
    /// A tree of outputs only. The wrong number of leaves, a leaf of another family or shape than the tree's, or a leaf
    /// that does not verify.
    pub fn prove_first(&self, leaves: &[Leaf<'_>]) -> Result<TreeProof, TreeError> {
        self.outputs()?;
        let d = &self.design;
        let leaves: Vec<&Leaf<'_>> = leaves.iter().collect();
        let rows = match &d.family {
            Family::Runs(shape) => {
                let items = self.leaf_witnesses(shape, &leaves, |_, _| Ok([0; 4]))?;
                let inputs = NodeInputs::Prove {
                    items: &items,
                    tables: &self.tables,
                    union: None,
                };
                info_span!("Build circuit").in_scope(|| d.first_runs(shape, &inputs))
            }
            Family::Circuit(family) => {
                let items = self.circuit_witnesses(family, &leaves)?;
                let inputs = NodeInputs::Prove {
                    items: &items,
                    tables: &self.tables,
                    union: None,
                };
                info_span!("Build circuit").in_scope(|| d.first_circuit(family, &inputs))
            }
        };
        self.prove_rows(rows, 0)
    }

    /// Nothing, if a first-level node is given as many leaves as it verifies.
    const fn leaf_count(&self, got: usize) -> Result<(), TreeError> {
        let expected = self.design.arity_0;
        if got == expected {
            Ok(())
        } else {
            Err(TreeError::Children { expected, got })
        }
    }

    /// The first level's witnesses of its RISC-V leaves of this shape, each verified natively; `claims` gives a leaf's
    /// set's digest from its index and output.
    fn leaf_witnesses<'a>(
        &self,
        shape: &ProofShape<'_>,
        leaves: &[&Leaf<'a>],
        claims: impl Fn(usize, &Output) -> Result<[u64; 4], TreeError>,
    ) -> Result<Vec<LeafWitness<'a>>, TreeError> {
        self.leaf_count(leaves.len())?;
        let announced = LeafShape::new(*shape.taus(), shape.rate());
        let program = shape.program();
        (leaves.iter().enumerate())
            .map(|(index, leaf)| {
                let LeafProof::Run { proof, output } = leaf.0 else {
                    return Err(TreeError::ForeignLeaf { index });
                };
                if LeafShape::announced(proof) != Some(announced) {
                    return Err(TreeError::ForeignLeaf { index });
                }
                let claims = claims(index, &output)?;
                let openings =
                    (program.verify_recording(output, proof)).map_err(|error| TreeError::Leaf { index, error })?;
                Ok(LeafWitness {
                    proof: &proof.0,
                    openings,
                    output: *output.words(),
                    set: claims,
                })
            })
            .collect()
    }

    /// The first level's witnesses of its leaves of the leaf circuit, each verified natively.
    fn circuit_witnesses<'a>(
        &self,
        family: &CircuitFamily<'a>,
        leaves: &[&Leaf<'a>],
    ) -> Result<Vec<CircuitWitness<'a>>, TreeError> {
        self.leaf_count(leaves.len())?;
        let c = &family.leaf;
        (leaves.iter().enumerate())
            .map(|(index, leaf)| {
                let LeafProof::Circuit {
                    session,
                    ref statement,
                    proof,
                    rate,
                } = leaf.0
                else {
                    return Err(TreeError::ForeignLeaf { index });
                };
                let words = statement.len() == c.circuit.statement_len && statement.iter().all(|w| w[3] == 0);
                if session != c.session || rate != c.rate || !words {
                    return Err(TreeError::ForeignLeaf { index });
                }
                let openings =
                    (c.circuit.verify_with(statement, &c.session, c.rate, proof, c.columns)).map_err(|error| {
                        TreeError::Leaf {
                            index,
                            error: error.into(),
                        }
                    })?;
                Ok(CircuitWitness {
                    statement: statement.clone(),
                    proof,
                    openings,
                    columns: c.columns,
                })
            })
            .collect()
    }

    /// The node's witnesses of its children, proofs of `tier`, each verified natively, short of its claims.
    fn child_witnesses<'a>(
        &'a self,
        tier: usize,
        children: &[&'a TreeProof],
        statements: &'a [TreeStatement],
    ) -> Result<Vec<ChildWitness<'a>>, TreeError> {
        (children.iter().zip(statements).enumerate())
            .map(|(index, (c, statement))| {
                let position = self.known(c)?;
                if self.design.places[position].tier != tier {
                    return Err(TreeError::Circuit(c.circuit));
                }
                let openings = self
                    .read(c, position)
                    .map_err(|error| TreeError::Child { index, error })?;
                Ok(ChildWitness {
                    statement,
                    proof: &c.proof,
                    openings,
                    columns: &self.columns[position],
                })
            })
            .collect()
    }

    /// Prove a node over its children, tree proofs of either kind, in order.
    ///
    /// A child is verified under the tree's session, which names the tree's leaf family: a tree proof of another tree is refused as a child that does not verify.
    ///
    /// # Errors
    ///
    /// A tree of outputs only. The wrong number of children, or a child that does not verify.
    pub fn prove_node(&self, children: &[TreeProof]) -> Result<TreeProof, TreeError> {
        self.outputs()?;
        let d = &self.design;
        if children.len() != d.arity {
            return Err(TreeError::Children {
                expected: d.arity,
                got: children.len(),
            });
        }
        let children: Vec<&TreeProof> = children.iter().collect();
        children.iter().try_for_each(|c| self.known(c).map(drop))?;
        let statements: Vec<TreeStatement> = (children.iter())
            .map(|c| TreeStatement::new(d.statement, c.words.clone()))
            .collect();
        let items = self.child_witnesses(SMALL, &children, &statements)?;
        let inputs = NodeInputs::Prove {
            items: &items,
            tables: &self.tables,
            union: None,
        };
        let rows = info_span!("Build circuit").in_scope(|| d.node(&inputs, 1));
        self.prove_rows(rows, 1)
    }

    /// Prove a first-level node of a claim-set tree over its leaves, in order, declaring `declare`, by default the
    /// union of the leaves' sets.
    ///
    /// # Errors
    ///
    /// - A tree of outputs.
    /// - The wrong number of leaves, a leaf of another shape, a leaf that does not verify, or one whose output is not
    ///   its set's.
    /// - A declared set that is not canonical, past the capacity, or with a claim no leaf carries.
    /// - Leaves whose sets together do not fit the first level's capacity: the small tier's, if the tree has one.
    pub fn aggregate_leaves(
        &self,
        leaves: &[ClaimLeaf<'_>],
        declare: Option<&ClaimSet>,
    ) -> Result<Aggregate, TreeError> {
        self.capacity()?;
        let Family::Runs(shape) = &self.design.family else {
            unreachable!("a claim-set tree's leaves are RISC-V proofs");
        };
        let digests: Vec<[u64; 4]> = leaves.iter().map(|l| l.claims.digest()).collect();
        let plain: Vec<&Leaf<'_>> = leaves.iter().map(|l| &l.leaf).collect();
        let items = self.leaf_witnesses(shape, &plain, |index, output| {
            // The guest commits the digest, so its output is the digest's hash.
            if *output.words() == chain(&digests[index]) {
                Ok(digests[index])
            } else {
                Err(TreeError::LeafClaims { index })
            }
        })?;
        let sets: Vec<&ClaimSet> = leaves.iter().map(|l| l.claims).collect();
        let (union, claims) = self.fill(0, &sets, declare)?;
        let inputs = NodeInputs::Prove {
            items: &items,
            tables: &self.tables,
            union: Some(&union),
        };
        let rows = info_span!("Build circuit").in_scope(|| self.design.first_runs(shape, &inputs));
        let proof = self.prove_rows(rows, 0)?;
        Ok(Aggregate { proof, claims })
    }

    /// Prove a node of a claim-set tree over any of its proofs, from one to the tree's arity, each with the set it
    /// declares, declaring `declare`, by default the union of their sets.
    ///
    /// The children may be of any kind and any provers'. A node's places past its children verify the first child again
    /// and are absent: their sets are read as the empty set. So a lone child is taken once, by a node of two, which
    /// narrows or republishes it whatever the size of its set within the capacity.
    ///
    /// In a tree of two tiers, the node is the small tier's if the children are few enough and their sets and the
    /// declared set fit its capacity, else the large tier's one node. A child of the large tier is wrapped first, a
    /// proof of its own.
    ///
    /// # Errors
    ///
    /// - A tree of outputs.
    /// - No child, or more than the arity; a child that does not verify, or whose statement is not of its set.
    /// - A declared set that is not canonical, past the capacity, or with a claim no child carries.
    /// - Children whose sets together do not fit the capacity.
    pub fn aggregate(&self, children: &[&Aggregate], declare: Option<&ClaimSet>) -> Result<Aggregate, TreeError> {
        self.capacity()?;
        let d = &self.design;
        let n = children.len();
        // A lone child is taken by a node of two, its other place absent.
        let small = d.place(SMALL, Level::Node(n.max(2))).map(|p| (p, n.max(2)));
        let large = d.place(LARGE, Level::Node(d.arity)).map(|p| (p, d.arity));
        if n == 0 || n > d.arity || (small.is_none() && large.is_none()) {
            return Err(TreeError::Children {
                expected: d.arity,
                got: n,
            });
        }
        let mut wraps = Vec::with_capacity(n);
        for (index, c) in children.iter().enumerate() {
            let position = self.known(&c.proof)?;
            wraps.push(
                (d.places[position].tier == LARGE)
                    .then(|| self.wrap(index, c))
                    .transpose()?,
            );
        }
        let children: Vec<&Aggregate> = (children.iter().zip(&wraps))
            .map(|(&c, w)| w.as_ref().unwrap_or(c))
            .collect();
        let proofs: Vec<&TreeProof> = children.iter().map(|c| &c.proof).collect();
        let statements: Vec<TreeStatement> = (proofs.iter())
            .map(|c| TreeStatement::new(d.statement, c.words.clone()))
            .collect();
        let items = self.child_witnesses(SMALL, &proofs, &statements)?;
        if let Some(index) = (statements.iter().zip(&children)).position(|(s, c)| s.digest_words() != c.claims.digest())
        {
            return Err(TreeError::ChildClaims { index });
        }
        let sets: Vec<&ClaimSet> = children.iter().map(|c| &c.claims).collect();
        // The first tier whose union holds the sets. A place past the children verifies the first child again, absent
        // from the union.
        for (position, slots) in small.into_iter().chain(large) {
            let (union, claims) = match self.fill(position, &sets, declare) {
                Err(TreeError::Capacity) => continue,
                filled => filled?,
            };
            let slot_items: Vec<ChildWitness<'_>> = (0..slots)
                .map(|i| {
                    let w = &items[if i < n { i } else { 0 }];
                    ChildWitness {
                        statement: w.statement,
                        proof: w.proof,
                        openings: w.openings.clone(),
                        columns: w.columns,
                    }
                })
                .collect();
            let inputs = NodeInputs::Prove {
                items: &slot_items,
                tables: &self.tables,
                union: Some(&union),
            };
            let rows = info_span!("Build circuit").in_scope(|| d.node(&inputs, position));
            let proof = self.prove_rows(rows, position)?;
            return Ok(Aggregate { proof, claims });
        }
        Err(TreeError::Capacity)
    }

    /// Wrap child `index`, a proof of the large tier: a proof of the small tier stating its set.
    fn wrap(&self, index: usize, child: &Aggregate) -> Result<Aggregate, TreeError> {
        let d = &self.design;
        let position = (d.place(SMALL, Level::Wrap)).expect("a tree of two tiers wraps");
        let statements = [TreeStatement::new(d.statement, child.proof.words.clone())];
        let items = (self.child_witnesses(LARGE, &[&child.proof], &statements)).map_err(|e| match e {
            TreeError::Child { error, .. } => TreeError::Child { index, error },
            e => e,
        })?;
        if statements[0].digest_words() != child.claims.digest() {
            return Err(TreeError::ChildClaims { index });
        }
        let inputs = NodeInputs::Prove {
            items: &items,
            tables: &self.tables,
            union: None,
        };
        let rows = info_span!("Build circuit").in_scope(|| d.node(&inputs, position));
        let proof = self.prove_rows(rows, position)?;
        Ok(Aggregate {
            proof,
            claims: child.claims.clone(),
        })
    }

    /// The union's values over these sets in the circuit at `position`, and the set it declares: `declare`, or the
    /// canonical union, which must fit the circuit's tier's capacity.
    fn fill(
        &self,
        position: usize,
        sets: &[&ClaimSet],
        declare: Option<&ClaimSet>,
    ) -> Result<(UnionFill, ClaimSet), TreeError> {
        let capacity = self.capacity()?;
        let declared = match declare {
            Some(set) => {
                set.check(capacity).map_err(TreeError::ClaimSet)?;
                set.clone()
            }
            None => {
                let union = ClaimSet::from_claims(sets.iter().flat_map(|s| s.claims()));
                union.check(capacity).map_err(|_| TreeError::Capacity)?;
                union
            }
        };
        let tier = self.design.places[position].tier;
        let held = (self.design.claims).map_or(capacity, |c| c.tier_capacity(tier));
        if declared.n_claims() >= held.claims || declared.groups.len() > held.groups {
            return Err(TreeError::Capacity);
        }
        let shape = self
            .design
            .union_shape(position)
            .expect("a claim-set tree's node has a union");
        let fill = UnionFill::new(&shape, sets, &declared).map_err(|e| match e {
            FillError::Children | FillError::Declared => TreeError::Capacity,
            FillError::NotCovered(claim) => TreeError::NotCovered(claim),
        })?;
        Ok((fill, declared))
    }

    /// Prove the balanced tree over its leaves, in order.
    ///
    /// The first level, then each level of nodes, up to the root.
    ///
    /// # Errors
    ///
    /// A tree of outputs only. A number of leaves no tree of the arities has, or a leaf the first level refuses.
    pub fn prove(&self, leaves: &[Leaf<'_>]) -> Result<TreeProof, TreeError> {
        self.outputs()?;
        self.shape.depth(leaves.len())?;
        let (arity_0, arity) = (self.design.arity_0, self.design.arity);
        let mut level: Vec<TreeProof> = (leaves.chunks(arity_0))
            .map(|leaves| self.prove_first(leaves))
            .collect::<Result<_, _>>()?;
        while level.len() > 1 {
            level = level
                .chunks(arity)
                .map(|c| self.prove_node(c))
                .collect::<Result<_, _>>()?;
        }
        Ok(level.pop().expect("one root"))
    }

    /// Verify a root: its recursion proof, that it covers the expected tree, and every claim it carries.
    ///
    /// # Errors
    ///
    /// A tree of outputs only. Returns the first check that refuses.
    #[tracing::instrument(name = "Verify tree", skip_all)]
    pub fn verify(&self, root: &TreeProof, expected: &Subtree) -> Result<(), TreeError> {
        self.outputs()?;
        let d = &self.design;
        if root.rate != d.rate {
            return Err(TreeError::Rate {
                expected: d.rate,
                got: root.rate,
            });
        }
        let (kind, digest) = self.expect(expected)?;
        if root.kind() != kind {
            return Err(TreeError::Kind {
                expected: kind,
                got: root.kind(),
            });
        }
        let position = self.known(root)?;
        self.read(root, position).map_err(TreeError::Root)?;
        let statement = TreeStatement::new(d.statement, root.words.clone());
        if statement.digest_words() != digest {
            return Err(TreeError::Digest);
        }
        self.settle(&statement, position)
    }

    /// Verify the root of a claim-set tree: its recursion proof, that its set is canonical and within the capacity,
    /// that it states this set, and every claim it carries.
    ///
    /// The root may be of any kind and either tier, made by anyone, over any shape of tree: the set is all its
    /// statement says.
    ///
    /// # Errors
    ///
    /// A tree of outputs. Otherwise the first check that refuses.
    #[tracing::instrument(name = "Verify claim-set tree", skip_all)]
    pub fn verify_claims(&self, root: &TreeProof, claims: &ClaimSet) -> Result<(), TreeError> {
        let capacity = self.capacity()?;
        let d = &self.design;
        if root.rate != d.rate {
            return Err(TreeError::Rate {
                expected: d.rate,
                got: root.rate,
            });
        }
        let position = self.known(root)?;
        claims.check(capacity).map_err(TreeError::ClaimSet)?;
        self.read(root, position).map_err(TreeError::Root)?;
        let statement = TreeStatement::new(d.statement, root.words.clone());
        if statement.digest_words() != claims.digest() {
            return Err(TreeError::Claims);
        }
        self.settle(&statement, position)
    }

    /// The kind and the digest of the root of an expected tree.
    fn expect(&self, tree: &Subtree) -> Result<(Kind, Limbs), TreeError> {
        let d = &self.design;
        let count = |expected, got| {
            (got == expected)
                .then_some(())
                .ok_or(TreeError::Children { expected, got })
        };
        match tree {
            Subtree::First(leaves) => {
                count(d.arity_0, leaves.len())?;
                let items = (leaves.iter().enumerate())
                    .map(|(index, l)| match (&d.family, &l.0) {
                        (Family::Runs(_), Stated::Run(output)) => Ok(*output.words()),
                        (Family::Circuit(c), Stated::Circuit { session, words }) if *session == c.leaf.session => {
                            Ok(instance_digest(session, words))
                        }
                        _ => Err(TreeError::ForeignLeaf { index }),
                    })
                    .collect::<Result<Vec<Limbs>, _>>()?;
                let under = match &d.family {
                    Family::Runs(_) => Items::Runs,
                    Family::Circuit(c) => Items::Circuit(c.leaf.seed()),
                };
                Ok((Kind::First, under.digest(&items)))
            }
            Subtree::Node(children) => {
                count(d.arity, children.len())?;
                let digests = (children.iter())
                    .map(|c| self.expect(c).map(|(_, digest)| digest))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok((Kind::Node, Items::Node.digest(&digests)))
            }
        }
    }

    /// Verify a tree proof's recursion proof, short of its claims, returning every opening it authenticated.
    ///
    /// The proof is of the tree's circuit at `position`.
    fn read(&self, p: &TreeProof, position: usize) -> Result<Vec<Openings>, VerifyError> {
        let limbs: Vec<[u64; 4]> = p.words.iter().map(|w| [w.c0, w.c1, w.c2, 0]).collect();
        self.circuit(position)
            .verify_with(
                &limbs,
                &self.design.session,
                self.design.rate,
                &p.proof,
                &self.columns[position],
            )
            .map_err(Into::into)
    }

    /// Prove the rows of the circuit at `position`: its reduction, then its recursion proof.
    fn prove_rows(&self, rows: NodeRows, position: usize) -> Result<TreeProof, TreeError> {
        let d = &self.design;
        let reduction = rows.claim_values().prove(&d.session, &d.vars, &self.tables);
        let Finished {
            assignment, failures, ..
        } = info_span!("Reduce in rows").in_scope(|| rows.reduce(d, ProofSource::Proof(&reduction, &[])));
        if let Some(first) = failures.into_iter().next() {
            return Err(TreeError::Unsatisfied(first));
        }
        let proof = (self.circuit(position))
            .prove_with(&assignment, &d.session, d.rate, Some(&self.columns[position]))
            .map_err(|_| TreeError::TooLarge)?;
        let words = (assignment.statement().iter())
            .map(|l| F192::new(l[0], l[1], l[2]))
            .collect();
        Ok(TreeProof {
            circuit: d.code(position),
            words,
            proof,
            rate: d.rate,
        })
    }

    /// Evaluate every claim a root's statement carries: each dense polynomial a proof of its circuit carries a claim on,
    /// and every flock circuit's matrices.
    #[tracing::instrument(name = "Settle claims", skip_all)]
    fn settle(&self, s: &TreeStatement, position: usize) -> Result<(), TreeError> {
        let d = &self.design;
        // A first-level node carries a claim only on a polynomial its leaves fix.
        let carried = |poly| position != 0 || d.leaves_fix(poly);
        for poly in d.statement.polys().filter(|&p| carried(p)) {
            let point = &s.dense_point()[..d.vars.0[poly as usize]];
            if mle_eval_par(&self.tables.0[poly as usize], point) != s.dense_value(poly) {
                return Err(TreeError::Claim(FalseClaim::Dense(poly)));
            }
        }
        let held = parallel::map_collect(FlockId::ALL.len(), |f| {
            let f = FlockId::ALL[f];
            let circuit = f.circuit();
            let k = circuit.k_log();
            let (ra, rb) = circuit.row_values(&eq_table(&s.cols()[..k]));
            let u = eq_table(&s.rows()[..k]);
            let dot = |r: &[F192]| u.iter().zip(r).fold(F192::ZERO, |acc, (&x, &y)| acc + x * y);
            [dot(&ra), dot(&rb)] == s.matrices(f)
        });
        (FlockId::ALL.into_iter().zip(held))
            .find(|&(_, h)| !h)
            .map_or(Ok(()), |(f, _)| {
                Err(TreeError::Claim(FalseClaim::Matrix {
                    table: f.table().name(),
                    part: f.part(),
                }))
            })
    }
}
