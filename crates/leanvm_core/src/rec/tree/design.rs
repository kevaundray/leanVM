//! The tree's two circuits, one per kind, and the heights they share.
//!
//! - A first-level node verifies leaves of the tree's one family, and reduces every claim they leave. RISC-V proofs of the program leave program claims, which become point claims on the bytecode table and the image; proofs of the leaf circuit leave hinted evaluations of that circuit's fixed columns, which become claims on the leaves' fixed polynomial.
//! - A node verifies tree proofs of either kind, and reduces their fresh claims with the claims they carry, each weighed by whether a child of its kind carries it.
//!
//! Both circuits have the same heights, so a node verifies a child of either kind with one set of rows.

use super::claims::{Bits, DenseClaim, DensePoly, DenseTerm, MatrixClaim, NodeClaims};
use super::fixed::{FixedLayout, side_by_side};
use super::reduce::{DenseTables, DenseVars, Reduced};
use super::statement::{Kind, Level, Section, StatementLayout, TreeStatement, digest_halves_rows};
use super::{LeafCircuit, TreeError, reduce};
use crate::class_flock::FlockId;
use crate::cpu::{Claim, Lookup, ProgramPoint};
use crate::leaf::N_TUPLE_BITS;
use crate::pcs::Rate;
use crate::rec::circuit::{Builder, Dw, Ew, Finished, Kw, Limbs};
use crate::rec::fixed::FixedColumns;
use crate::rec::table::{HashFlock, Heights};
use crate::rec::transcript::{ProofSource, Transcript};
use crate::rec::verifier::{FixedHint, ProofShape, RecShape, Rows, infallible};
use fiat_shamir::arith::Arith;
use fiat_shamir::{ProofTranscript, SessionId};
use pcs::merkle::Openings;

use pcs::ring_switch::inverse_frobenius_ladder;
use primitives::field::{F64, F192};
use primitives::multilinear::mle_eval_par;

/// The protocol half of every recursion proof's session tag.
const DOMAIN: &[u8] = b"leanvm-tree-13";

/// The tree's leaf family, as its circuits verify it.
pub(crate) enum Family<'p> {
    /// RISC-V proofs of one program, of one shape: the program, its tables' heights, its rate.
    Runs(ProofShape<'p>),
    /// Proofs of one recursion circuit.
    Circuit(CircuitFamily<'p>),
}

/// Proofs of one recursion circuit, as a first-level node verifies them.
pub(crate) struct CircuitFamily<'p> {
    /// The circuit, its fixed columns, its session and its proofs' rate.
    pub(crate) leaf: LeafCircuit<'p>,
    /// The shape of its proofs, at its own heights.
    shape: RecShape,
    /// Where each of its fixed columns sits in its stack, `W_leaf`.
    fixed: FixedLayout,
}

/// What fixes a tree's circuits: the leaf family, the arities, the rate, and the nodes' heights.
pub(crate) struct Design<'p> {
    /// The leaf family, which the first-level circuit verifies.
    pub(crate) family: Family<'p>,
    /// The leaves a first-level node verifies.
    pub(crate) arity_0: usize,
    /// The children a node verifies.
    pub(crate) arity: usize,
    /// Every tree proof's rate.
    pub(crate) rate: Rate,
    /// The nodes' heights, which both circuits share: a table is absent from them only if both circuits lack it.
    pub(crate) taus: Heights,
    /// The shape of a child recursion proof.
    child: RecShape,
    /// Where each fixed column sits in one kind's circuit's stack.
    pub(crate) fixed: FixedLayout,
    /// Each dense polynomial's variables.
    pub(crate) vars: DenseVars,
    /// Which dense polynomials the tree has.
    pub(crate) present: [bool; DensePoly::COUNT],
    /// Where each part of a statement sits.
    pub(crate) statement: StatementLayout,
    /// The transcript's session for every recursion proof of the tree.
    pub(crate) session: SessionId,
}

/// A leaf as a first-level node's prover holds it: its proof, which the native verifier accepted, and its output.
pub(crate) struct LeafWitness<'a> {
    /// The proof.
    pub(crate) proof: &'a ProofTranscript,
    /// Every opening its native verifier authenticated, phase by phase.
    pub(crate) openings: Vec<Openings>,
    /// The output it proves.
    pub(crate) output: [u64; 4],
}

/// A leaf of a recursion circuit as a first-level node's prover holds it: its statement, its proof, which the native verifier accepted, and its circuit's fixed columns.
pub(crate) struct CircuitWitness<'a> {
    /// What it states, word by word.
    pub(crate) statement: Vec<Limbs>,
    /// The proof.
    pub(crate) proof: &'a ProofTranscript,
    /// Every opening its native verifier authenticated, phase by phase.
    pub(crate) openings: Vec<Openings>,
    /// The fixed columns of its circuit.
    pub(crate) columns: &'a FixedColumns,
}

/// A child as a node's prover holds it: its statement, its proof, and its circuit's fixed columns.
pub(crate) struct ChildWitness<'a> {
    /// What it states.
    pub(crate) statement: &'a TreeStatement,
    /// The proof, which the native verifier accepted.
    pub(crate) proof: &'a ProofTranscript,
    /// Every opening its native verifier authenticated, phase by phase.
    pub(crate) openings: Vec<Openings>,
    /// The fixed columns of its circuit.
    pub(crate) columns: &'a FixedColumns,
}

/// What a circuit is built from: the shapes alone, or what a prover holds.
pub(crate) enum NodeInputs<'a, T> {
    /// No values: every proof read is zeros, and the rows are the circuit's.
    Shape,
    /// The verified proofs, and the dense polynomials the hints are evaluations of.
    Prove {
        /// The proofs, in order.
        items: &'a [T],
        /// The dense polynomials.
        tables: &'a DenseTables,
    },
}

/// A circuit's rows up to its reduction: they verify its proofs, and leave the claims the reduction takes.
pub(crate) struct NodeRows {
    /// The circuit so far, and its values.
    b: Builder,
    /// The circuit's kind.
    kind: Kind,
    /// The digest of what the leaves under it state.
    digest: Dw,
    /// The claims its rows leave.
    claims: NodeClaims<Ew>,
}

impl<'p> CircuitFamily<'p> {
    /// The family of a leaf circuit's proofs.
    ///
    /// # Errors
    ///
    /// A circuit whose heights admit no recursion proof.
    pub(crate) fn new(leaf: LeafCircuit<'p>) -> Result<Self, TreeError> {
        let taus = leaf.circuit.heights();
        Ok(Self {
            shape: RecShape::new(taus, leaf.rate).map_err(|_| TreeError::TooLarge)?,
            fixed: FixedLayout::new(&taus),
            leaf,
        })
    }

    /// The leaves' fixed polynomial `W_leaf` of the leaf circuit's fixed columns: its stack.
    pub(crate) fn leaf_polynomial(&self, columns: &FixedColumns) -> Vec<F64> {
        side_by_side([(&self.fixed, columns)], self.fixed.kappa(), 0)
    }
}

impl<T> NodeInputs<'_, T> {
    /// Proof `i`, when a prover holds it.
    const fn item(&self, i: usize) -> Option<&T> {
        match self {
            Self::Shape => None,
            Self::Prove { items, .. } => Some(&items[i]),
        }
    }

    /// A dense polynomial's value at a point, as a hint: only the prover's tables give it, zero from the shapes.
    fn hint(&self, b: &mut Builder, poly: DensePoly, point: &[Ew]) -> Ew {
        let value = match self {
            Self::Shape => F192::ZERO,
            Self::Prove { tables, .. } => {
                let at: Vec<F192> = point.iter().map(|&w| b.e(w)).collect();
                mle_eval_par(&tables.0[poly as usize], &at)
            }
        };
        b.free_e(value)
    }
}

impl NodeClaims<Ew> {
    /// Bind a verified proof's final transcript digest, as two scalars: its first three words, then its fourth.
    fn bind_state(&mut self, b: &mut Builder, state: Dw) {
        let [w0, w1, w2, w3] = b.d_to_k(state);
        self.bound.extend([b.k_to_e([w0, w1, w2]), b.k_to_e1(w3)]);
    }
}

impl<'p> Design<'p> {
    /// The design at the given heights of both circuits.
    ///
    /// # Errors
    ///
    /// Returns an error if the heights admit no recursion proof.
    pub(crate) fn new(
        family: Family<'p>,
        arity_0: usize,
        arity: usize,
        rate: Rate,
        taus: Heights,
    ) -> Result<Self, TreeError> {
        let child = RecShape::new(taus, rate).map_err(|_| TreeError::TooLarge)?;
        let fixed = FixedLayout::new(&taus);
        // The kind's one variable selects its circuit's stack in `W_node`.
        let node = fixed.kappa() + 1;
        let (present, vars) = match &family {
            Family::Runs(shape) => {
                let rv = shape.program().rv();
                let bytecode = crate::log2_strict_usize(rv.entries().len()) + N_TUPLE_BITS;
                let image = crate::log2_ceil_usize(rv.image().len().max(1));
                ([true, true, false, true], DenseVars([bytecode, image, 0, node]))
            }
            Family::Circuit(c) => ([false, false, true, true], DenseVars([0, 0, c.fixed.kappa(), node])),
        };
        let n_dense = (vars.0.iter().zip(present))
            .filter_map(|(&n, p)| p.then_some(n))
            .max()
            .unwrap_or(0);
        let mut design = Self {
            family,
            arity_0,
            arity,
            rate,
            taus,
            child,
            fixed,
            vars,
            present,
            statement: StatementLayout::new(n_dense, present),
            session: SessionId([0; 32]),
        };
        design.session = design.session();
        Ok(design)
    }

    /// The transcript's session: everything that fixes the circuits, as one tag.
    ///
    /// Both kinds share it.
    /// The kind is the statement's first word, and the statement is the transcript's instance.
    ///
    /// It names the leaf family: the program's digest, or the leaf circuit's session, statement length and heights, with the leaves' heights and rate. So a tree proof verifies only under a tree of its own leaf family.
    fn session(&self) -> SessionId {
        let mut tag = DOMAIN.to_vec();
        let word = |tag: &mut Vec<u8>, x: usize| tag.extend_from_slice(&(x as u64).to_le_bytes());
        // An absent table's height is a word no height is.
        let height = |tag: &mut Vec<u8>, tau: Option<usize>| word(tag, tau.unwrap_or(usize::MAX));
        match &self.family {
            Family::Runs(shape) => {
                tag.extend_from_slice(b"runs....");
                tag.extend_from_slice(shape.program().digest());
                shape.taus().values().for_each(|&t| word(&mut tag, t));
                tag.push(shape.rate().log_inv_rate());
            }
            Family::Circuit(c) => {
                tag.extend_from_slice(b"circuit.");
                tag.extend_from_slice(&c.leaf.session.0);
                word(&mut tag, c.leaf.circuit.statement_len);
                for t in c.leaf.circuit.heights().into_values() {
                    height(&mut tag, t);
                }
                tag.push(c.leaf.rate.log_inv_rate());
            }
        }
        for x in [self.arity_0, self.arity, self.statement.len()] {
            word(&mut tag, x);
        }
        for t in self.taus.into_values() {
            height(&mut tag, t);
        }
        tag.push(self.rate.log_inv_rate());
        SessionId::new(&tag)
    }

    /// Whether a proof of this kind carries a claim on the polynomial: a first-level node on those its leaves fix, a node on every one the tree has.
    pub(crate) fn active(&self, kind: Kind, poly: DensePoly) -> bool {
        self.present[poly as usize]
            && match kind {
                Kind::Node => true,
                Kind::First => match self.family {
                    Family::Runs(_) => matches!(poly, DensePoly::Bytecode | DensePoly::Image),
                    Family::Circuit(_) => poly == DensePoly::Leaf,
                },
            }
    }

    /// The nodes' fixed polynomial `W_node` of the two circuits' fixed columns, the first level's then the node's.
    pub(crate) fn node_polynomial(&self, columns: [&FixedColumns; 2]) -> Vec<F64> {
        side_by_side(columns.map(|c| (&self.fixed, c)), self.fixed.kappa(), 1)
    }

    /// The dense polynomials, of the two circuits' fixed columns, the first level's then the node's: a polynomial the tree lacks is the zero table of no variables.
    pub(crate) fn tables(&self, columns: [&FixedColumns; 2]) -> DenseTables {
        let none = || vec![F64::ZERO];
        let [bytecode, image, leaf] = match &self.family {
            Family::Runs(shape) => {
                let rv = shape.program().rv();
                let mut image: Vec<F64> = rv.image().iter().map(|&w| F64(w)).collect();
                image.resize(1 << self.vars.0[DensePoly::Image as usize], F64::ZERO);
                [Lookup::Bytecode.table(rv), image, none()]
            }
            Family::Circuit(c) => [none(), none(), c.leaf_polynomial(c.leaf.columns)],
        };
        DenseTables([bytecode, image, leaf, self.node_polynomial(columns)])
    }

    /// The first level's rows over RISC-V proofs, verifying its leaves.
    pub(crate) fn first_runs(&self, leaf: &ProofShape<'_>, inputs: &NodeInputs<'_, LeafWitness<'_>>) -> NodeRows {
        let mut b = Builder::new();
        let mut claims = NodeClaims::default();
        let mut outputs = Vec::with_capacity(self.arity_0);
        for i in 0..self.arity_0 {
            let item = inputs.item(i);
            let output = item.map_or([0; 4], |l| l.output).map(|o| b.free_k(o));
            let source = item.map_or(ProofSource::Shape, |l| ProofSource::Proof(l.proof, &l.openings));
            let core = b.scope(format!("leaf {i}"), |b| leaf.verify_core(b, output, source));
            claims.bind_state(&mut b, core.state);
            b.scope(format!("leaf {i} program"), |b| {
                self.program_claims(b, &core.claims.program, inputs, &mut claims);
            });
            let fresh = FlockId::ALL.into_iter().zip(&core.claims.circuits);
            claims.matrices.extend(fresh.map(|(f, c)| MatrixClaim::fresh(f, c)));
            outputs.push(output);
        }
        let digest = Level::Runs.digest_rows(&mut b, &outputs);
        NodeRows {
            b,
            kind: Kind::First,
            digest,
            claims,
        }
    }

    /// The first level's rows over proofs of a recursion circuit, verifying its leaves at the circuit's own heights, rate and session.
    ///
    /// Each leaf's statement is free wires, which its verifier's rows absorb as its transcript's instance; the digest is over each transcript's digest of its instance (`instance_digest`).
    pub(crate) fn first_circuit(
        &self,
        family: &CircuitFamily<'_>,
        inputs: &NodeInputs<'_, CircuitWitness<'_>>,
    ) -> NodeRows {
        let leaf = &family.leaf;
        let mut b = Builder::new();
        let zeros = matches!(inputs, NodeInputs::Shape).then(|| FixedColumns::zeros(&leaf.circuit.heights()));
        let zero = b.k_const(0);
        let mut claims = NodeClaims::default();
        let mut instances = Vec::with_capacity(self.arity_0);
        for i in 0..self.arity_0 {
            let item = inputs.item(i);
            let limbs: Vec<[Kw; 4]> = (0..leaf.circuit.statement_len)
                .map(|z| {
                    let [l0, l1, l2, _] = item.map_or([0; 4], |l| l.statement[z]);
                    [b.free_k(l0), b.free_k(l1), b.free_k(l2), zero]
                })
                .collect();
            let columns = item.map_or_else(|| zeros.as_ref().expect("zero columns from a shape"), |l| l.columns);
            let source = item.map_or(ProofSource::Shape, |l| ProofSource::Proof(l.proof, &l.openings));
            let (instance, rows) = b.scope(format!("leaf {i}"), |b| {
                let t = RecShape::transcript(b, &leaf.session, &limbs, source);
                let instance = t.digest_so_far(b);
                (instance, family.shape.verify_from(b, t, &limbs, columns))
            });
            claims.bind_state(&mut b, rows.state);
            claims.bound.extend(rows.hints.iter().map(|h| h.value));
            claims
                .dense
                .push(fixed_claim(DensePoly::Leaf, &family.fixed, &rows.hints, None));
            claims.matrices.push(MatrixClaim::fresh(HashFlock::FLOCK, &rows.matrix));
            instances.push(b.d_to_k(instance));
        }
        let digest = Level::Circuit(leaf.seed()).digest_rows(&mut b, &instances);
        NodeRows {
            b,
            kind: Kind::First,
            digest,
            claims,
        }
    }

    /// The node's rows, verifying its children, of either kind.
    pub(crate) fn node(&self, inputs: &NodeInputs<'_, ChildWitness<'_>>) -> NodeRows {
        let mut b = Builder::new();
        let zeros = matches!(inputs, NodeInputs::Shape).then(|| FixedColumns::zeros(&self.taus));
        let mut claims = NodeClaims::default();
        let mut digests = Vec::with_capacity(self.arity);
        for i in 0..self.arity {
            let child = inputs.item(i);
            let statement = match child {
                Some(c) => c.statement.map(|&w| b.free_e(w)),
                None => TreeStatement::filled(self.statement, F192::ZERO).map(|&w| b.free_e(w)),
            };
            // The kind is a bit: it selects the child's circuit's stack of the nodes' fixed polynomial.
            let kind = statement.kind();
            b.scope(format!("child {i} kind"), |b| {
                let square = b.square(kind);
                b.eq_e(square, kind);
            });
            let zero = b.k_const(0);
            let limbs: Vec<[Kw; 4]> = (statement.words().iter())
                .map(|&w| {
                    let [c0, c1, c2] = b.e_to_k(w);
                    [c0, c1, c2, zero]
                })
                .collect();
            let columns = child.map_or_else(|| zeros.as_ref().expect("zero columns from a shape"), |c| c.columns);
            let source = child.map_or(ProofSource::Shape, |c| ProofSource::Proof(c.proof, &c.openings));
            let rows = b.scope(format!("child {i}"), |b| {
                self.child.verify(b, &self.session, &limbs, columns, source)
            });

            claims.bind_state(&mut b, rows.state);
            claims.bound.extend(rows.hints.iter().map(|h| h.value));
            claims
                .dense
                .push(fixed_claim(DensePoly::Fixed, &self.fixed, &rows.hints, Some(kind)));
            claims.matrices.push(MatrixClaim::fresh(HashFlock::FLOCK, &rows.matrix));
            self.carried(&statement, kind, &mut claims);
            let digest = statement.digest_wire(&mut b);
            digests.push(b.d_to_k(digest));
        }
        let digest = Level::Node.digest_rows(&mut b, &digests);
        NodeRows {
            b,
            kind: Kind::Node,
            digest,
            claims,
        }
    }

    /// A circuit built from the shapes alone.
    pub(crate) fn shape(&self, kind: Kind) -> Finished {
        let rows = match (kind, &self.family) {
            (Kind::First, Family::Runs(leaf)) => self.first_runs(leaf, &NodeInputs::Shape),
            (Kind::First, Family::Circuit(family)) => self.first_circuit(family, &NodeInputs::Shape),
            (Kind::Node, _) => self.node(&NodeInputs::Shape),
        };
        rows.reduce(self, ProofSource::Shape)
    }

    /// A leaf's program claim as point claims on the bytecode table and RAM's image.
    ///
    /// - Bit `i`'s share is `phi^i(T(phi^(-i)(chi), alpha))`, by its hinted value `D_i` at the point `(phi^(-i)(chi), alpha)`.
    /// - The image's share is its value at the point's low coordinates, the image being zero above them.
    fn program_claims(
        &self,
        b: &mut Builder,
        program: &Claim<ProgramPoint<Ew>, Ew>,
        inputs: &NodeInputs<'_, LeafWitness<'_>>,
        claims: &mut NodeClaims<Ew>,
    ) {
        let p = &program.point;
        let kbc = self.vars.0[DensePoly::Bytecode as usize] - N_TUPLE_BITS;
        let (chi, alpha) = p.bytecode.split_at(kbc);
        let ladders: Vec<Vec<Ew>> = chi.iter().map(|&x| inverse_frobenius_ladder(b, x, 1)).collect();
        let mut total = b.zero();
        for (i, &mu) in p.twist.iter().enumerate() {
            let point: Vec<Ew> = ladders.iter().map(|l| l[i]).chain(alpha.iter().copied()).collect();
            let d = inputs.hint(b, DensePoly::Bytecode, &point);
            let twisted = (0..i).fold(d, |x, _| b.square(x));
            total = b.mul_add(mu, twisted, total);
            claims.bound.push(d);
            claims.dense.push(DenseClaim::at(DensePoly::Bytecode, point, None, d));
        }
        let m = self.vars.0[DensePoly::Image as usize];
        let low = p.image_point[..m].to_vec();
        let image = inputs.hint(b, DensePoly::Image, &low);
        let above = (p.image_point[m..].iter()).fold(p.image_weight, |acc, &x| b.times_one_plus(acc, x));
        total = b.mul_add(above, image, total);
        b.eq_e(total, program.value);
        claims.bound.push(image);
        claims.dense.push(DenseClaim::at(DensePoly::Image, low, None, image));
    }

    /// The claims a child's statement carries, each on a polynomial a first-level node does not fix scaled by the child's kind.
    ///
    /// A first-level node's statement is zero on such a polynomial, and its kind, the scale, is zero.
    fn carried(&self, statement: &TreeStatement<Ew>, kind: Ew, claims: &mut NodeClaims<Ew>) {
        let point = statement.dense_point();
        for poly in DensePoly::ALL.into_iter().filter(|&p| self.present[p as usize]) {
            let n = self.vars.0[poly as usize];
            let scale = (!self.active(Kind::First, poly)).then_some(kind);
            claims.dense.push(DenseClaim::at(
                poly,
                point[..n].to_vec(),
                scale,
                statement.dense_value(poly),
            ));
        }
        for f in FlockId::ALL {
            claims.matrices.extend(MatrixClaim::carried(
                f,
                f.k_log(),
                statement.rows(),
                statement.cols(),
                statement.matrices(f),
            ));
        }
    }
}

/// A circuit's hinted fixed-column evaluations as claims on a fixed polynomial whose stack of that circuit has this layout.
///
/// Column `c` at the bus point's prefix `p` is the polynomial at `(p, block_c, top)`: `top` the kind, if the polynomial holds both kinds' stacks.
fn fixed_claim(poly: DensePoly, layout: &FixedLayout, hints: &[FixedHint], top: Option<Ew>) -> DenseClaim<Ew> {
    let low = hints
        .iter()
        .map(|h| &h.point)
        .max_by_key(|p| p.len())
        .cloned()
        .unwrap_or_default();
    let terms = (hints.iter())
        .map(|h| {
            let n_low = h.point.len();
            assert!(
                n_low == layout.tau(h.column) && h.point[..] == low[..n_low],
                "a fixed column is read at its prefix of the bus point"
            );
            DenseTerm {
                n_low,
                bits: Bits {
                    value: layout.block(h.column),
                    len: layout.kappa() - n_low,
                },
                top,
                scale: None,
                value: h.value,
            }
        })
        .collect();
    DenseClaim { poly, low, terms }
}

impl Reduced<Ew> {
    /// The statement of a circuit of this kind and digest whose reduction left these claims.
    ///
    /// A polynomial left unreduced has a zero value, and the point is zero past the reduction's rounds.
    fn statement(&self, b: &mut Builder, layout: StatementLayout, kind: Kind, digest: Dw) -> TreeStatement<Ew> {
        let zero = b.zero();
        let mut s = TreeStatement::filled(layout, zero);
        s.section_mut(Section::Kind)[0] = b.e_const(kind.word());
        s.section_mut(Section::Digest)
            .copy_from_slice(&digest_halves_rows(b, digest));
        s.section_mut(Section::DensePoint)[..self.dense.point.len()].copy_from_slice(&self.dense.point);
        for (poly, value) in DensePoly::ALL.into_iter().zip(self.dense.values) {
            if let Some(value) = value {
                *s.dense_value_mut(poly) = value;
            }
        }
        s.section_mut(Section::Rows).copy_from_slice(&self.matrices.rows);
        s.section_mut(Section::Cols).copy_from_slice(&self.matrices.cols);
        s.section_mut(Section::Matrices)
            .copy_from_slice(self.matrices.values.as_flattened());
        s
    }
}

impl NodeRows {
    /// The claims' values, which the prover's reduction takes.
    pub(crate) fn claim_values(&self) -> NodeClaims<F192> {
        self.claims.map(|w| self.b.e(w))
    }

    /// Verify the reduction the given source holds, then expose the statement: the kind, the digest, the reduced claims.
    pub(crate) fn reduce(mut self, design: &Design<'_>, source: ProofSource<'_>) -> Finished {
        let b = &mut self.b;
        let claims = &self.claims;

        // The instance is every value the claims rest on, their count first.
        let count = b.k_const(claims.bound.len() as u64);
        let mut instance = vec![count];
        for &x in &claims.bound {
            instance.extend(b.e_to_k(x));
        }
        let mut t = Transcript::new(b, &reduce::session(&design.session), &instance, source);
        let reduced = b.scope("reduction", |b| {
            infallible(claims.verify(&mut Rows::new(b, &mut t), &design.vars))
        });
        if !t.finished() {
            b.scope("reduction", |b| {
                b.fail("the reduction has data the verifier never reads");
            });
        }
        let statement = reduced.statement(b, design.statement, self.kind, self.digest);
        for &w in statement.words() {
            b.expose_e(w);
        }
        self.b.finish()
    }
}
