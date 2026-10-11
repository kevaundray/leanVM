//! The tree's two circuits, and the heights they share.
//!
//! - A first-level node verifies RISC-V proofs of the program, and of the proofs each assumes, turns their program claims into point claims, and reduces every claim.
//! - A node verifies recursion proofs of either kind, and reduces their fresh claims with the claims they carry.
//!
//! Both circuits have the same heights, so a node verifies a child of either kind with one set of rows.

use super::claims::{Bits, DenseClaim, DensePoly, DenseTerm, MatrixClaim, NodeClaims};
use super::fixed::FixedLayout;
use super::reduce::{DenseTables, DenseVars, Reduced};
use super::statement::{Kind, Section, StatementLayout, TreeStatement, digest_halves_rows};
use super::{TreeError, reduce};
use crate::class_flock::FlockId;
use crate::cpu::{Claim, Lookup, Program, ProgramPoint};
use crate::leaf::N_TUPLE_BITS;
use crate::pcs::Rate;
use crate::rec::circuit::{ASSUMING_IV, Builder, Dw, Ew, Finished, Kw};
use crate::rec::fixed::FixedColumns;
use crate::rec::table::{HashFlock, PerRecTable};
use crate::rec::transcript::{ProofSource, Transcript};
use crate::rec::verifier::{FixedHint, ProofShape, RecShape, Rows, infallible};
use fiat_shamir::arith::Arith;
use fiat_shamir::{ProofTranscript, SessionId};
use pcs::merkle::Openings;

use pcs::ring_switch::inverse_frobenius_ladder;
use primitives::field::{F64, F192};
use primitives::multilinear::mle_eval_par;

/// The protocol half of every recursion proof's session tag.
const DOMAIN: &[u8] = b"leanvm-tree-12";

/// Where one program's tables sit in the dense polynomials: alone, or as one half of a stack of two.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Slot {
    /// The bytecode table's entry variables.
    kbc: usize,
    /// The image's variables.
    m: usize,
    /// The half it fills when the leaves' program and the assumed one share the polynomials: their top variable.
    half: Option<usize>,
}

/// The proofs each leaf of a tree assumes: their shape, how many, and where their program sits.
pub(crate) struct Assumed<'p> {
    /// Their shape: the program, its tables' heights, its rate.
    pub(crate) shape: ProofShape<'p>,
    /// How many each leaf assumes.
    pub(crate) count: usize,
    /// Where their program sits in the dense polynomials.
    slot: Slot,
}

/// What fixes a tree's circuits: the leaves' shape, the proofs they assume, the arities, the rate, and the nodes' heights.
pub(crate) struct Design<'p> {
    /// The leaves' shape: the program, its tables' heights, its rate.
    pub(crate) leaf: ProofShape<'p>,
    /// Where the leaves' program sits in the dense polynomials.
    slot: Slot,
    /// The proofs each leaf assumes, if any.
    pub(crate) assumed: Option<Assumed<'p>>,
    /// The leaves a first-level node verifies.
    pub(crate) arity_0: usize,
    /// The children a node verifies.
    pub(crate) arity: usize,
    /// Every tree proof's rate.
    pub(crate) rate: Rate,
    /// The nodes' heights, which both circuits share.
    pub(crate) taus: PerRecTable<usize>,
    /// The shape of a child recursion proof.
    child: RecShape,
    /// Where each fixed column sits in one circuit's stack.
    pub(crate) fixed: FixedLayout,
    /// Each dense polynomial's variables.
    pub(crate) vars: DenseVars,
    /// Where each part of a statement sits.
    pub(crate) statement: StatementLayout,
    /// The transcript's session for every recursion proof of the tree.
    pub(crate) session: SessionId,
}

/// A leaf as a first-level node's prover holds it: its proof, which the native verifier accepted, and what it states.
pub(crate) struct LeafWitness<'a> {
    /// The proof.
    pub(crate) proof: &'a ProofTranscript,
    /// Every opening its native verifier authenticated, phase by phase.
    pub(crate) openings: Vec<Openings>,
    /// The output it proves, its run's exit output.
    pub(crate) output: [u64; 4],
    /// The digest of its run's committed values: its output when it assumes nothing.
    pub(crate) committed: [u64; 4],
    /// The proofs it assumes, in order, each assuming nothing.
    pub(crate) assumed: Vec<Self>,
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
    /// The digest of the leaves' outputs under it.
    digest: Dw,
    /// The claims its rows leave.
    claims: NodeClaims<Ew>,
}

impl<T> NodeInputs<'_, T> {
    /// Proof `i`, when a prover holds it.
    const fn item(&self, i: usize) -> Option<&T> {
        match self {
            Self::Shape => None,
            Self::Prove { items, .. } => Some(&items[i]),
        }
    }

    /// A dense polynomial's value at a point then public bits, as a hint: only the prover's tables give it, zero from
    /// the shapes.
    fn hint(&self, b: &mut Builder, poly: DensePoly, point: &[Ew], bits: Bits) -> Ew {
        let value = match self {
            Self::Shape => F192::ZERO,
            Self::Prove { tables, .. } => {
                let bit = |i: usize| F192::new((bits.value >> i & 1) as u64, 0, 0);
                let at: Vec<F192> = (point.iter().map(|&w| b.e(w))).chain((0..bits.len).map(bit)).collect();
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

impl Slot {
    /// The slot of a program's tables, in the given half of a stack of two if any.
    fn of(program: &Program, half: Option<usize>) -> Self {
        let rv = program.rv();
        Self {
            kbc: crate::log2_strict_usize(rv.entries().len()),
            m: crate::log2_ceil_usize(rv.image().len().max(1)),
            half,
        }
    }

    /// The public coordinates that place a point of `n` coordinates on this program's tables in a polynomial of `vars`:
    /// zeros past the program's own variables, then its half.
    fn bits(self, n: usize, vars: usize) -> Bits {
        self.half.map_or_else(
            || {
                assert_eq!(n, vars, "a program alone fills its polynomial");
                Bits::NONE
            },
            |half| Bits {
                value: half << (vars - 1 - n),
                len: vars - n,
            },
        )
    }
}

impl<'p> Design<'p> {
    /// The design at the given heights of both circuits.
    ///
    /// # Errors
    ///
    /// Returns an error if the heights admit no recursion proof.
    pub(crate) fn new(
        leaf: ProofShape<'p>,
        assumed: Option<(ProofShape<'p>, usize)>,
        arity_0: usize,
        arity: usize,
        rate: Rate,
        taus: PerRecTable<usize>,
    ) -> Result<Self, TreeError> {
        let child = RecShape::new(taus, rate).map_err(|_| TreeError::TooLarge)?;
        let fixed = FixedLayout::new(&taus);
        let stacked = assumed.as_ref().map(|_| 0);
        let slot = Slot::of(leaf.program(), stacked);
        let assumed = assumed.map(|(shape, count)| Assumed {
            slot: Slot::of(shape.program(), Some(1)),
            shape,
            count,
        });
        // Two programs stack their tables, each padded to the larger, under one more variable.
        let slots = [Some(slot), assumed.as_ref().map(|a| a.slot)];
        let most = |f: fn(&Slot) -> usize| slots.iter().flatten().map(f).max().unwrap_or(0);
        let halves = usize::from(assumed.is_some());
        let vars = DenseVars([
            most(|s| s.kbc) + N_TUPLE_BITS + halves,
            most(|s| s.m) + halves,
            fixed.kappa() + 1,
        ]);
        let statement = StatementLayout::new(vars.0.into_iter().max().unwrap_or(0));
        let mut design = Self {
            leaf,
            slot,
            assumed,
            arity_0,
            arity,
            rate,
            taus,
            child,
            fixed,
            vars,
            statement,
            session: SessionId([0; 32]),
        };
        design.session = design.session();
        Ok(design)
    }

    /// The transcript's session: everything that fixes the circuits, as one tag.
    ///
    /// Both kinds share it.
    /// The kind is the statement's first word, and the statement is the transcript's instance.
    fn session(&self) -> SessionId {
        let mut tag = DOMAIN.to_vec();
        tag.extend_from_slice(self.leaf.program().digest());
        let count = self.assumed.as_ref().map_or(0, |a| a.count);
        let sizes = (self.leaf.taus().values().copied())
            .chain([self.arity_0, self.arity, self.statement.len(), count])
            .chain(self.taus.into_values());
        for x in sizes {
            tag.extend_from_slice(&(x as u64).to_le_bytes());
        }
        tag.extend_from_slice(&[self.leaf.rate().log_inv_rate(), self.rate.log_inv_rate()]);
        if let Some(a) = &self.assumed {
            tag.extend_from_slice(a.shape.program().digest());
            for &x in a.shape.taus().values() {
                tag.extend_from_slice(&(x as u64).to_le_bytes());
            }
            tag.push(a.shape.rate().log_inv_rate());
        }
        SessionId::new(&tag)
    }

    /// The dense polynomials the root's claims are settled against: the bytecode tables, the images, the fixed one.
    ///
    /// With assumed proofs, the leaves' program's table is the lower half of each of the first two, the assumed
    /// program's the upper.
    pub(crate) fn tables(&self, fixed: Vec<F64>) -> DenseTables {
        let programs: Vec<&Program> = [
            Some(self.leaf.program()),
            self.assumed.as_ref().map(|a| a.shape.program()),
        ]
        .into_iter()
        .flatten()
        .collect();
        let stack = |poly: DensePoly, table: fn(&Program) -> Vec<F64>| -> Vec<F64> {
            let half = (1 << self.vars.0[poly as usize]) / programs.len();
            (programs.iter())
                .flat_map(|&p| {
                    let mut t = table(p);
                    t.resize(half, F64::ZERO);
                    t
                })
                .collect()
        };
        DenseTables([
            stack(DensePoly::Bytecode, |p| Lookup::Bytecode.table(p.rv())),
            stack(DensePoly::Image, |p| p.rv().image().iter().map(|&w| F64(w)).collect()),
            fixed,
        ])
    }

    /// The first level's rows, verifying its leaves and the proofs they assume.
    ///
    /// A leaf that assumes proofs states its committed values' digest: the rows verify each assumed proof, fold the
    /// assumed program's digest and each one's output with that digest as the leaf's guest did, and hold the fold to
    /// the output the leaf's proof states.
    pub(crate) fn first(&self, inputs: &NodeInputs<'_, LeafWitness<'_>>) -> NodeRows {
        let mut b = Builder::new();
        let mut claims = NodeClaims::default();
        let mut outputs = Vec::with_capacity(self.arity_0);
        for i in 0..self.arity_0 {
            let leaf = inputs.item(i);
            let output = b.scope(format!("leaf {i}"), |b| {
                self.verified(b, (&self.leaf, self.slot), leaf, inputs, &mut claims)
            });
            let stated = self.assumed.as_ref().map_or(output, |a| {
                let assumed: Vec<[Kw; 4]> = (0..a.count)
                    .map(|j| {
                        let proof = leaf.map(|l| &l.assumed[j]);
                        b.scope(format!("leaf {i} assumption {j}"), |b| {
                            self.verified(b, (&a.shape, a.slot), proof, inputs, &mut claims)
                        })
                    })
                    .collect();
                let committed = leaf.map_or([0; 4], |l| l.committed).map(|w| b.free_k(w));
                b.scope(format!("leaf {i} assumptions"), |b| {
                    let program = a.shape.program().digest_words().map(|w| b.k_const(w));
                    let folded = assuming_rows(b, committed, program, &assumed);
                    for (w, o) in b.d_to_k(folded).into_iter().zip(output) {
                        b.eq_k(w, o);
                    }
                });
                committed
            });
            outputs.push(stated);
        }
        let digest = Kind::First.digest_rows(&mut b, &outputs);
        NodeRows {
            b,
            kind: Kind::First,
            digest,
            claims,
        }
    }

    /// One RISC-V proof's core in rows, of a program of this shape and slot, its claims added to the node's: returns
    /// its output's wires.
    fn verified(
        &self,
        b: &mut Builder,
        (shape, slot): (&ProofShape<'_>, Slot),
        proof: Option<&LeafWitness<'_>>,
        inputs: &NodeInputs<'_, LeafWitness<'_>>,
        claims: &mut NodeClaims<Ew>,
    ) -> [Kw; 4] {
        let output = proof.map_or([0; 4], |l| l.output).map(|o| b.free_k(o));
        let source = proof.map_or(ProofSource::Shape, |l| ProofSource::Proof(l.proof, &l.openings));
        let core = shape.verify_core(b, output, source);
        claims.bind_state(b, core.state);
        b.scope("program", |b| {
            self.program_claims(b, &core.claims.program, slot, inputs, claims);
        });
        let fresh = FlockId::ALL.into_iter().zip(&core.claims.circuits);
        claims.matrices.extend(fresh.map(|(f, c)| MatrixClaim::fresh(f, c)));
        output
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
            // The kind is a bit: it selects the child's circuit's half of the fixed polynomial.
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
            claims.dense.push(self.fixed_claim(&rows.hints, kind));
            claims.matrices.push(MatrixClaim::fresh(HashFlock::FLOCK, &rows.matrix));
            self.carried(&statement, kind, &mut claims);
            let digest = statement.digest_wire(&mut b);
            digests.push(b.d_to_k(digest));
        }
        let digest = Kind::Node.digest_rows(&mut b, &digests);
        NodeRows {
            b,
            kind: Kind::Node,
            digest,
            claims,
        }
    }

    /// A circuit built from the shapes alone.
    pub(crate) fn shape(&self, kind: Kind) -> Finished {
        let rows = match kind {
            Kind::First => self.first(&NodeInputs::Shape),
            Kind::Node => self.node(&NodeInputs::Shape),
        };
        rows.reduce(self, ProofSource::Shape)
    }

    /// A proof's program claim as point claims on the bytecode table and RAM's image, in its program's slot.
    ///
    /// - Bit `i`'s share is `phi^i(T(phi^(-i)(chi), alpha))`, by its hinted value `D_i` at the point `(phi^(-i)(chi), alpha)`.
    /// - The image's share is its value at the point's low coordinates, the image being zero above them.
    fn program_claims(
        &self,
        b: &mut Builder,
        program: &Claim<ProgramPoint<Ew>, Ew>,
        slot: Slot,
        inputs: &NodeInputs<'_, LeafWitness<'_>>,
        claims: &mut NodeClaims<Ew>,
    ) {
        let p = &program.point;
        let (chi, alpha) = p.bytecode.split_at(slot.kbc);
        let ladders: Vec<Vec<Ew>> = chi.iter().map(|&x| inverse_frobenius_ladder(b, x, 1)).collect();
        let mut total = b.zero();
        let vars = self.vars.0[DensePoly::Bytecode as usize];
        for (i, &mu) in p.twist.iter().enumerate() {
            let point: Vec<Ew> = ladders.iter().map(|l| l[i]).chain(alpha.iter().copied()).collect();
            let bits = slot.bits(point.len(), vars);
            let d = inputs.hint(b, DensePoly::Bytecode, &point, bits);
            let twisted = (0..i).fold(d, |x, _| b.square(x));
            total = b.mul_add(mu, twisted, total);
            claims.bound.push(d);
            claims
                .dense
                .push(DenseClaim::at_bits(DensePoly::Bytecode, point, bits, d));
        }
        let low = p.image_point[..slot.m].to_vec();
        let bits = slot.bits(slot.m, self.vars.0[DensePoly::Image as usize]);
        let image = inputs.hint(b, DensePoly::Image, &low, bits);
        let above = (p.image_point[slot.m..].iter()).fold(p.image_weight, |acc, &x| b.times_one_plus(acc, x));
        total = b.mul_add(above, image, total);
        b.eq_e(total, program.value);
        claims.bound.push(image);
        claims
            .dense
            .push(DenseClaim::at_bits(DensePoly::Image, low, bits, image));
    }

    /// A child's hinted fixed-column evaluations as claims on the fixed polynomial, in its circuit's half.
    ///
    /// Column `c` at the bus point's prefix `p` is the fixed polynomial at `(p, block_c, kind)`.
    fn fixed_claim(&self, hints: &[FixedHint], kind: Ew) -> DenseClaim<Ew> {
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
                    n_low == self.fixed.tau(h.column) && h.point[..] == low[..n_low],
                    "a fixed column is read at its prefix of the bus point"
                );
                DenseTerm {
                    n_low,
                    bits: Bits {
                        value: self.fixed.block(h.column),
                        len: self.fixed.kappa() - n_low,
                    },
                    top: Some(kind),
                    scale: None,
                    value: h.value,
                }
            })
            .collect();
        DenseClaim {
            poly: DensePoly::Fixed,
            low,
            terms,
        }
    }

    /// The claims a child's statement carries.
    ///
    /// A first-level node reduces no claim on the fixed polynomial, so its carried one is scaled by its kind, zero.
    fn carried(&self, statement: &TreeStatement<Ew>, kind: Ew, claims: &mut NodeClaims<Ew>) {
        let point = statement.dense_point();
        for poly in DensePoly::ALL {
            let n = self.vars.0[poly as usize];
            let scale = (poly == DensePoly::Fixed).then_some(kind);
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

impl Reduced<Ew> {
    /// The statement of a circuit of this kind and digest whose reduction left these claims.
    ///
    /// A polynomial left unreduced has a zero value, and the point is zero past the reduction's rounds.
    fn statement(&self, b: &mut Builder, layout: StatementLayout, kind: Kind, digest: Dw) -> TreeStatement<Ew> {
        let zero = b.zero();
        let mut s = TreeStatement::filled(layout, zero);
        s.section_mut(Section::Kind)[0] = b.e_const(F192::new(kind.bit(), 0, 0));
        s.section_mut(Section::Digest)
            .copy_from_slice(&digest_halves_rows(b, digest));
        s.section_mut(Section::DensePoint)[..self.dense.point.len()].copy_from_slice(&self.dense.point);
        let values = self.dense.values.map(|v| v.unwrap_or(zero));
        s.section_mut(Section::DenseValues).copy_from_slice(&values);
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

/// The output a run committing values of digest `committed` exits with, having assumed runs of the program of digest
/// `program` exiting with `outputs`, in order: `Output::assuming`, in rows, one hash row per assumption and one more.
pub(crate) fn assuming_rows(b: &mut Builder, committed: [Kw; 4], program: [Kw; 4], outputs: &[[Kw; 4]]) -> Dw {
    let words: Vec<Kw> = (outputs.iter())
        .flat_map(|o| program.into_iter().chain(*o))
        .chain(committed)
        .collect();
    b.chain_from(ASSUMING_IV, &words)
}
