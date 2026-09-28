use std::sync::Arc;

use fiat_shamir::transcript::{Challenger, Proof, ProverState, Receiver, Transmitter, VerifierState};
use lean_vm::{
    colval::ColVal,
    constraints, hash_flock, leaf, pcs as vm_pcs,
    witness::{self, Placement, StackShape},
};
use leanvm_guest::{Field, deferred::public_digest};
use primitives::{
    field::{F64, F192, g_pow},
    hash::Hasher,
};
use riscv_proof::schema::Coord;

use crate::{
    Circuit, Error,
    tables::{self, NativeTable, TableKind},
};

pub(crate) const FIXED_LOG_INV_RATE: usize = 1;
pub(crate) const KEY_HEADER_WORDS: usize = 12;
pub(crate) const KEY_TABLE_WORDS: usize = 5;
pub(crate) const KEY_WORDS: usize = KEY_HEADER_WORDS + tables::KIND_COUNT * KEY_TABLE_WORDS;
pub(crate) const KEY_DOMAIN: &[u8] = b"leanVM/native-circuit/key/v2\0";

type Owners = [Vec<Option<(usize, usize)>>; 3];

struct Stack {
    placements: Vec<Placement>,
    shape: StackShape,
}

impl Stack {
    fn new(logs: Vec<Option<usize>>) -> Result<Self, Error> {
        let words = logs
            .iter()
            .try_fold(0usize, |sum, log| {
                sum.checked_add(1usize.checked_shl(log.unwrap() as u32)?)
            })
            .ok_or(Error::Capacity)?;
        if words > 1usize << vm_pcs::MAX_MU {
            return Err(Error::Capacity);
        }
        let (placements, shape) = witness::placements_of(&logs);
        Ok(Self { placements, shape })
    }

    fn columns<'a>(&self, values: &'a [F64]) -> Vec<&'a [F64]> {
        self.placements
            .iter()
            .map(|p| &values[p.offset..p.offset + (1 << p.n_vars)])
            .collect()
    }
}

struct Layout {
    fixed: Stack,
    private: Stack,
    fixed_starts: Vec<usize>,
    spans: Vec<(usize, usize)>,
    columns: Vec<(bool, usize)>,
    flock: Option<(usize, usize)>,
}

impl Layout {
    fn new(tables: &[NativeTable]) -> Result<Self, Error> {
        let mut fixed_logs = Vec::new();
        let mut private_logs = Vec::new();
        let mut fixed_starts = Vec::new();
        let mut spans = Vec::new();
        let mut columns = Vec::new();
        let mut flock = None;
        for (index, table) in tables.iter().enumerate() {
            let fixed = fixed_logs.len();
            let private = private_logs.len();
            fixed_starts.push(fixed);
            spans.push((columns.len(), table.fixed.len() + table.width));
            columns.extend((0..table.fixed.len()).map(|column| (true, fixed + column)));
            columns.extend((0..table.width).map(|column| (false, private + column)));
            fixed_logs.extend(std::iter::repeat_n(Some(table.log_rows), table.fixed.len()));
            private_logs.extend(std::iter::repeat_n(Some(table.log_rows), table.width));
            if table.kind == TableKind::Blake2s {
                flock = Some((index, 0));
            }
        }
        if let Some((table, column)) = &mut flock {
            *column = private_logs.len();
            private_logs.push(Some(hash_flock::qflock_kappa(1 << tables[*table].log_rows)));
        }
        Ok(Self {
            fixed: Stack::new(fixed_logs)?,
            private: Stack::new(private_logs)?,
            fixed_starts,
            spans,
            columns,
            flock,
        })
    }

    fn columns<'a>(&self, fixed: &'a [F64], private: &'a [F64]) -> Vec<&'a [F64]> {
        let fixed = self.fixed.columns(fixed);
        let private = self.private.columns(private);
        self.columns
            .iter()
            .map(|&(is_fixed, index)| if is_fixed { fixed[index] } else { private[index] })
            .collect()
    }
}

struct Wiring {
    blocks: [Vec<leaf::Block>; 3],
    owners: Owners,
}

fn coordinate(coord: &Coord, base: usize) -> leaf::Coord {
    let scaled = |a: usize, b: Option<usize>, coefficient: u64| {
        let terms: Vec<_> = (0..64)
            .filter(|bit| coefficient >> bit & 1 != 0)
            .map(|bit| match b {
                Some(b) => leaf::Coord::Prod(base + a, base + b, bit),
                None if bit == 0 => leaf::Coord::Col(base + a),
                None => leaf::Coord::GCol(base + a, bit),
            })
            .collect();
        if terms.is_empty() {
            leaf::Coord::Const(F64::ZERO)
        } else {
            leaf::Coord::Sum(terms)
        }
    };
    match coord {
        Coord::Constant(value) => leaf::Coord::Const(F64(*value)),
        Coord::Column(column) => leaf::Coord::Col(base + column),
        Coord::Scaled(column, coefficient) | Coord::PublicScaled(column, _, coefficient) => {
            scaled(*column, None, *coefficient)
        }
        Coord::Product(a, b, coefficient) => scaled(*a, Some(*b), *coefficient),
        Coord::Sum(terms) => leaf::Coord::Sum(terms.iter().map(|term| coordinate(term, base)).collect()),
    }
}

impl Wiring {
    fn new(tables: &[NativeTable], layout: &Layout, public: &[Field]) -> Self {
        let mut result = Self {
            blocks: std::array::from_fn(|_| Vec::new()),
            owners: std::array::from_fn(|_| Vec::new()),
        };
        for (index, table) in tables.iter().enumerate() {
            let base = layout.spans[index].0;
            for flush in &table.flushes {
                for (side, coords) in [&flush.push, &flush.pull].into_iter().enumerate() {
                    result.blocks[side].push(leaf::Block {
                        kappa: table.log_rows,
                        coords: coords.iter().map(|coord| coordinate(coord, base)).collect(),
                    });
                    result.owners[side].push(Some((index, base)));
                }
                assert!(flush.count.is_none(), "native read counters are fixed metadata");
            }
        }
        // Constant one-row blocks avoid treating statement data as program ROM.
        for (index, value) in public.iter().enumerate() {
            let tuple = [256, g_pow(index).0, value.0[0], value.0[1], value.0[2]];
            result.blocks[0].push(leaf::Block {
                kappa: 0,
                coords: tuple.into_iter().map(|value| leaf::Coord::Const(F64(value))).collect(),
            });
            result.blocks[1].push(leaf::Block {
                kappa: 0,
                coords: vec![leaf::Coord::Const(F64::ZERO); 5],
            });
            result.owners[0].push(None);
            result.owners[1].push(None);
        }
        result
    }
}

fn digest_words(bytes: [u8; 32]) -> [F64; 4] {
    std::array::from_fn(|i| F64(u64::from_le_bytes(bytes[8 * i..8 * i + 8].try_into().unwrap())))
}

fn descriptor(circuit: &Circuit, tables: &[NativeTable], layout: &Layout, root: &[u8; 32]) -> [u64; KEY_WORDS] {
    let mut blocks = Vec::new();
    let mut starts = Vec::new();
    let mut public_offset = 0usize;
    for table in tables {
        starts.push(blocks.len());
        for _ in &table.flushes {
            blocks.push(leaf::Block {
                kappa: table.log_rows,
                coords: Vec::new(),
            });
            public_offset += 1usize << table.log_rows;
        }
    }
    let bus = leaf::layout(&blocks);
    let total = public_offset + circuit.public_inputs();
    let bus_mu = (usize::BITS - (total.max(1) - 1).leading_zeros()) as usize;
    let mut words = [0; KEY_WORDS];
    let header = [
        circuit.public_inputs(),
        layout.fixed.shape.mu,
        layout.fixed.shape.n_lanes,
        layout.private.shape.mu,
        layout.private.shape.n_lanes,
        bus_mu,
        public_offset,
        layout
            .flock
            .map_or(0, |(_, column)| layout.private.placements[column].offset),
    ];
    for (slot, value) in words.iter_mut().zip(header) {
        *slot = value as u64;
    }
    for (slot, word) in words[8..12].iter_mut().zip(digest_words(*root)) {
        *slot = word.0;
    }
    for (index, table) in tables.iter().enumerate() {
        let fixed = layout.fixed.placements[layout.fixed_starts[index]].offset;
        let private = layout.columns[layout.spans[index].0 + table.fixed.len()].1;
        let offset = KEY_HEADER_WORDS + table.kind as usize * KEY_TABLE_WORDS;
        let values = [
            1,
            table.log_rows,
            fixed,
            layout.private.placements[private].offset,
            bus.offsets[starts[index]],
        ];
        for (slot, value) in words[offset..offset + KEY_TABLE_WORDS].iter_mut().zip(values) {
            *slot = value as u64;
        }
    }
    words
}

fn descriptor_digest(words: &[u64; KEY_WORDS]) -> [u8; 32] {
    let mut hash = Hasher::new();
    hash.update(&primitives::hash::hash(KEY_DOMAIN));
    for word in words {
        hash.update(&word.to_le_bytes());
    }
    hash.finalize()
}

fn form_powers(tables: &[NativeTable], eta: F192) -> [F192; 3] {
    let count: usize = tables.iter().map(|table| table.relations.len()).sum();
    let mut first = F192::ONE;
    for _ in 0..count {
        first *= eta;
    }
    [first, first * eta, first * eta * eta]
}

fn airs(
    tables: &[NativeTable],
    forms: &[Vec<leaf::BusForm>; 3],
    eta: F192,
    shared: [F192; 3],
) -> Vec<constraints::Air<'static>> {
    let mut weight = F192::ONE;
    tables
        .iter()
        .enumerate()
        .map(|(index, table)| {
            let mut form = leaf::BusForm::sum((0..3).map(|side| forms[side][index].scaled(shared[side])));
            for relation in &table.relations {
                relation.accumulate(&mut form, weight);
                weight *= eta;
            }
            for (a, b, _) in &mut form.prods {
                if *a > *b {
                    std::mem::swap(a, b);
                }
            }
            form.prods.sort_unstable_by_key(|&(a, b, _)| (a, b));
            let mut length = 0;
            for i in 0..form.prods.len() {
                let (a, b, coefficient) = form.prods[i];
                if length != 0 && (form.prods[length - 1].0, form.prods[length - 1].1) == (a, b) {
                    form.prods[length - 1].2 += coefficient;
                } else {
                    form.prods[length] = (a, b, coefficient);
                    length += 1;
                }
            }
            form.prods.truncate(length);
            form.prods.retain(|&(_, _, value)| value != F192::ZERO);
            let form = Arc::new(form);
            let form_k = Arc::clone(&form);
            constraints::Air {
                tau: table.log_rows,
                n_cols: table.fixed.len() + table.width,
                n_constraints: table.relations.len(),
                eval: Box::new(move |_, values, quadratic| {
                    <F192 as ColVal>::reduce(form.eval_unreduced(values, quadratic))
                }),
                eval_k: Box::new(move |_, values, quadratic| {
                    <F64 as ColVal>::reduce(form_k.eval_unreduced(values, quadratic))
                }),
            }
        })
        .collect()
}

#[derive(Clone, Copy, Debug)]
pub struct Summary {
    pub fixed_words: usize,
    pub witness_words: usize,
    pub table_rows: usize,
    pub hash_compressions: usize,
}

/// Prepared from the expected circuit, never from a proof-supplied program.
/// Persistent metadata and commitment buffers use ordinary vectors.
pub struct Key {
    circuit: Circuit,
    tables: Vec<NativeTable>,
    layout: Layout,
    fixed: Vec<F64>,
    fixed_codeword: Vec<F64>,
    fixed_merkle: Vec<[u8; 32]>,
    fixed_root: [u8; 32],
    fixed_config: pcs::whir::ProverConfig,
    digest: [u8; 32],
    descriptor: [u64; KEY_WORDS],
}

impl Key {
    pub fn new(circuit: Circuit) -> Result<Self, Error> {
        let mut tables = tables::compile(&circuit)?;
        if tables.is_empty() {
            return Err(Error::InvalidCircuit);
        }
        let layout = Layout::new(&tables)?;
        let mut fixed = vec![F64::ZERO; layout.fixed.shape.committed_len()];
        for (index, table) in tables.iter_mut().enumerate() {
            for (column, values) in table.fixed.iter_mut().enumerate() {
                let placement = layout.fixed.placements[layout.fixed_starts[index] + column];
                fixed[placement.offset..placement.offset + values.len()].copy_from_slice(values);
                // Keep the column count, but move its storage into the cached stack.
                *values = Vec::new();
            }
        }
        let fixed_config =
            pcs::whir::config_for_rate(layout.fixed.shape.mu, FIXED_LOG_INV_RATE).map_err(|_| Error::Capacity)?;
        let (commitment, data) = pcs::whir::commit(
            &fixed,
            layout.fixed.shape.mu,
            pcs::whir::INITIAL_FOLDING_FACTOR,
            FIXED_LOG_INV_RATE,
        );
        let descriptor = descriptor(&circuit, &tables, &layout, &commitment.root);
        let digest = descriptor_digest(&descriptor);
        Ok(Self {
            circuit,
            tables,
            layout,
            fixed,
            fixed_codeword: data.codeword.to_vec(),
            fixed_merkle: data.merkle_tree.to_vec(),
            fixed_root: commitment.root,
            fixed_config,
            digest,
            descriptor,
        })
    }

    pub fn digest(&self) -> [u8; 32] {
        self.digest
    }

    /// Descriptor of this trusted circuit, suitable for independent verification.
    pub fn descriptor(&self) -> &[u64; KEY_WORDS] {
        &self.descriptor
    }

    pub fn summary(&self) -> Summary {
        Summary {
            fixed_words: self.fixed.len(),
            witness_words: self.layout.private.shape.committed_len(),
            table_rows: self.tables.iter().map(|table| 1usize << table.log_rows).sum(),
            hash_compressions: self.layout.flock.map_or(0, |(table, _)| self.tables[table].row_count()),
        }
    }

    pub fn prove(&self, public: &[Field], private: &[Field], log_inv_rate: usize) -> Result<Proof, Error> {
        let values = self.circuit.evaluate(public, private)?;
        self.prove_values(public, &values, log_inv_rate)
    }

    fn prove_values(&self, public: &[Field], values: &[Field], log_inv_rate: usize) -> Result<Proof, Error> {
        if public.len() != self.circuit.public_inputs() {
            return Err(Error::InvalidInput);
        }
        if !(vm_pcs::MIN_LOG_INV_RATE..=vm_pcs::MAX_LOG_INV_RATE).contains(&log_inv_rate) {
            return Err(Error::InvalidInput);
        }
        let _phase = zk_alloc::enter_phase();
        // SAFETY: the table materializer and Flock fill every window; split_stack zeros the tail.
        let mut q = unsafe { witness::alloc_stack(self.layout.private.shape) };
        let prepared = {
            let mut windows = witness::split_stack(&mut q, &self.layout.private.placements).into_iter();
            let mut table_windows: Vec<Vec<&mut [F64]>> = self
                .tables
                .iter()
                .map(|table| windows.by_ref().take(table.width).collect())
                .collect();
            tables::witness(&self.tables, &self.circuit, values, &mut table_windows)?;
            if let Some((table, _)) = self.layout.flock {
                let fixed_count = self.tables[table].fixed.len();
                let mut slots = [0usize; 20];
                for &(column, slot) in &self.tables[table].flock_slots {
                    slots[slot] = column - fixed_count;
                }
                let columns = &table_windows[table];
                let blocks: Vec<_> = (0..1usize << self.tables[table].log_rows)
                    .map(|row| {
                        let words =
                            |start: usize| -> [F64; 4] { std::array::from_fn(|i| columns[slots[start + i]][row]) };
                        let metadata = F192::new(columns[slots[18]][row].0, columns[slots[19]][row].0, 0);
                        hash_flock::compression(words(10), words(14), words(0), metadata)
                    })
                    .collect();
                Some(hash_flock::build_qflock_prepared(
                    &blocks,
                    windows.next().ok_or(Error::InvalidCircuit)?,
                ))
            } else {
                None
            }
        };
        let mut ps = ProverState::new(digest_words(self.digest), digest_words(public_digest(public)));
        ps.add_scalar(F192::from(F64(log_inv_rate as u64)));
        let committed = vm_pcs::commit(&mut ps, &q, self.layout.private.shape, log_inv_rate);
        let columns = self.layout.columns(&self.fixed, &q);
        let wiring = Wiring::new(&self.tables, &self.layout, public);
        let bus = leaf::prove_balance(
            &wiring.blocks[0],
            &wiring.blocks[1],
            &wiring.blocks[2],
            &columns,
            &wiring.owners,
            &self.layout.spans,
            &mut ps,
        );
        let eta = ps.sample();
        let shared = form_powers(&self.tables, eta);
        let sigma: Vec<_> = (0..self.tables.len())
            .map(|table| (0..3).fold(F192::ZERO, |sum, side| sum + shared[side] * bus.sigmas[side][table]))
            .collect();
        let table_columns: Vec<_> = self
            .layout
            .spans
            .iter()
            .map(|&(base, width)| columns[base..base + width].to_vec())
            .collect();
        let claims = constraints::prove(
            &airs(&self.tables, &bus.forms, eta, shared),
            &table_columns,
            eta,
            &bus.point,
            &sigma,
            &mut ps,
        );
        let (fixed_claims, private_claims) = self.claims(bus.claims, &claims);
        let rings = prepared
            .as_ref()
            .map(|prepared| {
                let reduced = prepared.prove(&mut ps);
                hash_flock::ring_switch_open(
                    prepared.n_blocks(),
                    self.layout.private.placements[self.layout.flock.unwrap().1].offset,
                    &reduced,
                )
            })
            .into_iter()
            .collect::<Vec<_>>();
        vm_pcs::open(&mut ps, &committed, &q, &private_claims, &rings);
        pcs::stack_open::open_batch_mixed_whir_stacked(
            &mut ps,
            self.layout.fixed.shape.mu,
            &self.fixed,
            &self.fixed_codeword,
            &self.fixed_merkle,
            &self.fixed_config,
            &fixed_claims,
            &[],
        );
        Ok(ps.into_proof())
    }

    fn claims(
        &self,
        bus: Vec<leaf::ColumnClaim>,
        tables: &[constraints::Claims],
    ) -> (Vec<vm_pcs::SlotClaim>, Vec<vm_pcs::SlotClaim>) {
        let mut fixed = Vec::new();
        let mut private = Vec::new();
        let mut add = |column: usize, point: Vec<F192>, value: F192| {
            let (is_fixed, index) = self.layout.columns[column];
            let stack = if is_fixed {
                &self.layout.fixed
            } else {
                &self.layout.private
            };
            let claim = vm_pcs::SlotClaim::Point {
                offset: stack.placements[index].offset,
                low_point: point,
                value,
            };
            if is_fixed {
                fixed.push(claim);
            } else {
                private.push(claim);
            }
        };
        for claim in bus {
            add(claim.col, claim.point, claim.value);
        }
        for (index, claim) in tables.iter().enumerate() {
            for (column, &value) in claim.evals.iter().enumerate() {
                add(self.layout.spans[index].0 + column, claim.chi.clone(), value);
            }
        }
        if let Some((table, column)) = self.layout.flock {
            for &(dense, slot) in &self.tables[table].flock_slots {
                private.push(vm_pcs::SlotClaim::Strided {
                    offset: self.layout.private.placements[column].offset,
                    slot,
                    stride_log: hash_flock::SLOT_STRIDE_LOG,
                    point: tables[table].chi.clone(),
                    value: tables[table].evals[dense],
                });
            }
        }
        (fixed, private)
    }

    fn replay<'a>(&self, public: &[Field], proof: &'a Proof) -> Result<VerifierState<'a>, Error> {
        if public.len() != self.circuit.public_inputs() {
            return Err(Error::InvalidInput);
        }
        let mut vs = VerifierState::new(digest_words(self.digest), proof, digest_words(public_digest(public)));
        let rate = vs.next_scalar().map_err(|_| Error::InvalidProof)?;
        if rate.c1 != 0
            || rate.c2 != 0
            || !(vm_pcs::MIN_LOG_INV_RATE as u64..=vm_pcs::MAX_LOG_INV_RATE as u64).contains(&rate.c0)
        {
            return Err(Error::InvalidProof);
        }
        let log_inv_rate = rate.c0 as usize;
        let root = vm_pcs::read_commitment(&mut vs).map_err(|_| Error::InvalidProof)?;
        let wiring = Wiring::new(&self.tables, &self.layout, public);
        let bus = leaf::verify_balance(
            &wiring.blocks[0],
            &wiring.blocks[1],
            &wiring.blocks[2],
            &wiring.owners,
            &self.layout.spans,
            &mut vs,
        )
        .map_err(|_| Error::InvalidProof)?;
        let eta = vs.sample();
        let shared = form_powers(&self.tables, eta);
        let target = (0..3).fold(F192::ZERO, |sum, side| sum + shared[side] * bus.totals[side]);
        let claims = constraints::verify(
            &airs(&self.tables, &bus.forms, eta, shared),
            eta,
            &bus.point,
            target,
            &mut vs,
        )
        .map_err(|_| Error::InvalidProof)?;
        let (fixed_claims, private_claims) = self.claims(bus.claims, &claims);
        let reduction = if let Some((table, _)) = self.layout.flock {
            Some(
                hash_flock::verify_reduction(1 << self.tables[table].log_rows, &mut vs)
                    .map_err(|_| Error::InvalidProof)?,
            )
        } else {
            None
        };
        let rings: Vec<_> = reduction
            .as_ref()
            .map(|reduction| {
                let (table, column) = self.layout.flock.unwrap();
                hash_flock::ring_switch_verify(
                    1 << self.tables[table].log_rows,
                    self.layout.private.placements[column].offset,
                    &reduction.claim,
                )
            })
            .into_iter()
            .collect();
        vm_pcs::verify(
            &mut vs,
            &private_claims,
            &rings,
            self.layout.private.shape,
            log_inv_rate,
            &root,
        )
        .map_err(|_| Error::InvalidProof)?;
        vm_pcs::verify(
            &mut vs,
            &fixed_claims,
            &[],
            self.layout.fixed.shape,
            FIXED_LOG_INV_RATE,
            &self.fixed_root,
        )
        .map_err(|_| Error::InvalidProof)?;
        vs.finish().map_err(|_| Error::InvalidProof)?;
        Ok(vs)
    }

    pub fn verify(&self, public: &[Field], proof: &Proof) -> Result<(), Error> {
        self.replay(public, proof).map(|_| ())
    }

    pub fn raw_proof(&self, public: &[Field], proof: &Proof) -> Result<fiat_shamir::transcript::RawProof, Error> {
        Ok(self.replay(public, proof)?.into_raw_proof())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Builder, circuit::Operation};

    #[test]
    fn native_constraints_reject_forged_advice() {
        lean_vm::init_prover_pool();
        let builder = Builder::new();
        let word = builder.input(false);
        let inverse_input = builder.input(false);
        let inverse = builder.inverse(inverse_input);
        let bits = builder.bits(word, 192);
        let mut compression = [word; 14];
        for i in 0..4 {
            compression[8 + i] = builder.constant(Field::from(hash_flock::IV[i].0));
        }
        compression[12] = builder.constant(Field::from(64));
        compression[13] = builder.constant(Field::from(u32::MAX as u64));
        let outputs = builder.blake2s(compression);
        let public_wires: [_; 4] = std::array::from_fn(|i| {
            let wire = builder.input(true);
            builder.assert_equal(outputs[i], wire);
            wire
        });
        let key = Key::new(builder.finish()).unwrap();
        let message: Vec<_> = (0..8).flat_map(|_| 3u64.to_le_bytes()).collect();
        let digest = primitives::hash::hash(&message);
        let public: Vec<_> = (0..4)
            .map(|i| Field::from(u64::from_le_bytes(digest[8 * i..8 * i + 8].try_into().unwrap())))
            .collect();
        let private = [Field::from(3), Field::new(5, 7, 11)];
        let values = key.circuit.evaluate(&public, &private).unwrap();
        let valid = key.prove_values(&public, &values, 1).unwrap();
        key.verify(&public, &valid).unwrap();

        // Preserve recombination while making one bit non-Boolean.
        let mut forged = values.clone();
        forged[bits[0].index()] += Field::from(2);
        forged[bits[1].index()] += Field::ONE;
        let proof = key.prove_values(&public, &forged, 1).unwrap();
        assert!(key.verify(&public, &proof).is_err());

        let mut forged = values.clone();
        forged[inverse_input.index()] = Field::ZERO;
        forged[inverse.index()] = Field::ZERO;
        let proof = key.prove_values(&public, &forged, 1).unwrap();
        assert!(key.verify(&public, &proof).is_err());

        // Change both the output and its public equality, leaving Flock to reject it.
        let mut forged = values.clone();
        let mut changed = public.clone();
        forged[outputs[0].index()] += Field::ONE;
        forged[public_wires[0].index()] += Field::ONE;
        changed[0] += Field::ONE;
        let proof = key.prove_values(&changed, &forged, 1).unwrap();
        assert!(key.verify(&changed, &proof).is_err());

        // The low hash word remains correct; only the base-word constraint rejects this.
        let mut forged = values.clone();
        let mut changed = public.clone();
        let high = Field::new(0, 1, 0);
        forged[outputs[0].index()] += high;
        forged[public_wires[0].index()] += high;
        changed[0] += high;
        let proof = key.prove_values(&changed, &forged, 1).unwrap();
        assert!(key.verify(&changed, &proof).is_err());
    }

    fn scaled_key(coefficient: u64) -> Key {
        let builder = Builder::new();
        let input = builder.input(false);
        let output = builder.input(true);
        let product = builder.mul(input, builder.constant(Field::from(coefficient)));
        builder.assert_equal(product, output);
        Key::new(builder.finish()).unwrap()
    }

    #[test]
    fn expected_key_authenticates_fixed_metadata() {
        lean_vm::init_prover_pool();
        let mut expected = scaled_key(3);
        let same = scaled_key(3);
        assert_eq!(expected.digest(), same.digest());
        let alternate = scaled_key(5);
        let public = [Field::ZERO];
        let private = [Field::ZERO];
        let alternate_proof = alternate.prove(&public, &private, 1).unwrap();
        alternate.verify(&public, &alternate_proof).unwrap();
        assert!(expected.verify(&public, &alternate_proof).is_err());

        let valid = expected.prove(&public, &private, 1).unwrap();
        let mut values = expected.circuit.evaluate(&public, &private).unwrap();
        for operation in expected.circuit.operations() {
            if let Operation::Constant { output, value } = operation {
                assert_eq!(*value, Field::from(3));
                values[output.index()] = Field::from(5);
            }
        }
        let table = expected
            .tables
            .iter()
            .position(|table| table.kind == TableKind::Constant)
            .unwrap();
        let column = expected.layout.fixed_starts[table] + expected.tables[table].fixed.len() - 3;
        let offset = expected.layout.fixed.placements[column].offset;
        expected.fixed[offset] += F64(3 ^ 5);
        expected.verify(&public, &valid).unwrap();
        let forged = expected.prove_values(&public, &values, 1).unwrap();
        assert!(expected.verify(&public, &forged).is_err());
    }
}
