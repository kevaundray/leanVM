//! The columns of a circuit's bus that its wiring alone fixes.
//!
//! - Each slot's `next` column holds the key of the next slot of its wire class, its own key on a padding row.
//! - The public table's four constant columns hold each constant row's limbs, zero on the statement's rows.
//! - Each table with dynamic tuples has an activity column, one on the circuit's rows and zero on padding rows.
//!
//! Two circuits of the same heights differ exactly where these columns do, so the columns name the circuit.
//! A table the proof leaves out has no rows, so its columns are empty, and no block reads them.

use super::bus::SlotKey;
use super::circuit::{Circuit, Limbs, PubSource};
use super::table::{Heights, Table};
use crate::leaf::PublicColumn;
use primitives::field::F64;
use std::sync::Arc;

/// How many slots all tables have together.
const N_SLOTS: usize = Table::Pub.first_slot() + Table::Pub.n_slots();

/// One fixed column of a circuit's bus.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FixedColumn {
    /// The `next` column of a slot, by its index among all tables' slots.
    Next(usize),
    /// Limb `j` of the public table's constants.
    Constant(usize),
    /// The activity column of a table with dynamic tuples.
    Active(Table),
}

/// A circuit's fixed columns, each at its table's height, empty for a table the proof leaves out, in stacking order.
///
/// Every column is its own allocation, which a bus block shares.
#[derive(Clone, Debug)]
pub(crate) struct FixedColumns {
    /// The columns, in stacking order.
    columns: Vec<Arc<Vec<F64>>>,
}

impl FixedColumn {
    /// How many fixed columns a circuit has.
    pub(crate) const COUNT: usize = N_SLOTS + 4 + Table::DYNAMIC.len();

    /// The column at an index of the stacking order: every slot's `next`, then the four constant limbs, then the
    /// dynamic tables' activity columns.
    pub(crate) const fn at(index: usize) -> Self {
        if index < N_SLOTS {
            Self::Next(index)
        } else if index < N_SLOTS + 4 {
            Self::Constant(index - N_SLOTS)
        } else {
            Self::Active(Table::DYNAMIC[index - N_SLOTS - 4])
        }
    }

    /// Its index in the stacking order.
    pub(crate) const fn index(self) -> usize {
        match self {
            Self::Next(slot) => slot,
            Self::Constant(j) => N_SLOTS + j,
            Self::Active(table) => {
                let mut i = 0;
                while Table::DYNAMIC[i] as usize != table as usize {
                    i += 1;
                }
                N_SLOTS + 4 + i
            }
        }
    }

    /// The table whose height the column has.
    pub(crate) fn table(self) -> Table {
        match self {
            Self::Next(slot) => (Table::ALL.into_iter().rev())
                .find(|t| t.first_slot() <= slot)
                .expect("slot 0 is the first table's"),
            Self::Constant(_) => Table::Pub,
            Self::Active(table) => table,
        }
    }
}

impl FixedColumns {
    /// The fixed columns of a circuit at the given table heights.
    ///
    /// The slots of a wire class, in table, row and slot order, form one cycle: each slot's `next` is the following one's key.
    pub(crate) fn of(circuit: &Circuit, taus: &Heights) -> Self {
        let height = |t: Table| taus[t].map_or(0, |tau| 1 << tau);
        let mut next: Vec<Vec<F64>> = (Table::ALL.into_iter())
            .flat_map(|t| {
                let height = height(t);
                (0..t.n_slots()).map(move |s| (0..height).map(|z| SlotKey::new(t, s, z).to_f64()).collect())
            })
            .collect();
        let mut link = |from: SlotKey, to: SlotKey| next[from.global_slot()][from.row()] = to.to_f64();

        // Each class's first and last slot so far: every slot links the last to itself.
        let mut ends: Vec<Option<(SlotKey, SlotKey)>> = vec![None; circuit.n_classes()];
        for t in Table::ALL {
            let n = t.n_slots();
            for (i, &class) in circuit.classes.of(t).iter().enumerate() {
                let key = SlotKey::new(t, i % n, i / n);
                match &mut ends[class as usize] {
                    Some((_, last)) => {
                        link(*last, key);
                        *last = key;
                    }
                    end @ None => *end = Some((key, key)),
                }
            }
        }
        // The last slot closes the cycle back to the first.
        for (first, last) in ends.into_iter().flatten() {
            link(last, first);
        }

        let mut constants: [Vec<F64>; 4] = std::array::from_fn(|_| vec![F64::ZERO; height(Table::Pub)]);
        for (z, source) in circuit.pubs.iter().enumerate() {
            if let PubSource::Const(v) = *source {
                for (column, &v) in constants.iter_mut().zip(&v) {
                    column[z] = F64(v);
                }
            }
        }
        let active: [Vec<F64>; 2] = Table::DYNAMIC.map(|t| {
            let rows = circuit.classes.len(t);
            (0..height(t)).map(|z| F64(u64::from(z < rows))).collect()
        });
        Self {
            columns: next.into_iter().chain(constants).chain(active).map(Arc::new).collect(),
        }
    }

    /// Zero columns at the given heights: what a circuit built from shapes alone reads, whose rows never depend on them.
    pub(crate) fn zeros(taus: &Heights) -> Self {
        let columns = (0..FixedColumn::COUNT)
            .map(|c| {
                Arc::new(vec![
                    F64::ZERO;
                    taus[FixedColumn::at(c).table()].map_or(0, |tau| 1 << tau)
                ])
            })
            .collect();
        Self { columns }
    }

    /// A column.
    pub(crate) fn get(&self, column: FixedColumn) -> &Arc<Vec<F64>> {
        &self.columns[column.index()]
    }

    /// Set one word of a column.
    #[cfg(test)]
    pub(crate) fn set(&mut self, column: FixedColumn, z: usize, value: F64) {
        Arc::make_mut(&mut self.columns[column.index()])[z] = value;
    }

    /// A column as a bus coordinate reads it, naming which fixed column it is.
    pub(crate) fn public(&self, column: FixedColumn) -> PublicColumn {
        PublicColumn::fixed(Arc::clone(self.get(column)), column)
    }

    /// `next` and the bus's `next` key of every slot of the circuit's rows, per table, row-major, as `CheckRec` reads them.
    #[cfg(feature = "circuit-trace")]
    pub(crate) fn dump_next(&self, circuit: &Circuit) -> String {
        use std::fmt::Write;
        let mut next = String::from("next\n");
        for t in Table::ALL {
            let n = t.n_slots();
            let rows = circuit.classes.of(t).len() / n;
            let _ = write!(next, "table {}", rows * n);
            for z in 0..rows {
                for s in 0..n {
                    let _ = write!(next, " {}", self.get(FixedColumn::Next(t.first_slot() + s))[z].0);
                }
            }
            next.push('\n');
        }
        next
    }

    /// The public table's four value columns: the constants, with the statement's words on their rows, which come first.
    pub(crate) fn public_values(&self, statement: &[Limbs]) -> [PublicColumn; 4] {
        std::array::from_fn(|j| {
            let mut column = self.get(FixedColumn::Constant(j)).to_vec();
            for (cell, word) in column.iter_mut().zip(statement) {
                *cell = F64(word[j]);
            }
            PublicColumn::new(Arc::new(column))
        })
    }
}
