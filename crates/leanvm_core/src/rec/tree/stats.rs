//! What a recursion circuit costs.

use super::{Kind, Tree};
use crate::rec::circuit::Circuit;
use crate::rec::table::Table;
use primitives::pretty_integer;
use std::fmt;

/// What a recursion circuit costs: one of a tree's, or a leanXMSS batch's.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct CircuitStats {
    /// Each table of the recursion machine, in the machine's order.
    pub tables: Vec<TableStats>,
    /// The words a proof of the circuit commits.
    pub committed: usize,
}

/// One table of a circuit: its rows, and the height they are padded to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct TableStats {
    /// The table's name.
    pub name: &'static str,
    /// The rows the circuit puts in the table.
    pub rows: usize,
    /// The base-two logarithm of the table's height, none if the proof leaves the table out.
    ///
    /// The height is a power of two, at least the rows.
    pub height_log: Option<usize>,
}

impl TableStats {
    /// The rows its proof has: its height, zero if the proof leaves it out.
    #[must_use]
    pub const fn height(&self) -> usize {
        match self.height_log {
            Some(tau) => 1 << tau,
            None => 0,
        }
    }
}

/// Its name, its rows and its height: `HASH 1,234 (2^11)`, or `STEP 0 (absent)` for a table the proof leaves out.
impl fmt::Display for TableStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} ", self.name, pretty_integer(&self.rows))?;
        match self.height_log {
            Some(tau) => write!(f, "(2^{tau})"),
            None => f.write_str("(absent)"),
        }
    }
}

impl CircuitStats {
    /// What a circuit costs.
    ///
    /// # Panics
    ///
    /// Panics if the circuit fits no commitment, which every caller has refused before.
    pub(crate) fn of(circuit: &Circuit) -> Self {
        // The circuit's rows per table, and the padded heights it is proven at.
        let (rows, heights) = (circuit.row_counts(), circuit.heights());

        // One entry per table of the recursion machine, in its order.
        let tables = (Table::ALL.iter())
            .map(|&table| TableStats {
                name: table.name(),
                rows: rows[table],
                height_log: heights[table],
            })
            .collect();

        let committed = circuit.committed_words().expect("the circuit fits one commitment");
        Self { tables, committed }
    }
}

impl Tree<'_> {
    /// What the circuit of one kind of node costs.
    #[must_use]
    pub fn stats(&self, kind: Kind) -> CircuitStats {
        // Invariant: building the tree refused any circuit that fits no commitment.
        CircuitStats::of(self.circuit(kind))
    }
}
