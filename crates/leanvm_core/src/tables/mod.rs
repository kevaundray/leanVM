//! Instruction tables: class specifications, local columns, bus tuples, and witness filling.
//!
//! Column and port order are protocol data mirrored by the Python verifier.
//! Circuit words are virtual columns bound to the machine through the bus.

mod bus;
mod clock;
mod columns;
mod fill;
mod spec;
mod table;
mod word;

pub use bus::FlushBuilder;
pub use clock::Clock;
pub use fill::ColumnOut;
pub use spec::{BAD_SLOT, BatchWitness, ClassSpec, EXIT_SLOT, InstanceWitness, N_CIRCUITS, N_TABLES, Ram};
pub use table::ClassTable;
pub use word::Word;

pub(crate) use bus::Separator;
pub(crate) use fill::FillContext;

/// One of a table's flock circuits: its class's function, which the extension-field table has none of, or its clock.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Part {
    /// Instruction semantics.
    Class,
    /// Memory access ordering.
    Clock,
}
