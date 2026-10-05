//! The public proof structure: the global column order, the bus blocks, the producers, and where every claim lands.
//!
//! The verifier rebuilds it from the program and the prover's announced sizes, with no witness value.
//!
//! The blocks name columns by index, so the layout is pure public structure.
//!
//! Each enum's declaration order is protocol order.
//!
//! The Python verifier mirrors it, so reordering a variant changes the proof layout.

use super::MAX_LOG_ROWS;
use super::error::CpuError;
use super::execute::Trace;
use crate::arith::Arith;
use crate::constraints::Claims;
use crate::leaf::{Block, ColumnClaim, Coord, Producer, PublicColumn, SparseColumn};
use crate::pcs::{Piece, Rate, RingClaim, RingSwitch, SliceClaim, StackClaim, Term};
use crate::rv::{Entry, Reg, Region, RegisterFile, RiscvProgram, Syscall};
use crate::tables::{ClassSpec, ClassTable, Clock, Part, Separator};
use crate::witness::{Placement, Source, StackShape};
use crate::{class_flock, pcs, tables, witness};
use ::pcs::pack::PACKING_WIDTH;
use Coord::{Col, Const, IntIndex, Sparse};
use fiat_shamir::transcript::{ProverState, Receiver, Transmitter, VerifierState};
use primitives::field::{F64, F192};
use std::sync::{Arc, OnceLock};

/// The bus blocks no table owns, which each side of the bus starts with.
///
/// Each has a push block and a pull block of the same height.
///
/// - The push block seeds an array, or starts the run.
/// - The pull block finalizes it, or ends the run, with committed columns.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Framework {
    /// The run's boundary: it starts at the entry point on cycle 1 and ends on the halt slot.
    State,
    /// The register file.
    Registers,
    /// RAM.
    Ram,
    /// The advice.
    Advice,
}

impl Framework {
    /// Every framework block, in bus order.
    pub const ALL: [Self; 4] = [Self::State, Self::Registers, Self::Ram, Self::Advice];

    /// Where the final clock sits in the state's finalizing tuple, twice: the run's last state is `(pc, ts)` at slot zero.
    pub(crate) const FINAL_CLOCK: [usize; 2] = [2, 3];

    /// The base-two logarithm of the block's rows: one per cell of its array.
    pub const fn log_rows(self, sizes: Sizes) -> usize {
        match self {
            Self::State => 0,
            Self::Registers => RegisterFile::LOG_CELLS,
            Self::Ram => sizes.log_ram,
            Self::Advice => sizes.log_advice,
        }
    }

    /// The block's two tuples: the push side's seed, then the pull side's finalization.
    fn tuples(self, p: &RiscvProgram, ts_final: u64) -> (Vec<Coord>, Vec<Coord>) {
        // A read-write array: each cell starts at the seed's clock holding `init`.
        //
        // It ends at its last timestamp holding its final word (§sec:memchan).
        let array = |sep: F64, cell: Coord, init: Option<Coord>, ts: Shared, fin: Shared| {
            let seed = [Const(sep), cell.clone(), Const(F64(Clock::SEED_CLOCK))]
                .into_iter()
                .chain(init)
                .collect();
            (seed, vec![Const(sep), cell, Col(ts.col()), Col(fin.col())])
        };

        // Word `z` of a memory region sits at `base + 8z`.
        let word = |base: u64| IntIndex {
            base: F64(base),
            shift: 3,
        };

        match self {
            // The run starts at the entry point and ends on the halt slot; a wrong clock leaves the end unmatched.
            Self::State => (
                vec![
                    Separator::State.coordinate(),
                    Const(F64(p.entry_pc())),
                    Const(F64(Clock::CLOCK_START)),
                    Const(F64::ZERO),
                ],
                vec![
                    Separator::State.coordinate(),
                    Const(F64(p.halt_pc())),
                    Const(F64(ts_final)),
                    Const(F64(ts_final)),
                ],
            ),
            // Register `i` is cell `i`, starting at zero.
            Self::Registers => {
                let cell = IntIndex {
                    base: F64::ZERO,
                    shift: 0,
                };
                array(Separator::Registers.value(), cell, None, Shared::RegTs, Shared::RegFin)
            }
            // RAM starts as the program's image, then zeros, all public.
            Self::Ram => {
                let image = Sparse(Arc::new(SparseColumn::new(p.log_ram(), &[(0, p.image())])));
                array(
                    Separator::Memory.value(),
                    word(Region::RAM.base()),
                    Some(image),
                    Shared::RamTs,
                    Shared::RamFin,
                )
            }
            // The one array seeded from a committed column: the prover's words.
            Self::Advice => array(
                Separator::Memory.value(),
                word(Region::ADVICE.base()),
                Some(Col(Shared::AdvInit.col())),
                Shared::AdvTs,
                Shared::AdvFin,
            ),
        }
    }
}

/// How many public columns a bytecode entry has.
///
/// They are the class tag, `flags`, `a1`, `a2`, `ad`, `imm`, `pc4`, `dt`, `link` and `jalr` (§sec:e2e-bc).
///
/// Then come a zero verdict and the exit selector.
pub const N_BYTECODE_COLUMNS: usize = tables::EXIT_SLOT + 1 - crate::leaf::BYTECODE_PUBLIC_SLOT;

/// The read-only arrays (§sec:lookup).
///
/// Their table side is a producer rather than a pair of framework blocks.
///
/// It pushes every entry as often as it is read, which a committed multiplicity column says.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Lookup {
    /// The program: one entry per instruction slot.
    Bytecode,
}

impl Lookup {
    /// Every lookup array, in producer order.
    pub const ALL: [Self; 1] = [Self::Bytecode];

    /// The base-two logarithm of the array's entries.
    pub const fn log_rows(self, sizes: Sizes) -> usize {
        match self {
            Self::Bytecode => sizes.log_bytecode,
        }
    }

    /// The committed column of how often each entry is read.
    pub const fn multiplicity(self) -> Shared {
        match self {
            Self::Bytecode => Shared::BytecodeMult,
        }
    }

    /// How many bits of its multiplicities the array's producer puts on the bus.
    ///
    /// Enough for the most reads tables of these heights can make of it.
    ///
    /// Completeness only: no read count is too large for soundness.
    pub fn multiplicity_bits(self, taus: [usize; tables::N_TABLES]) -> usize {
        match self {
            // Every row reads the bytecode once.
            Self::Bytecode => {
                let rows: u64 = taus.iter().map(|&tau| 1u64 << tau).sum();
                (u64::BITS - rows.leading_zeros()) as usize
            }
        }
    }

    /// The tuple the array's producer pushes for each entry, none of it committed.
    pub fn tuple(self, p: &RiscvProgram) -> Vec<Coord> {
        match self {
            // Entry `i` at its byte address, four bytes after the preceding one, then the program's public columns.
            Self::Bytecode => {
                let pc = Coord::IntIndex {
                    base: F64(Region::TEXT.base()),
                    shift: 2,
                };
                [Separator::Bytecode.coordinate(), pc]
                    .into_iter()
                    .chain(
                        self.columns(p)
                            .into_iter()
                            .map(|c| Coord::Public(PublicColumn::new(Arc::new(c)))),
                    )
                    .collect()
            }
        }
    }

    /// The array's stacked polynomial: its columns at their bus tuple coordinates.
    ///
    /// It makes the array's whole share of a bus leaf one evaluation.
    ///
    /// For the bytecode, it is what an outer verifier is handed in place of a structured program.
    ///
    /// It is also what the program digest binds.
    pub fn table(self, p: &RiscvProgram) -> Vec<F64> {
        crate::leaf::stacked_bytecode_table(self.log_rows(Sizes::of(p)), &self.tuple(p))
    }

    /// The array's public columns over its entries, in tuple order after the address.
    pub fn columns(self, p: &RiscvProgram) -> Vec<Vec<F64>> {
        match self {
            // The program's columns, in bytecode slot order.
            Self::Bytecode => {
                let entries = p.entries();
                let column = |f: &(dyn Fn(usize, &Entry) -> u64 + Sync)| {
                    parallel::map_collect(entries.len(), |i| F64(f(i, &entries[i])))
                };
                vec![
                    // An illegal entry's tag is zero, which is no table's: nothing can read it.
                    parallel::map_collect(entries.len(), |i| {
                        ClassTable::index_of(entries[i].class).map_or(F64::ZERO, primitives::field::g_pow)
                    }),
                    column(&|_, e| e.flags),
                    column(&|_, e| e.a1 as u64),
                    column(&|_, e| e.a2 as u64),
                    column(&|_, e| e.ad as u64),
                    column(&|_, e| e.imm),
                    column(&|i, _| p.pc_of(i).wrapping_add(4)),
                    column(&|i, _| p.dt_of(i)),
                    column(&|_, e| e.link as u64),
                    column(&|_, e| e.jalr as u64),
                    column(&|_, _| 0),
                    column(&|_, e| e.is_exit() as u64),
                ]
            }
        }
    }
}

/// The committed columns no table owns, first in the global column order.
///
/// What is committed is what each array holds after the run, and each cell's last timestamp (§sec:memchan).
///
/// - The program is public, not committed: only the multiplicities of its reads are.
/// - The registers start at zero and RAM at the program's image, both public.
/// - The advice is the one array whose initial words are committed too: they are the prover's.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Shared {
    /// Each register's final value.
    RegFin,
    /// Each register's final timestamp, the seed's if never accessed.
    RegTs,
    /// Each RAM word's final value.
    RamFin,
    /// Each RAM word's final timestamp.
    RamTs,
    /// Each advice word's initial value, the prover's.
    AdvInit,
    /// Each advice word's final value.
    AdvFin,
    /// Each advice word's final timestamp.
    AdvTs,
    /// How often each bytecode entry is read (§sec:lookup).
    ///
    /// Entry `x`'s word is the integer `m_x`.
    ///
    /// Its bits are the producer's one-bit columns, opened by ring switching.
    BytecodeMult,
}

impl Shared {
    /// Every shared column, in global column order.
    pub const ALL: [Self; 8] = [
        Self::RegFin,
        Self::RegTs,
        Self::RamFin,
        Self::RamTs,
        Self::AdvInit,
        Self::AdvFin,
        Self::AdvTs,
        Self::BytecodeMult,
    ];

    /// The column's global index: its position in the declaration.
    pub const fn col(self) -> usize {
        self as usize
    }

    /// The base-two logarithm of the column's rows: one per cell or entry of its array.
    pub const fn log_rows(self, sizes: Sizes) -> usize {
        match self {
            Self::RegFin | Self::RegTs => Framework::Registers.log_rows(sizes),
            Self::RamFin | Self::RamTs => Framework::Ram.log_rows(sizes),
            Self::AdvInit | Self::AdvFin | Self::AdvTs => Framework::Advice.log_rows(sizes),
            Self::BytecodeMult => Lookup::Bytecode.log_rows(sizes),
        }
    }

    /// The column's values as the run left them.
    ///
    /// A multiplicity column has none: it is counted from the rows.
    pub(super) fn values(self, trace: &Trace) -> Option<&[F64]> {
        Some(match self {
            Self::RegFin => &trace.reg_fin,
            Self::RegTs => &trace.reg_ts,
            Self::RamFin => &trace.ram_fin,
            Self::RamTs => &trace.ram_ts,
            Self::AdvInit => &trace.adv_init,
            Self::AdvFin => &trace.adv_fin,
            Self::AdvTs => &trace.adv_ts,
            Self::BytecodeMult => return None,
        })
    }
}

// Invariant: `Shared::ALL` lists the variants in declaration order.
//
// A column's index is its discriminant, and the stack is built in the order of `ALL`.
//
// So the two orders must be one, or a column's claims would land in another column's window.
const _: () = {
    let mut i = 0;
    while i < Shared::ALL.len() {
        assert!(Shared::ALL[i] as usize == i);
        i += 1;
    }
};

/// The index of the first packed flock witness, right after the shared columns.
///
/// Each table has two packed witnesses: every class circuit's in table order, then every clock circuit's.
///
/// Each is the sole copy of its circuit's words, committed in the same stack as every other column.
pub const Q_BASE: usize = Shared::ALL.len();

/// The columns before the first table's: the shared ones, then the packed witnesses.
pub const N_SHARED: usize = Q_BASE + class_flock::N_FLOCKS;

/// The committed column holding packed witness `f`.
pub(crate) const fn q_column(f: usize) -> usize {
    Q_BASE + f
}

/// The program's sizes the layout depends on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Sizes {
    /// The base-two logarithm of the program's entries.
    pub log_bytecode: usize,
    /// The base-two logarithm of RAM's words.
    pub log_ram: usize,
    /// The base-two logarithm of the advice's words.
    pub log_advice: usize,
}

impl Sizes {
    /// The sizes of `p`.
    pub fn of(p: &RiscvProgram) -> Self {
        Self {
            log_bytecode: crate::log2_strict_usize(p.entries().len()),
            log_ram: p.log_ram(),
            log_advice: p.log_advice(),
        }
    }

    /// Where every column of a program of these sizes sits in the stacked witness, for tables of these heights, and the stack's shape.
    ///
    /// No witness is needed.
    pub(super) fn stack(self, heights: [usize; tables::N_TABLES]) -> (Vec<Placement>, StackShape) {
        witness::placements_of(&self.column_sources(heights))
    }

    /// Every column's source, in global order.
    ///
    /// - The shared columns, at their arrays' sizes.
    /// - The packed witnesses, at their tables' proven sizes times their instance strides.
    /// - Each table's columns, at its proven size.
    ///
    /// A table's columns and packed witnesses commit [`committed_rows`] of their rows (§sec:jagged).
    ///
    /// A circuit word is a port of its class's packed witness, which already holds it.
    ///
    /// So it is never committed again: its bus claims settle against that witness.
    pub(super) fn column_sources(self, heights: [usize; tables::N_TABLES]) -> Vec<Source> {
        let taus: [usize; tables::N_TABLES] = std::array::from_fn(|t| tau_of(t, heights[t]));
        let jagged = |t: usize, stride_log: usize| Source::Committed {
            row_vars: taus[t],
            stride_log,
            rows: committed_rows(heights[t], taus[t]),
        };
        let mut sources: Vec<Source> = Shared::ALL.iter().map(|c| Source::full(c.log_rows(self))).collect();

        // The packed witnesses: every class circuit's, then every clock circuit's.
        sources.extend((0..class_flock::N_FLOCKS).map(|f| {
            let (t, part) = class_flock::flock(f);
            jagged(t, class_flock::stride_log(ClassSpec::ALL[t], part))
        }));

        // Each table's columns, its circuit words turned into ports of its packed witnesses.
        for (t, table) in ClassTable::all().iter().enumerate() {
            let base = sources.len();
            sources.resize(base + table.n_committed_columns(), jagged(t, 0));
            for part in [Part::Class, Part::Clock] {
                for (port, c) in table.word_columns(part) {
                    sources[base + c] = Source::Port {
                        column: q_column(class_flock::flock_index(t, part)),
                        port,
                        stride_log: class_flock::stride_log(ClassSpec::ALL[t], part),
                    };
                }
            }
        }
        debug_assert_eq!(sources.len(), Schema::get().n);
        sources
    }
}

/// A table's base-two logarithm of rows as proven: its height padded to a power of two, and to flock's instance floor.
pub const fn tau_of(t: usize, height: usize) -> usize {
    class_flock::n_blocks_log(ClassSpec::ALL[t], height)
}

/// The rows a table's columns commit: its live rows, then the first padding row, which every later one repeats (§sec:jagged).
pub const fn committed_rows(height: usize, tau: usize) -> usize {
    if height < 1 << tau { height + 1 } else { 1 << tau }
}

/// Where each table's columns sit in the global column order.
///
/// The shared columns and the packed witnesses come first.
///
/// Then each table, in table order, owns a contiguous span of columns.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Schema {
    /// Each table's first column and its number of columns.
    pub spans: [(usize, usize); tables::N_TABLES],
    /// The total number of columns.
    pub n: usize,
}

impl Schema {
    /// The schema of the fixed table set, computed once.
    pub fn get() -> &'static Self {
        static SCHEMA: OnceLock<Schema> = OnceLock::new();
        SCHEMA.get_or_init(|| {
            // Each table's span starts where the previous one ends.
            let mut next = N_SHARED;
            let spans = ClassTable::all().each_ref().map(|table| {
                let span = (next, table.n_committed_columns());
                next += span.1;
                span
            });
            Self { spans, n: next }
        })
    }
}

/// The public proof structure: everything the verifier rebuilds from the program and the announced sizes.
pub struct Layout {
    /// The push side's blocks: the framework's, then each table's.
    pub push: Vec<Block>,
    /// The pull side's blocks: the framework's, then each table's.
    pub pull: Vec<Block>,
    /// The lookup arrays' table sides, in lookup order (§sec:lookup).
    pub producers: Vec<Producer>,
    /// Where each column sits in the stacked witness, from the columns' sizes alone.
    pub placements: Vec<Placement>,
    /// The stacked witness's shape: its announced size, and how many lane blocks are committed.
    pub shape: StackShape,
    /// Each table's announced height, its live rows (§sec:jagged).
    pub heights: [usize; tables::N_TABLES],
    /// Each table's base-two logarithm of rows as proven, its height padded.
    pub taus: [usize; tables::N_TABLES],
}

impl Layout {
    /// The layout of a run of `p` with these table heights, ending on clock `ts_final`.
    ///
    /// A table's rows past its height are padding (§sec:jagged): they repeat the row at its height.
    ///
    /// Its bus blocks take the identity there, so the bus is over its live rows.
    pub fn new(p: &RiscvProgram, heights: [usize; tables::N_TABLES], ts_final: u64) -> Self {
        let sizes = Sizes::of(p);
        let taus: [usize; tables::N_TABLES] = std::array::from_fn(|t| tau_of(t, heights[t]));

        // The framework's blocks open both sides, one push and one pull block each.
        let (mut push, mut pull) = (Vec::new(), Vec::new());
        for block in Framework::ALL {
            let kappa = block.log_rows(sizes);
            let (seed, finalize) = block.tuples(p, ts_final);
            push.push(Block::framework(kappa, seed));
            pull.push(Block::framework(kappa, finalize));
        }

        // Each table declares its flushes in local column indices, offset here to its global span.
        let schema = Schema::get();
        for (t, table) in ClassTable::all().iter().enumerate() {
            let (base, kappa) = (schema.spans[t].0, taus[t]);
            let flushes = table.flushes();
            push.extend(
                flushes
                    .push
                    .into_iter()
                    .map(|c| Block::table(t, kappa, c.into_iter().map(|c| c.offset(base)).collect())),
            );
            pull.extend(
                flushes
                    .pull
                    .into_iter()
                    .map(|c| Block::table(t, kappa, c.into_iter().map(|c| c.offset(base)).collect())),
            );
        }

        // Each lookup array's producer: its tuple, its multiplicity column, and how many bits of it the bus reads.
        let producers = Lookup::ALL
            .into_iter()
            .map(|lookup| Producer {
                kappa: lookup.log_rows(sizes),
                coords: lookup.tuple(p),
                col: lookup.multiplicity().col(),
                bits: lookup.multiplicity_bits(taus),
            })
            .collect();

        let (placements, shape) = sizes.stack(heights);
        Self {
            push,
            pull,
            producers,
            placements,
            shape,
            heights,
            taus,
        }
    }

    /// Packed witness `f`'s column in the stack.
    pub(crate) fn witness_column(&self, f: usize) -> &witness::Column {
        self.placements[q_column(f)]
            .column()
            .expect("a packed witness is committed")
    }

    /// A producer's multiplicity column in the stack.
    pub(crate) fn multiplicity_column(&self, p: &Producer) -> &witness::Column {
        self.placements[p.col]
            .column()
            .expect("a multiplicity column is committed")
    }

    /// Whether table `t` has padding rows: rows past its height, which repeat the row at its height and which the bus leaves out.
    pub(crate) const fn padded(&self, t: usize) -> bool {
        self.heights[t] < 1 << self.taus[t]
    }

    /// Every ring-switched region of the opening, prover and verifiers alike: a committed column's pieces, its claim weighing each at the claim's point (§sec:jagged).
    ///
    /// - Each packed witness, with its reduction's claim.
    /// - Each producer's multiplicity column, its bits' evaluations as the slices, then zeros up to 64.
    pub(crate) fn rings<A: Arith>(
        &self,
        a: &mut A,
        witnesses: impl IntoIterator<Item = SliceClaim<A::E>>,
        multiplicities: &[Claims<A::E>],
    ) -> Vec<RingSwitch<A::E>> {
        let zero = a.zero();
        let mut rings: Vec<RingSwitch<A::E>> = (witnesses.into_iter().enumerate())
            .map(|(f, claim)| ring(a, self.witness_column(f), claim))
            .collect();
        for (p, claims) in self.producers.iter().zip(multiplicities) {
            let claim = SliceClaim {
                suffix_point: claims.chi.clone(),
                s_hat_v: claims.evals_padded_with(PACKING_WIDTH, zero),
            };
            rings.push(ring(a, self.multiplicity_column(p), claim));
        }
        rings
    }

    /// Every claim the opening discharges, located in the stack, in the order that feeds the batch's weights.
    ///
    /// - The bus's framework claims.
    /// - The batch's per-table column claims.
    /// - Each padded table's padding row: its columns' values on the row at its height, which the padding rows repeat (§sec:jagged).
    /// - The exit's claims: the run halted on `exit`, returning `output` (§sec:e2e-pi).
    ///
    /// Prover and verifiers all assemble them here, so no claim can shift by one.
    pub(crate) fn opening_claims<A: Arith>(
        &self,
        a: &mut A,
        bus_claims: Vec<ColumnClaim<A::E>>,
        table_claims: &[Claims<A::E>],
        pads: &[Option<Vec<A::E>>],
        output: &[A::E; 4],
    ) -> Vec<StackClaim<A::E>> {
        let schema = Schema::get();
        let mut claims = bus_claims;
        claims.reserve(schema.n - N_SHARED);

        // Each table's column claims, at the batch's point.
        for (&(base, _), table) in schema.spans.iter().zip(table_claims) {
            claims.extend(table.evals.iter().enumerate().map(|(c, &value)| ColumnClaim {
                col: base + c,
                point: table.chi.clone(),
                value,
            }));
        }

        // The exit: the syscall register holds `exit`, and the output registers the output.
        //
        // Each is the final registers at the Boolean point naming the register.
        // Both parties know the value, so the claim is computed rather than sent.
        let exit = a.constant(F192::from(F64(Syscall::Exit.number())));
        let mut register_claim = |reg: Reg, value: A::E| ColumnClaim {
            col: Shared::RegFin.col(),
            point: (0..RegisterFile::LOG_CELLS)
                .map(|b| a.constant(F192::from(F64(((reg.index() >> b) & 1) as u64))))
                .collect(),
            value,
        };
        let exits: Vec<ColumnClaim<A::E>> = std::iter::once(register_claim(Reg::SYSCALL, exit))
            .chain((Reg::OUTPUTS.into_iter().zip(output)).map(|(reg, &value)| register_claim(reg, value)))
            .collect();

        let mut slots: Vec<StackClaim<A::E>> = claims.into_iter().map(|c| self.slot_claim(a, c)).collect();

        // The row a table's padding rows repeat is the one at its height, one row of each of its columns.
        let one = a.one();
        for ((&(base, _), row), &height) in schema.spans.iter().zip(pads).zip(&self.heights) {
            let Some(row) = row else { continue };
            slots.extend(
                row.iter()
                    .enumerate()
                    .map(|(c, &value)| self.padding_claim(base + c, height, value, one)),
            );
        }
        slots.extend(exits.into_iter().map(|c| self.slot_claim(a, c)));
        slots
    }

    /// A column claim, located in the stacked witness: one scaled term per piece of the column (§sec:jagged).
    ///
    /// - A committed column's claim weighs its pieces at the claim's point.
    /// - A port has no place of its own: its claim is a strided evaluation of its class's packed witness.
    ///
    /// The strided form freezes the low coordinates to the port's bits and the high ones to the claim's point.
    ///
    /// It is folded at the table's height, not the packed witness's, and joins the one opening.
    fn slot_claim<A: Arith>(&self, a: &mut A, c: ColumnClaim<A::E>) -> StackClaim<A::E> {
        match &self.placements[c.col] {
            Placement::Committed(column) => StackClaim {
                terms: terms(a, column, &c.point, c.point.len() - column.row_vars),
                point: c.point,
                slot: 0,
                stride_log: 0,
                value: c.value,
            },
            &Placement::Port {
                column,
                port,
                stride_log,
            } => StackClaim {
                terms: terms(
                    a,
                    self.placements[column]
                        .column()
                        .expect("a port is of a committed column"),
                    &c.point,
                    0,
                ),
                point: c.point,
                slot: port,
                stride_log,
                value: c.value,
            },
        }
    }

    /// A claim on a column's padding row, the row `height`: one row of the column's last piece, which holds it.
    ///
    /// That piece is the row alone, or the whole column when the height is one short of it.
    /// At the Boolean point naming the row every other row weighs zero, so the claim is that one row, with no point.
    fn padding_claim<E: Copy>(&self, col: usize, height: usize, value: E, one: E) -> StackClaim<E> {
        let (column, slot, stride_log) = match &self.placements[col] {
            Placement::Committed(column) => (column, 0, 0),
            &Placement::Port {
                column,
                port,
                stride_log,
            } => (
                self.placements[column]
                    .column()
                    .expect("a port is of a committed column"),
                port,
                stride_log,
            ),
        };
        let last = column.pieces.last().expect("a column has a piece");
        debug_assert!(
            (last.first_row..last.first_row + (1 << last.log_rows)).contains(&height),
            "a padded column's last piece holds its padding row"
        );
        StackClaim {
            point: Vec::new(),
            slot,
            stride_log,
            terms: vec![Term {
                offset: last.offset + ((height - last.first_row) << stride_log),
                n_vars: 0,
                scale: one,
            }],
            value,
        }
    }
}

/// A claim's terms on a committed column at `point`, its first `low_vars` coordinates a row's own and the rest the row point: one per piece of the column (§sec:jagged).
fn terms<A: Arith>(a: &mut A, column: &witness::Column, point: &[A::E], low_vars: usize) -> Vec<Term<A::E>> {
    (column.terms(a, &point[low_vars..], low_vars).into_iter())
        .map(|(offset, n_vars, scale)| Term { offset, n_vars, scale })
        .collect()
}

/// A committed column as a ring-switched region, its pieces, holding one claim, which weighs each piece at its point's row coordinates (§sec:jagged).
fn ring<A: Arith>(a: &mut A, column: &witness::Column, claim: SliceClaim<A::E>) -> RingSwitch<A::E> {
    let pieces = (column.pieces.iter())
        .map(|p| Piece {
            offset: p.offset,
            n_vars: column.stride_log + p.log_rows,
        })
        .collect();
    let scales = column.scales(a, &claim.suffix_point[column.stride_log..]);
    RingSwitch {
        pieces,
        claims: vec![RingClaim { slices: claim, scales }],
    }
}

/// The sizes the prover announces before committing: each table's height, the rate, and the final clock.
///
/// The program's own sizes are public, so they are never announced.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Announcement {
    /// Each table's height: its live rows.
    pub(super) heights: [usize; tables::N_TABLES],
    /// The commitment's base-two logarithm of the inverse rate.
    pub(super) log_inv_rate: usize,
    /// The clock the run ended on: the final state's timestamp (§sec:state).
    pub(super) ts_final: u64,
}

impl Announcement {
    /// Write the announcement onto the scalar stream, which binds it into the transcript.
    ///
    /// Heights, not log heights: a table's rows past its height are padding, which the bus leaves out and the commitment stores once (§sec:jagged).
    ///
    /// So the height is what the layout and the bus are made of.
    pub(super) fn write(&self, ps: &mut ProverState) {
        for &height in &self.heights {
            ps.add_scalar(F192::new(height as u64, 0, 0));
        }
        ps.add_scalar(F192::new(self.log_inv_rate as u64, 0, 0));
        ps.add_scalar(F192::new(self.ts_final, 0, 0));
    }

    /// Read an announcement off the scalar stream, and check every value is in range.
    ///
    /// The checks run before any reduction, so an out-of-range announcement costs nothing.
    ///
    /// # Errors
    ///
    /// Refuses a non-canonical size, a final clock that is not live, a table height or a rate outside its range.
    pub(super) fn read(vs: &mut VerifierState) -> Result<Self, CpuError> {
        // A size is a canonical integer in the first coordinate.
        let read_size = |vs: &mut VerifierState| -> Result<usize, CpuError> {
            let word = vs.next_scalar()?;
            if word.c1 != 0 || word.c2 != 0 {
                return Err(CpuError::NonCanonicalSize);
            }
            usize::try_from(word.c0).map_err(|_| CpuError::NonCanonicalSize)
        };
        let mut heights = [0usize; tables::N_TABLES];
        for height in &mut heights {
            *height = read_size(vs)?;
        }
        let log_inv_rate = read_size(vs)?;

        // A live clock at slot zero: neither a padding row's clock nor a failed row's can end the run.
        let ts_final = vs.next_scalar()?;
        let live = ts_final.c0 >> Clock::LIVE_BIT == 1 && ts_final.c0.is_multiple_of(Clock::CYCLE);
        if !live || ts_final.c1 != 0 || ts_final.c2 != 0 {
            return Err(CpuError::FinalClock);
        }

        Layout::check_heights(&heights)?;

        // A rate the commitment supports.
        if !u8::try_from(log_inv_rate).is_ok_and(|r| Rate::new(r).is_ok()) {
            return Err(CpuError::Rate { log_inv_rate });
        }
        Ok(Self {
            heights,
            log_inv_rate,
            ts_final: ts_final.c0,
        })
    }

    /// The layout the announced heights describe for `p`, its final clock zero.
    ///
    /// The verifier adds the announced clock's share itself.
    ///
    /// # Errors
    ///
    /// Refuses heights whose stacked witness the commitment does not take.
    pub(super) fn layout(&self, p: &RiscvProgram) -> Result<Layout, CpuError> {
        Layout::announced(p, self.heights)
    }
}

impl Layout {
    /// The layout a verifier rebuilds from announced heights, its final clock zero.
    ///
    /// # Errors
    ///
    /// Refuses a height above the cap, or heights whose stacked witness the commitment does not take.
    pub(crate) fn announced(p: &RiscvProgram, heights: [usize; tables::N_TABLES]) -> Result<Self, CpuError> {
        Self::check_heights(&heights)?;
        // The caps bound each height alone; the stacked size they imply is checked here.
        let layout = Self::new(p, heights, 0);
        if !(pcs::MIN_MU..=pcs::MAX_MU).contains(&layout.shape.mu) {
            return Err(CpuError::WitnessSize { mu: layout.shape.mu });
        }
        Ok(layout)
    }

    /// Check each table's height is at most the public cap.
    ///
    /// A table's rows are its class's runs, unbounded by the program's size, so it has a cap of its own.
    ///
    /// Any height below the cap has a layout: the padding rows bring it up to a power of two at or above flock's instance floor.
    fn check_heights(heights: &[usize; tables::N_TABLES]) -> Result<(), CpuError> {
        for (spec, &rows) in ClassSpec::ALL.iter().zip(heights) {
            if rows > 1 << MAX_LOG_ROWS {
                return Err(CpuError::TableHeight {
                    table: spec.name,
                    rows,
                    max: MAX_LOG_ROWS,
                });
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn multiplicity_bits_cover_every_read() {
        // Fixture: one table of 2^10 rows, the rest of 2^3.
        let mut taus = [3; tables::N_TABLES];
        taus[0] = 10;
        let rows: u64 = taus.iter().map(|&tau| 1u64 << tau).sum();

        // The bits hold the most reads one entry can get, every row reading it, and no more.
        let bits = Lookup::Bytecode.multiplicity_bits(taus);
        assert!(rows < 1 << bits);
        assert!(rows >= 1 << (bits - 1));
    }
}
