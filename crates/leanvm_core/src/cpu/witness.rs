//! The prover's witness: the stacked multilinear holding every committed piece, and the live stack of the columns that commit only some of their rows, built once from a run.

use super::MAX_LOG_ROWS;
use super::execute::Execution;
use super::layout::{Layout, Lookup, Schema, Shared, Sizes, committed_rows, q_column};
use super::program::Program;
use crate::class_flock::Prepared;
use crate::tables::{ClassSpec, ClassTable, ColumnOut, FillContext};
use crate::witness::Window;
use crate::{class_flock, tables};
use primitives::field::F64;
use std::mem::MaybeUninit;

/// The prover's witness: the committed stack `q`, the live stack of the columns that commit only some of their rows, and the public layout.
///
/// The bus and the table sumcheck read a table's columns in the live stack, or in `q` for a column committed whole.
pub(crate) struct Witness {
    /// The stacked multilinear the commitment takes: every committed column's pieces at their placed offsets.
    pub(crate) q: Vec<F64>,
    /// Every column that commits only some of its rows, at those rows, end to end.
    pub(crate) live: Vec<F64>,
    /// Each column's window in `live`.
    pub(crate) windows: Vec<Option<Window>>,
    /// The ports' values, by global column index, at their tables' committed rows.
    ///
    /// They carry data for the bus but are not committed, so they are not in the stack.
    pub(crate) virt: Vec<(usize, Vec<F64>)>,
    /// The public structure the witness fills.
    pub(crate) layout: Layout,
    /// The clock the run ended on, which the prover announces.
    pub(crate) ts_final: u64,
    /// Every circuit's flock batch, freed right after the batched reduction.
    pub(crate) reductions: Vec<Prepared>,
}

impl Witness {
    /// The witness of a finished run.
    ///
    /// # Panics
    ///
    /// Panics if a table is taller than the cap, or its rows are not its live rows then its padding row.
    pub(crate) fn build(program: &Program, exec: &Execution) -> Self {
        let (p, trace, schema) = (&program.rv, &exec.trace, Schema::get());
        assert!(
            trace.heights.iter().all(|&h| h <= 1 << MAX_LOG_ROWS),
            "a table exceeds 2^{MAX_LOG_ROWS} rows"
        );

        // The public layout comes first: it fixes each column's committed rows, so each is allocated once.
        let layout = Layout::new(p, trace.heights, trace.ts_final);

        // The executor wrote each table's live rows, then the padding row every later row repeats: its committed rows.
        let rows: [usize; tables::N_TABLES] = std::array::from_fn(|t| committed_rows(trace.heights[t], layout.taus[t]));
        for (t, table_rows) in trace.rows.iter().enumerate() {
            assert_eq!(
                table_rows.len(),
                rows[t],
                "the {} table is not its committed rows",
                ClassSpec::ALL[t].name
            );
        }

        // The committed stack and the live stack are each written exactly once: every piece and every window is filled in place.
        //
        // A column that commits only some of its rows is written at those rows, and each piece copied while it is in cache.
        //
        // One committed whole is written into its piece alone.
        let sources = Sizes::of(p).column_sources(trace.heights);
        let (live_windows, live_len) = crate::witness::live_windows(&sources);
        let mut live = Box::new_uninit_slice(live_len);
        let mut q = Box::new_uninit_slice(layout.shape.committed_len());

        // A port is not in the stack, so its values get a buffer of their own.
        let mut virt: Vec<(usize, Box<[MaybeUninit<F64>]>)> = Vec::new();
        for (t, &(base, width)) in schema.spans.iter().enumerate() {
            for i in (base..base + width).filter(|&i| layout.placements[i].column().is_none()) {
                virt.push((i, Box::new_uninit_slice(rows[t])));
            }
        }
        // SAFETY: `split_pieces` hands out pieces tiling `q` but its tail, zeroed below, and `split_stack` windows tiling all of `live`.
        // Each table checks it wrote every column it was given, the shared columns are written below, and each flock batch writes its pieces.
        let (pieces, tail) =
            crate::witness::split_pieces(unsafe { primitives::write_only(&mut q) }, &layout.placements);
        parallel::chunks_mut(tail, 1 << 16, |_, chunk| chunk.fill(F64::ZERO));

        // Each column's pieces as `(first row, piece)`; the packed witnesses' go to their flock batches.
        let mut pieces: Vec<Vec<(usize, &mut [F64])>> = (pieces.into_iter().zip(&layout.placements))
            .map(|(pieces, placement)| {
                placement
                    .column()
                    .map_or_else(Vec::new, |c| c.pieces.iter().map(|p| p.first_row).zip(pieces).collect())
            })
            .collect();
        let flocks: Vec<Vec<(usize, &mut [F64])>> = (0..class_flock::N_FLOCKS)
            .map(|f| std::mem::take(&mut pieces[q_column(f)]))
            .collect();
        // SAFETY: as above.
        let mut windows = crate::witness::split_stack(unsafe { primitives::write_only(&mut live) }, &live_windows);
        let mut outs: Vec<ColumnOut<'_>> = (windows.iter_mut().zip(pieces))
            .map(|(window, mut pieces)| {
                if window.is_empty() && pieces.len() == 1 {
                    // Committed whole: its one piece is the column.
                    ColumnOut {
                        rows: pieces.pop().expect("one piece").1,
                        pieces,
                    }
                } else {
                    ColumnOut {
                        rows: std::mem::take(window),
                        pieces,
                    }
                }
            })
            .collect();
        for (i, buf) in virt.iter_mut() {
            // SAFETY: each table checks that it writes every circuit port column in full.
            outs[*i].rows = unsafe { primitives::write_only(buf) };
        }

        crate::stage!("Fill columns", || {
            // Each table fills its own columns from the trace, in its global span.
            for (t, table) in ClassTable::all().iter().enumerate() {
                let (base, n) = schema.spans[t];
                let ctx = FillContext::new(trace, p, rows[t], n);
                table.fill(ctx, &mut outs[base..base + n]);
            }

            // Every shared column is written: the stack is uninitialized, so one left out would read garbage.
            for c in Shared::ALL {
                if let Some(values) = c.values(trace) {
                    outs[c.col()].rows.copy_from_slice(values);
                }
            }

            // What the run did not leave, the multiplicities, is counted from its rows.
            trace.count_reads(outs[Lookup::Bytecode.multiplicity().col()].rows);

            // The tables' register numbers, packed into their words.
            for word in &layout.registers {
                word.pack(&mut outs);
            }
        });

        // Release the borrows of the stacks and of the port buffers.
        drop(outs);

        // The packed witnesses, one instance per committed row of their table, each writing its committed pieces in place.
        let reductions = crate::stage!("Build flock witnesses", || {
            (flocks.into_iter().enumerate())
                .map(|(f, pieces)| {
                    let t = class_flock::flock(f).0;
                    Prepared::build(f, layout.taus[t], trace, p, pieces)
                })
                .collect()
        });

        // Release the windows' borrow of the live stack.
        drop(windows);
        // SAFETY: the fills above wrote every piece, window and port buffer, and the stack's tail is zeroed.
        let (q, live, virt) = unsafe {
            (
                q.assume_init().into_vec(),
                live.assume_init().into_vec(),
                virt.into_iter()
                    .map(|(i, buf)| (i, buf.assume_init().into_vec()))
                    .collect(),
            )
        };
        Self {
            q,
            live,
            windows: live_windows,
            virt,
            layout,
            ts_final: trace.ts_final,
            reductions,
        }
    }

    /// One read-only view per column, in global column order.
    ///
    /// A table's column is at its committed rows, every later row repeating the last: its window in the live stack, its piece of the committed stack when it is committed whole, or the private buffer of a port.
    ///
    /// A shared column is whole, and a packed witness's view is empty, its flock batch holding its words.
    pub(crate) fn columns(&self) -> Vec<&[F64]> {
        let mut cols: Vec<&[F64]> = (self.windows.iter().zip(&self.layout.placements))
            .map(|(w, p)| match (w, p.column()) {
                (Some(w), _) => &self.live[w.offset..w.offset + w.len],
                (None, Some(c)) if c.stride_log == 0 => {
                    debug_assert_eq!(c.pieces.len(), 1, "a column without a window is committed whole");
                    &self.q[c.pieces[0].offset..c.pieces[0].offset + (1 << c.row_vars)]
                }
                (None, _) => &[],
            })
            .collect();
        for (i, buf) in &self.virt {
            cols[*i] = buf;
        }
        cols
    }

    /// The committed data before the stack's zero pad: the real witness size.
    pub(crate) fn committed_size(&self) -> usize {
        crate::witness::committed_len(&self.layout.placements)
    }
}
