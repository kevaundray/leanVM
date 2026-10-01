//! Run the program on the reference interpreter ([`crate::rv::Machine`]) and record,
//! for every access, what the memory argument needs ([`Trace`]).

use super::*;
use crate::rv::{self, ADVICE_BASE, Class, LOG_REGS, Machine, RAM_BASE, Trap, hash, machine::compute};
use crate::tables::{CLASSES, CLOCK_STRIDE, RAM_SLOT, REG_SLOTS, block_slot};
use primitives::field::{F64, mul_by_g};

pub struct Execution {
    /// The public output: `a0..a3` as the run left them.
    pub output: [u64; 4],
    pub cycles: usize, // number of rows proven, padding rows included
    /// Rows per table before the padding rows: the work the program itself does, as
    /// against the power-of-two heights that get proven. Cost measurements want this one.
    pub base_counts: [usize; crate::tables::N_TABLES],
    pub(crate) trace: Trace, // rows and final timestamps, emitted in the same walk
}

/// What the memory argument keeps per cell of one read-write array (§sec:memchan):
/// its last access, as the clock's exponent and as its g-power.
struct Cells {
    last: Vec<u32>,
    last_ts: Vec<F64>,
}

impl Cells {
    /// Every cell starts last accessed at the seed's `g^0`.
    fn new(n: usize) -> Self {
        Self {
            last: vec![0; n],
            last_ts: vec![F64::ONE; n],
        }
    }

    /// Access `cell` at clock `y`, whose g-power is `ts`.
    #[inline(always)]
    fn access(&mut self, cell: usize, y: u32, ts: F64) -> Access {
        let (x, x_ts) = (self.last[cell], self.last_ts[cell]);
        self.last[cell] = y;
        self.last_ts[cell] = ts;
        // The clock only moves forward, and starts after the seed's zero.
        Access {
            x: x_ts,
            gap: y - x - 1,
        }
    }
}

/// `ts·g^k`.
fn advance(ts: F64, k: u32) -> F64 {
    (0..k).fold(ts, |t, _| mul_by_g(t))
}

impl Program {
    /// Run the program on `advice`, recording every row, then write out the
    /// padding rows that bring each table to a power of two ([`filler`]). A run that
    /// traps, or outruns the clock, has no proof.
    pub fn execute(&self, advice: &[u64]) -> Result<Execution, ProveError> {
        let p = &self.rv;
        let max = 1 << p.log_advice;
        if advice.len() > max {
            return Err(ProveError::AdviceTooLong { max, got: advice.len() });
        }
        let mut m = Machine::new(p, advice);
        let adv_init: Vec<F64> = m.advice().iter().map(|&w| F64(w)).collect();
        let mut regs = Cells::new(1 << LOG_REGS);
        // RAM's cells, then the advice's, as the machine numbers them.
        let mut ram = Cells::new((1 << p.log_ram) + (1 << p.log_advice));
        let cell_of = |address: u64| -> usize {
            if address >= RAM_BASE {
                ((address - RAM_BASE) / 8) as usize
            } else {
                (1 << p.log_ram) + ((address - ADVICE_BASE) / 8) as usize
            }
        };
        let mut rows: [Vec<Row>; crate::tables::N_TABLES] = std::array::from_fn(|_| Vec::new());

        // The clock, as an exponent and as its g-power: cycle 1, so that the first
        // access comes strictly after the seeds.
        let mut tick = CLOCK_STRIDE;
        let mut ts = crate::tables::CLOCK_START;
        while !m.halted() {
            // A cell's first access is measured from the seed, so the whole run has
            // to fit the range a gap can take (§sec:memchan).
            if tick >= u32::MAX - block_slot(hash::WORDS) {
                return Err(ProveError::TooLong);
            }
            let step = m.step()?;
            let e = &p.entries[step.index];
            let table = crate::tables::table_of(e.class).expect("every class that runs has a table");
            let spec = CLASSES[table];
            // The register accesses the class makes, then the RAM access if it has one.
            // Their order here is the order of their columns, not of their clock slots.
            let cells = [e.a1, e.a2, e.ad].map(|cell| cell as usize);
            // Why: a loop over all three slots unrolls, so every clock below is a constant power.
            let made = [true, spec.reads_rs2, spec.writes_rd];
            let mut acc = [Access::PADDING; 4];
            let mut n = 0;
            for (i, slot) in REG_SLOTS.into_iter().enumerate() {
                if made[i] {
                    acc[n] = regs.access(cells[i], tick + slot, advance(ts, slot));
                    n += 1;
                }
            }
            if let Some(access) = step.ram {
                let cell = cell_of(access.address);
                acc[n] = ram.access(cell, tick + RAM_SLOT, advance(ts, RAM_SLOT));
            }
            // A hash row's block, word `k` at `v1 ^ 8k`, after its register reads.
            let hash = step.hash.map(|h| {
                let mut all = [Access::PADDING; 2 + hash::WORDS];
                all[..n].copy_from_slice(&acc[..n]);
                for k in 0..hash::WORDS {
                    let cell = cell_of(step.v1 ^ (8 * k as u64));
                    all[n + k] = ram.access(cell, tick + block_slot(k), advance(ts, block_slot(k)));
                }
                Box::new(HashRow {
                    block: h.block,
                    out: h.out,
                    acc: all,
                })
            });
            rows[table].push(Row {
                index: step.index as u32,
                ts,
                v1: step.v1,
                v2: step.v2,
                out: step.out,
                taken: step.taken,
                vd_old: step.vd_old,
                ram: step.ram.unwrap_or_default(),
                acc,
                hash,
            });
            tick += spec.stride();
            ts = advance(ts, spec.stride());
        }
        let syscall = m.regs()[rv::SYSCALL_REG as usize];
        if syscall != rv::SYS_EXIT {
            return Err(Trap::NotAnExit { syscall }.into());
        }
        let output = rv::OUTPUT_REGS.map(|r| m.regs()[r as usize]);
        let base_counts: [usize; crate::tables::N_TABLES] = std::array::from_fn(|t| rows[t].len());

        // The padding rows, written out rather than executed: they sit at clock zero
        // and touch nothing, every read holding zero and every write rewriting what it
        // writes (`filler`). Their circuit instance is an honest one, on those zeros.
        for (first, size, traversals) in super::filler::cycles(&self.filler, base_counts) {
            for _ in 0..traversals {
                for index in first..=first + size {
                    let e = &p.entries[index];
                    let table = crate::tables::table_of(e.class).expect("a fill block's class has a table");
                    let (out, taken, access) = compute(e, 0, 0, 0);
                    // The row's accesses are all padding ones, in a hash row's own array.
                    let acc = [Access::PADDING; 4];
                    let hash = (e.class == Class::Hash).then(|| {
                        // The compression of a zero block, whose result the row rewrites.
                        let mut h = rv::machine::compute_hash([0; hash::WORDS], 0, e.flags);
                        h.block[hash::OUT as usize / 8..][..4].copy_from_slice(&h.out);
                        Box::new(HashRow {
                            block: h.block,
                            out: h.out,
                            acc: [Access::PADDING; 2 + hash::WORDS],
                        })
                    });
                    rows[table].push(Row {
                        index: index as u32,
                        ts: F64::ZERO,
                        v1: 0,
                        v2: 0,
                        out,
                        taken,
                        vd_old: if e.link { p.pc_of(index) + 4 } else { out },
                        ram: access,
                        acc,
                        hash,
                    });
                }
            }
        }

        let cycles = rows.iter().map(Vec::len).sum();
        let (ram_ts, adv_ts) = ram.last_ts.split_at(1 << p.log_ram);
        let trace = Trace {
            rows,
            reg_fin: m.regs().iter().map(|&r| F64(r)).collect(),
            reg_ts: regs.last_ts,
            ram_fin: m.ram().iter().map(|&w| F64(w)).collect(),
            ram_ts: ram_ts.to_vec(),
            adv_init,
            adv_fin: m.advice().iter().map(|&w| F64(w)).collect(),
            adv_ts: adv_ts.to_vec(),
            ts_final: ts,
        };
        Ok(Execution {
            output,
            cycles,
            base_counts,
            trace,
        })
    }
}
