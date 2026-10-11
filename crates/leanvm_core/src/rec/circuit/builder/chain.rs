//! Hash chains on the dynamic bus: one `STEP` row per step, tied to its `HASH` row, and one `LINK` row per chain.
//!
//! A step pulls its input at its position's key and pushes its output at the next position's; a link pushes the
//! chain's tip at the position its digit names and pulls its end at position 7. The rows of a circuit balance only
//! if every key is pushed and pulled as often, with the same words.

use super::Builder;
use crate::rec::circuit::{Kw, PARAM_IV};
use crate::rec::clean::{LINK_A, LINK_D, LINK_E, LINK_T, LINK_W, STEP_A, STEP_J, STEP_O, STEP_T, STEP_V};
use crate::rec::table::Table;

/// The bits of a tweak word a step's columns hold: bit 8, always set, and the position and chain at bits 32 to 40.
const TWEAK_BITS: u64 = 0x100 | 0x1ff << 32;

impl Builder {
    /// One chain step: `T`, `v0`, `v1` as fresh `K` wires holding `tweak` and `v`, the hash row of the 6-word message
    /// `T, idx, p0, p1, v0, v1` from the parameter IV, and the step row reading `T`, `v`, the output's first three
    /// words, `tag` and `one`.
    ///
    /// Callers hold `one` to the constant one, so the step moves its position by one, and `tag` to a constant.
    pub fn chain_step(&mut self, idx: Kw, pp: [Kw; 2], tag: Kw, one: Kw, tweak: u64, v: [u64; 2]) {
        traced!(
            self,
            format!("chain_step {} {} {} {} {}", idx.0, pp[0].0, pp[1].0, tag.0, one.0),
            self.chain_step_rows(idx, pp, tag, one, tweak, v)
        );
    }

    fn chain_step_rows(&mut self, idx: Kw, pp: [Kw; 2], tag: Kw, one: Kw, tweak: u64, v: [u64; 2]) {
        let t = self.free_k(tweak);
        let v = v.map(|x| self.free_k(x));
        let z = self.k_zero();
        let h = self.d_const(PARAM_IV);
        let (_, ch) = self.leaf_block_rows(h, [t, idx, pp[0], pp[1], v[0], v[1], z, z], 48, true);
        let mut slots = [0u32; Table::Step.n_slots()];
        for (slot, w) in [
            (STEP_T, t.0),
            (STEP_V, v[0].0),
            (STEP_V + 1, v[1].0),
            (STEP_O, ch.0),
            (STEP_J, tag.0),
            (STEP_A, one.0),
        ] {
            slots[slot] = w;
        }
        self.row(Table::Step, &slots);
    }

    /// One chain: `t0`, `t1` and `e0`, `e1` as fresh `K` wires holding `tip` and `end`, and the link row reading
    /// `w`, the digit's bits `d`, the tip, the end and `one`. Returns the end's wires.
    ///
    /// Callers hold `one` to the constant one, so the link pulls the end at position 7.
    pub fn link(&mut self, w: Kw, d: [Kw; 3], one: Kw, tip: [u64; 2], end: [u64; 2]) -> [Kw; 2] {
        traced!(
            self,
            format!("link {} {} {} {} {}", w.0, d[0].0, d[1].0, d[2].0, one.0),
            self.link_rows(w, d, one, tip, end)
        )
    }

    fn link_rows(&mut self, w: Kw, d: [Kw; 3], one: Kw, tip: [u64; 2], end: [u64; 2]) -> [Kw; 2] {
        let t = tip.map(|x| self.free_k(x));
        let e = end.map(|x| self.free_k(x));
        let mut slots = [0u32; Table::Link.n_slots()];
        for (slot, w) in [
            (LINK_W, w.0),
            (LINK_D, d[0].0),
            (LINK_D + 1, d[1].0),
            (LINK_D + 2, d[2].0),
            (LINK_T, t[0].0),
            (LINK_T + 1, t[1].0),
            (LINK_E, e[0].0),
            (LINK_E + 1, e[1].0),
            (LINK_A, one.0),
        ] {
            slots[slot] = w;
        }
        self.row(Table::Link, &slots);
        e
    }

    /// Check the step and link rows on the values: each step's tweak word has the form its columns spell, each `a`
    /// is Boolean, and the dynamic tuples balance, every `(key, x0, x1)` pushed as often as pulled.
    pub(super) fn check_dynamic(&mut self) {
        let mut pushed = Vec::new();
        let mut pulled = Vec::new();
        let mut failures = Vec::new();
        for table in Table::DYNAMIC {
            let n = table.n_slots();
            let a = if table == Table::Step { STEP_A } else { LINK_A };
            for row in self.rows.of(table).chunks_exact(n) {
                let value = |s: usize| self.values[row[s] as usize];
                let t = value(STEP_T)[0];
                if table == Table::Step && (t & !TWEAK_BITS != 0 || t & 0x100 == 0) {
                    failures.push("a step's tweak word is tweak0(1, 8c + s)");
                }
                if value(a)[0] > 1 {
                    failures.push("a step's or link's a is Boolean");
                }
                let [push, pull] = table.row_dynamic(value).expect("a dynamic table");
                pushed.push(push.map(|x| x.0));
                pulled.push(pull.map(|x| x.0));
            }
        }
        pushed.sort_unstable();
        pulled.sort_unstable();
        if pushed != pulled {
            failures.push("the dynamic tuples balance");
        }
        for check in failures {
            self.fail(check);
        }
    }
}

/// Honest chains for tests, as planned rows a test may tamper with before they become rows.
#[cfg(test)]
pub(crate) mod testing {
    use super::Builder;
    use crate::rec::circuit::{Kw, chain};

    /// The hash message's index word and parameter words.
    const IDX: u64 = 0x1d;
    const PP: [u64; 2] = [0x77, 0x99];
    /// The tag every key carries, at bits 41 and up.
    const TAG: u64 = 3 << 41;

    /// A row of a test's chains.
    #[derive(Clone, Copy, Debug)]
    pub(crate) enum Planned {
        /// A step hashing `v` under the tweak word `tweak`.
        Step { tweak: u64, v: [u64; 2] },
        /// Chain `c`'s link: its digit, tip and end.
        Link { c: u64, d: u64, tip: [u64; 2], end: [u64; 2] },
    }

    /// The tweak word of position `s` of chain `c`: `tweak0(1, 8c + s)`.
    pub(crate) const fn tweak(c: u64, s: u64) -> u64 {
        0x100 | (8 * c + s) << 32
    }

    /// A step's output words, natively.
    pub(crate) fn step(tweak: u64, v: [u64; 2]) -> [u64; 2] {
        let o = chain(&[tweak, IDX, PP[0], PP[1], v[0], v[1]]);
        [o[0], o[1]]
    }

    /// The honest rows of chains with the given digits: chain `i` from its tip, a step per position from its digit to
    /// 6, then its link.
    pub(crate) fn plan(digits: &[u64]) -> Vec<Planned> {
        let mut rows = Vec::new();
        for (c, &d) in (0..).zip(digits) {
            let tip = [0x1000 + c, 0x2000 + c];
            let mut v = tip;
            for s in d..7 {
                rows.push(Planned::Step { tweak: tweak(c, s), v });
                v = step(tweak(c, s), v);
            }
            rows.push(Planned::Link { c, d, tip, end: v });
        }
        rows
    }

    impl Builder {
        /// The planned rows, each link's end a statement word.
        pub(crate) fn emit_chains(&mut self, plan: &[Planned]) {
            let idx = self.k_const(IDX);
            let pp = PP.map(|p| self.k_const(p));
            let tag = self.k_const(TAG);
            let one = self.k_const(1);
            for &row in plan {
                match row {
                    Planned::Step { tweak, v } => self.chain_step(idx, pp, tag, one, tweak, v),
                    Planned::Link { c, d, tip, end } => {
                        let w = self.k_const(tweak(c, 0) | TAG);
                        let d: [Kw; 3] = std::array::from_fn(|k| self.k_const(d >> k & 1));
                        for e in self.link(w, d, one, tip, end) {
                            self.expose_k(e);
                        }
                    }
                }
            }
        }
    }
}
