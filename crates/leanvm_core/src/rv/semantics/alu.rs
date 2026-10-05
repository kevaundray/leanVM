//! The ALU's four classes: sums and comparisons, bitwise logic, branches, and jumps.
//!
//! Each is a table of its own, so that a row pays only for the circuit its instruction needs.

use super::{InstructionClass, sext32};
use crate::rv::circuits::{ClassCircuit, Word, WordGadgets};
use crate::rv::entry::Class;
use flock::circuit::{Builder, Circuit};

/// One adder instance: add, subtract, and the two comparisons.
///
/// The second operand `b` is `v2 ^ imm`.
///
/// One of the two is always zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Add {
    /// What the adder computes: one of its legal words.
    pub flags: u64,
    /// The first register's value.
    pub v1: u64,
    /// The second register's value.
    pub v2: u64,
    /// The immediate.
    pub imm: u64,
}

impl Add {
    /// Compute `v1 - b` instead of `v1 + b`.
    ///
    /// The comparisons need the difference.
    pub const SUB: u64 = 1 << 0;
    /// Sign-extend the low 32 bits of the sum.
    pub const WORD: u64 = 1 << 1;
    /// Output `v1 < b`, signed.
    pub const SEL_LT: u64 = 1 << 2;
    /// Output `v1 < b`, unsigned.
    pub const SEL_LTU: u64 = 1 << 3;
}

impl InstructionClass for Add {
    const CLASS: Class = Class::Add;

    /// A comparison subtracts, and has no word form.
    const LEGAL: &'static [u64] = &[
        0,
        Self::SUB,
        Self::WORD,
        Self::SUB | Self::WORD,
        Self::SUB | Self::SEL_LT,
        Self::SUB | Self::SEL_LTU,
    ];

    /// The sum, or the comparison's bit.
    type Output = u64;

    fn eval(&self) -> u64 {
        let on = |flag: u64| self.flags & flag != 0;
        let (v1, b) = (self.v1, self.v2 ^ self.imm);
        if on(Self::SEL_LT) {
            ((v1 as i64) < (b as i64)) as u64
        } else if on(Self::SEL_LTU) {
            (v1 < b) as u64
        } else {
            let sum = if on(Self::SUB) {
                v1.wrapping_sub(b)
            } else {
                v1.wrapping_add(b)
            };
            if on(Self::WORD) { sext32(sum) } else { sum }
        }
    }

    fn input_words(&self) -> Vec<u64> {
        vec![self.v1, self.v2, self.imm, self.flags]
    }

    fn output_words(&self, &out: &u64) -> Vec<u64> {
        vec![out]
    }
}

impl ClassCircuit for Add {
    /// The adder: `(v1, v2, imm, flags) -> out`.
    ///
    /// - The second operand is `b = v2 ^ imm`.
    /// - One adder gives `v1 + b`, or `v1 - b` for the comparisons.
    /// - The output is that sum, unless a comparison replaces it by its bit.
    fn circuit() -> Circuit {
        let mut c = Builder::new(&[64, 64, 64, 4], &[64]);
        let (v1, v2, imm, f) = (c.input(0), c.input(1), c.input(2), c.input(3));
        let flag = |bit: u64| f[bit.trailing_zeros() as usize];
        let b = c.xor_word(&v2, &imm);

        // The difference is v1 + !b + 1.
        //
        // It borrows exactly when that sum does not carry out.
        let sub = flag(Self::SUB);
        let b_or_not: Word = b.iter().map(|&bit| c.xor(bit, sub)).collect();
        let (sum, carry_out) = c.add_with_carry(&v1, &b_or_not, sub);

        // The comparisons, from the borrow and the signs.
        //
        //     ltu = borrow
        //     lt  = borrow ^ sign(v1) ^ sign(b)
        let ltu = c.not(carry_out);
        let signs = c.xor(v1[63], b[63]);
        let lt = c.xor(ltu, signs);

        // The sum unless a comparison is selected, whose single bit is the output's bit 0.
        let sum = c.sext32_if(flag(Self::WORD), &sum);
        let compares = c.xor(flag(Self::SEL_LT), flag(Self::SEL_LTU));
        let keeps = c.not(compares);
        let mut out = c.and_word(keeps, &sum);
        let lt_term = c.and(flag(Self::SEL_LT), lt);
        let ltu_term = c.and(flag(Self::SEL_LTU), ltu);
        let compared = c.xor(lt_term, ltu_term);
        out[0] = c.xor(out[0], compared);

        c.output_word(0, &out);
        c.finish()
    }
}

/// One instance of the bitwise logic: AND, OR or XOR of `v1` and `b = v2 ^ imm`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Logic {
    /// The operation: one of its legal words.
    pub flags: u64,
    /// The first register's value.
    pub v1: u64,
    /// The second register's value.
    pub v2: u64,
    /// The immediate.
    pub imm: u64,
}

impl Logic {
    /// Output `v1 & b`.
    pub const AND: u64 = 1 << 0;
    /// Output `v1 | b`.
    pub const OR: u64 = 1 << 1;
    /// Output `v1 ^ b`.
    pub const XOR: u64 = 1 << 2;
}

impl InstructionClass for Logic {
    const CLASS: Class = Class::Logic;

    /// Exactly one operation.
    const LEGAL: &'static [u64] = &[Self::AND, Self::OR, Self::XOR];

    /// The result.
    type Output = u64;

    fn eval(&self) -> u64 {
        let (v1, b) = (self.v1, self.v2 ^ self.imm);
        match self.flags {
            Self::AND => v1 & b,
            Self::OR => v1 | b,
            _ => v1 ^ b,
        }
    }

    fn input_words(&self) -> Vec<u64> {
        vec![self.v1, self.v2, self.imm, self.flags]
    }

    fn output_words(&self, &out: &u64) -> Vec<u64> {
        vec![out]
    }
}

impl ClassCircuit for Logic {
    /// The bitwise logic: `(v1, v2, imm, flags) -> out`, two products per bit.
    ///
    /// With `b = v2 ^ imm` and the selectors `or` and `xor`, bit by bit:
    ///
    /// ```text
    ///     p   = (v1 ^ or) * (b ^ or)          v1 & b, or !(v1 | b) when or
    ///     out = p ^ or ^ xor * (p ^ v1 ^ b)
    /// ```
    fn circuit() -> Circuit {
        let mut c = Builder::new(&[64, 64, 64, 3], &[64]);
        let (v1, v2, imm, f) = (c.input(0), c.input(1), c.input(2), c.input(3));
        let flag = |bit: u64| f[bit.trailing_zeros() as usize];
        let (or, xor) = (flag(Self::OR), flag(Self::XOR));
        let b = c.xor_word(&v2, &imm);
        for i in 0..64 {
            let (x, y) = (c.xor(v1[i], or), c.xor(b[i], or));
            let p = c.and(x, y);
            let diff = c.xor(v1[i], b[i]);
            let flip = c.xor(p, diff);
            let xor_term = c.and(xor, flip);
            let kept = c.xor(p, or);
            let bit = c.xor(kept, xor_term);
            c.output(0, i, bit);
        }
        c.finish()
    }
}

/// One conditional branch: whether `v1` and `v2` meet its condition, and the offset that moves the successor.
///
/// A branch writes no register and has no immediate: its target is the entry's.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Branch {
    /// The condition: one of its legal words.
    pub flags: u64,
    /// The first register's value.
    pub v1: u64,
    /// The second register's value.
    pub v2: u64,
    /// The jump's offset: the fixed target XOR `pc + 4`.
    ///
    /// The decision does not read it; the circuit gates it by the decision.
    pub dt: u64,
}

impl Branch {
    /// Branch when `v1 == v2`.
    pub const EQ: u64 = 1 << 0;
    /// Branch when `v1 != v2`.
    pub const NE: u64 = 1 << 1;
    /// Branch when `v1 < v2`, signed.
    pub const LT: u64 = 1 << 2;
    /// Branch when `v1 >= v2`, signed.
    pub const GE: u64 = 1 << 3;
    /// Branch when `v1 < v2`, unsigned.
    pub const LTU: u64 = 1 << 4;
    /// Branch when `v1 >= v2`, unsigned.
    pub const GEU: u64 = 1 << 5;
}

impl InstructionClass for Branch {
    const CLASS: Class = Class::Branch;

    /// Exactly one condition.
    const LEGAL: &'static [u64] = &[Self::EQ, Self::NE, Self::LT, Self::GE, Self::LTU, Self::GEU];

    /// Whether the branch is taken.
    type Output = bool;

    fn eval(&self) -> bool {
        let (v1, v2) = (self.v1, self.v2);
        let (lt, ltu) = ((v1 as i64) < (v2 as i64), v1 < v2);
        match self.flags {
            Self::EQ => v1 == v2,
            Self::NE => v1 != v2,
            Self::LT => lt,
            Self::GE => !lt,
            Self::LTU => ltu,
            _ => !ltu,
        }
    }

    fn input_words(&self) -> Vec<u64> {
        vec![self.v1, self.v2, self.flags, self.dt]
    }

    /// The offset the successor adds to `pc + 4`: the entry's when the branch is taken, zero otherwise.
    fn output_words(&self, &taken: &bool) -> Vec<u64> {
        vec![if taken { self.dt } else { 0 }]
    }
}

impl ClassCircuit for Branch {
    /// The branch: `(v1, v2, flags, dt) -> jump`.
    ///
    /// - The difference `v1 + !v2 + 1` borrows exactly when it does not carry out, and only its carries are used.
    /// - The branch is taken when the one condition set holds.
    /// - `jump` is `dt` gated by that decision, so the successor `pc + 4 + jump` is linear in the row's columns.
    fn circuit() -> Circuit {
        let mut c = Builder::new(&[64, 64, 6, 64], &[64]);
        let (v1, v2, f, dt) = (c.input(0), c.input(1), c.input(2), c.input(3));
        let flag = |bit: u64| f[bit.trailing_zeros() as usize];
        let one = c.one();

        // The comparisons, from the borrow and the signs.
        //
        //     ltu = borrow
        //     lt  = borrow ^ sign(v1) ^ sign(v2)
        //     eq  = no bit of v1 ^ v2 set
        let not_v2: Word = v2.iter().map(|&bit| c.not(bit)).collect();
        let (_, carry_out) = c.add_with_carry(&v1, &not_v2, one);
        let ltu = c.not(carry_out);
        let signs = c.xor(v1[63], v2[63]);
        let lt = c.xor(ltu, signs);
        let diff = c.xor_word(&v1, &v2);
        let ne = c.any(&diff);
        let eq = c.not(ne);

        // The decision: the one condition set.
        let (ge, geu) = (c.not(lt), c.not(ltu));
        let taken = [
            (Self::EQ, eq),
            (Self::NE, ne),
            (Self::LT, lt),
            (Self::GE, ge),
            (Self::LTU, ltu),
            (Self::GEU, geu),
        ]
        .into_iter()
        .fold(None, |acc, (when, holds)| {
            let term = c.and(flag(when), holds);
            c.xor(acc, term)
        });

        // Each bit of the jump is a product written at its output position, so it costs no copy.
        for (i, &bit) in dt.iter().enumerate() {
            c.and_output(0, i, taken, bit);
        }
        c.finish()
    }
}

/// One jump: `JAL` and the exit to the entry's fixed target, `JALR` to `v1 + imm` with bit 0 cleared.
///
/// Every jump is taken, and links `pc + 4`, which its table writes to `rd` itself.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Jump {
    /// Direct or indirect: one of its legal words.
    pub flags: u64,
    /// The first register's value.
    pub v1: u64,
    /// The immediate.
    pub imm: u64,
    /// The jump's offset: the fixed target XOR `pc + 4`, zero for an indirect jump.
    pub dt: u64,
    /// The fall-through address `pc + 4`, what an indirect target is taken against.
    pub pc4: u64,
}

impl Jump {
    /// Jump to `v1 + imm` with bit 0 cleared, as `JALR` does, rather than to the entry's fixed target.
    pub const INDIRECT: u64 = 1 << 0;
}

impl InstructionClass for Jump {
    const CLASS: Class = Class::Jump;

    /// `JAL` and the exit, then `JALR`.
    const LEGAL: &'static [u64] = &[0, Self::INDIRECT];

    /// What the successor adds to `pc + 4`.
    ///
    /// - A fixed jump adds its offset, the target XOR `pc + 4`.
    /// - An indirect jump has offset zero and adds the sum XOR `pc + 4`, bit 0 left out.
    /// - Its successor is then the sum with bit 0 cleared, since `pc + 4` is even.
    type Output = u64;

    fn eval(&self) -> u64 {
        if self.flags & Self::INDIRECT == 0 {
            self.dt
        } else {
            self.dt ^ ((self.v1.wrapping_add(self.imm) ^ self.pc4) & !1)
        }
    }

    fn input_words(&self) -> Vec<u64> {
        vec![self.v1, self.imm, self.flags, self.dt, self.pc4]
    }

    fn output_words(&self, &jump: &u64) -> Vec<u64> {
        vec![jump]
    }
}

impl ClassCircuit for Jump {
    /// The jump: `(v1, imm, flags, dt, pc4) -> jump`.
    ///
    /// - The computed target is `v1 + imm`; its bit 0 is never made, the target clearing it.
    /// - `jump` is `dt`, plus the target XOR `pc + 4` for an indirect jump, bit 0 kept, so the successor
    ///   `pc + 4 + jump` is linear in the row's columns.
    fn circuit() -> Circuit {
        let mut c = Builder::new(&[64, 64, 1, 64, 64], &[64]);
        let (v1, imm, f, dt, pc4) = (c.input(0), c.input(1), c.input(2), c.input(3), c.input(4));
        let indirect = f[Self::INDIRECT.trailing_zeros() as usize];
        let target = c.add_wrapping(&v1, &imm);

        //     jump = dt ^ indirect * (target ^ pc4), bit 0 kept
        c.output(0, 0, dt[0]);
        for i in 1..64 {
            let d = c.xor(target[i], pc4[i]);
            let moved = c.and(indirect, d);
            let bit = c.xor(dt[i], moved);
            c.output(0, i, bit);
        }
        c.finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::semantics::tests::{circuit_matches_reference, edge_word};
    use fiat_shamir::transcript::{ProverState, VerifierState};
    use proptest::prelude::*;
    use proptest::sample::select;
    use proptest::strategy::BoxedStrategy;
    use std::sync::LazyLock;

    /// An operand pair as the decoder makes them: one of `v2` and `imm` is zero, and now and then the second operand
    /// equals `v1`, which random words never do.
    fn operands() -> impl Strategy<Value = (u64, u64, u64)> {
        (edge_word(), edge_word(), any::<bool>(), any::<bool>()).prop_map(|(v1, v2, equal, immediate)| {
            let v2 = if equal { v1 } else { v2 };
            let (v2, imm) = if immediate { (0, v2) } else { (v2, 0) };
            (v1, v2, imm)
        })
    }

    impl Arbitrary for Add {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with((): ()) -> Self::Strategy {
            (select(Self::LEGAL), operands())
                .prop_map(|(flags, (v1, v2, imm))| Self { flags, v1, v2, imm })
                .boxed()
        }
    }

    impl Arbitrary for Logic {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with((): ()) -> Self::Strategy {
            (select(Self::LEGAL), operands())
                .prop_map(|(flags, (v1, v2, imm))| Self { flags, v1, v2, imm })
                .boxed()
        }
    }

    impl Arbitrary for Branch {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with((): ()) -> Self::Strategy {
            (select(Self::LEGAL), operands(), any::<u64>())
                .prop_map(|(flags, (v1, v2, imm), dt)| Self {
                    flags,
                    v1,
                    v2: v2 ^ imm,
                    dt,
                })
                .boxed()
        }
    }

    impl Arbitrary for Jump {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with((): ()) -> Self::Strategy {
            (
                select(Self::LEGAL),
                edge_word(),
                edge_word(),
                any::<u64>(),
                any::<u64>(),
            )
                .prop_map(|(flags, v1, imm, dt, pc4)| Self {
                    flags,
                    v1,
                    imm,
                    dt,
                    pc4,
                })
                .boxed()
        }
    }

    static BRANCH: LazyLock<Circuit> = LazyLock::new(Branch::circuit);

    #[test]
    fn every_alu_class_circuit_matches_its_reference() {
        // Legal flags and edge-biased operands pin each gate list to its reference function.
        circuit_matches_reference::<Add>(4096);
        circuit_matches_reference::<Logic>(4096);
        circuit_matches_reference::<Branch>(4096);
        circuit_matches_reference::<Jump>(4096);
    }

    #[test]
    fn an_indirect_jump_lands_on_its_target_with_bit_0_cleared() {
        // Invariant: `pc + 4 + jump` is `JALR`'s target, and a fixed jump's offset is the entry's.
        let (v1, imm, pc4) = (0x1000_0001, 6, 0x2000_0004);
        let indirect = Jump {
            flags: Jump::INDIRECT,
            v1,
            imm,
            dt: 0,
            pc4,
        };
        assert_eq!(pc4 ^ indirect.eval(), 0x1000_0006);
        let direct = Jump {
            flags: 0,
            dt: 0x44,
            ..indirect
        };
        assert_eq!(direct.eval(), 0x44);
    }

    #[test]
    fn flock_proves_honest_branch_instances_and_refuses_a_flipped_bit() {
        // Fixture: 16 instances cycling through the legal words.
        const LABEL: &[u8] = b"rv-branch-reduction-test";
        let block = BRANCH.block();
        let n_log = 4;
        let rows: Vec<[u64; 4]> = (0..1u64 << n_log)
            .map(|i| {
                [
                    i.wrapping_mul(0x9e37_79b9_7f4a_7c15),
                    !i,
                    Branch::LEGAL[i as usize % Branch::LEGAL.len()],
                    i << 3,
                ]
            })
            .collect();

        // Prove the batch, optionally flipping one witness bit first, and verify.
        let accepts = |tamper: Option<usize>| {
            let (mut z, a, b, mut z_lincheck) = BRANCH.generate_witness(&rows, n_log);
            if let Some(bit) = tamper {
                z[bit / 64] ^= 1 << (bit % 64);
                z_lincheck[bit] ^= 1;
            }
            let mut ps = ProverState::from_label(LABEL);
            let instance = flock::reduction::Instance {
                block,
                n_blocks_log: n_log,
                z: &z,
                a: &a,
                b: &b,
                z_lincheck: &z_lincheck,
            };
            let claims = flock::reduction::prove(&[instance], &mut ps);
            let proof = ps.into_proof();
            let mut vs = VerifierState::from_label(LABEL, &proof);
            flock::reduction::verify(&[(block, n_log)], &mut vs).is_ok_and(|r| r[0].claim == claims[0])
                && vs.finish().is_ok()
        };
        assert!(accepts(None));

        // Mutation: a bit of the jump, a spare bit of the flags' word, the last product.
        for bit in [64 * BRANCH.n_input_words() + 3, 64 * 2 + 7, BRANCH.useful_bits() - 1] {
            assert!(!accepts(Some(bit)), "flipping bit {bit} must reject");
        }
    }
}
