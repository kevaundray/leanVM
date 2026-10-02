//! The ALU's four classes: sums and comparisons, bitwise logic, branches, and jumps.
//!
//! Each is a table of its own, so that a row pays only for the circuit its instruction needs.

use super::{InstructionClass, sext32};
use crate::rv::entry::Class;

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

    fn output_words(&out: &u64) -> Vec<u64> {
        vec![out]
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

    fn output_words(&out: &u64) -> Vec<u64> {
        vec![out]
    }
}

/// One conditional branch: whether `v1` and `v2` meet its condition.
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

    /// The flag word of a branch with function `funct3`.
    ///
    /// Returns `None` for functions 2 and 3, which are reserved.
    pub const fn flags_of(funct3: u32) -> Option<u64> {
        match funct3 {
            0 => Some(Self::EQ),
            1 => Some(Self::NE),
            4 => Some(Self::LT),
            5 => Some(Self::GE),
            6 => Some(Self::LTU),
            7 => Some(Self::GEU),
            _ => None,
        }
    }
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
        vec![self.v1, self.v2, self.flags]
    }

    fn output_words(&taken: &bool) -> Vec<u64> {
        vec![taken as u64]
    }
}

/// One jump: `JAL` and the exit to a fixed target, `JALR` to `v1 + imm` with bit 0 cleared.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Jump {
    /// Direct or not: one of its legal words.
    pub flags: u64,
    /// The first register's value.
    pub v1: u64,
    /// The immediate.
    pub imm: u64,
}

impl Jump {
    /// Jump to the entry's fixed target, not to the computed one.
    pub const DIRECT: u64 = 1 << 0;
}

impl InstructionClass for Jump {
    const CLASS: Class = Class::Jump;

    /// `JALR`, then `JAL` and the exit.
    const LEGAL: &'static [u64] = &[0, Self::DIRECT];

    /// The computed target, and whether the fixed one is taken.
    type Output = (u64, bool);

    fn eval(&self) -> (u64, bool) {
        (self.v1.wrapping_add(self.imm) & !1, self.flags & Self::DIRECT != 0)
    }

    fn input_words(&self) -> Vec<u64> {
        vec![self.v1, self.imm, self.flags]
    }

    fn output_words(&(out, taken): &(u64, bool)) -> Vec<u64> {
        vec![out, taken as u64]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::semantics::tests::edge_word;
    use proptest::prelude::*;
    use proptest::sample::select;
    use proptest::strategy::BoxedStrategy;

    /// An operand pair as the decoder makes them: one of `v2` and `imm` is zero, and now and
    /// then the second operand equals `v1`, which random words never do.
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
            (select(Self::LEGAL), operands())
                .prop_map(|(flags, (v1, v2, imm))| Self {
                    flags,
                    v1,
                    v2: v2 ^ imm,
                })
                .boxed()
        }
    }

    impl Arbitrary for Jump {
        type Parameters = ();
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with((): ()) -> Self::Strategy {
            (select(Self::LEGAL), edge_word(), edge_word())
                .prop_map(|(flags, v1, imm)| Self { flags, v1, imm })
                .boxed()
        }
    }
}
