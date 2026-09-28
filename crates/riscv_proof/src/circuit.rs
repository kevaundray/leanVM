//! Deterministic degree-two circuits over the binary extension field.
//! Integer words are little-endian Boolean wires, never field integers.

use alloc::{vec, vec::Vec};
use leanvm_guest::Field;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Bit(usize);

impl Bit {
    pub const fn index(self) -> usize {
        self.0
    }
}

#[derive(Clone, Debug)]
pub(crate) enum Gate {
    Input,
    Constant(bool),
    Xor(Bit, Bit),
    And(Bit, Bit),
    Pack(Vec<Bit>),
}

#[derive(Clone, Debug)]
pub struct Circuit {
    pub(crate) gates: Vec<Gate>,
    pub(crate) equalities: Vec<(Bit, Bit)>,
    inputs: usize,
}

impl Default for Circuit {
    fn default() -> Self {
        Self {
            gates: vec![Gate::Constant(false), Gate::Constant(true)],
            equalities: Vec::new(),
            inputs: 0,
        }
    }
}

impl Circuit {
    pub const ZERO: Bit = Bit(0);
    pub const ONE: Bit = Bit(1);

    fn gate(&mut self, gate: Gate) -> Bit {
        let bit = Bit(self.gates.len());
        self.gates.push(gate);
        bit
    }

    pub fn input(&mut self) -> Bit {
        self.inputs += 1;
        self.gate(Gate::Input)
    }

    pub fn input_word(&mut self, width: usize) -> Vec<Bit> {
        (0..width).map(|_| self.input()).collect()
    }

    pub fn constant(&self, value: u64, width: usize) -> Vec<Bit> {
        (0..width)
            .map(|i| {
                if i < 64 && value >> i & 1 != 0 {
                    Self::ONE
                } else {
                    Self::ZERO
                }
            })
            .collect()
    }

    pub fn xor(&mut self, a: Bit, b: Bit) -> Bit {
        if a == b {
            Self::ZERO
        } else if a == Self::ZERO {
            b
        } else if b == Self::ZERO {
            a
        } else {
            self.gate(Gate::Xor(a, b))
        }
    }

    pub fn and(&mut self, a: Bit, b: Bit) -> Bit {
        if a == Self::ZERO || b == Self::ZERO {
            Self::ZERO
        } else if a == b || b == Self::ONE {
            a
        } else if a == Self::ONE {
            b
        } else {
            self.gate(Gate::And(a, b))
        }
    }

    pub fn not(&mut self, a: Bit) -> Bit {
        self.xor(a, Self::ONE)
    }

    pub fn or(&mut self, a: Bit, b: Bit) -> Bit {
        let x = self.xor(a, b);
        let y = self.and(a, b);
        self.xor(x, y)
    }

    pub fn mux(&mut self, select: Bit, yes: Bit, no: Bit) -> Bit {
        let difference = self.xor(yes, no);
        let masked = self.and(select, difference);
        self.xor(no, masked)
    }

    pub fn select(&mut self, select: Bit, yes: &[Bit], no: &[Bit]) -> Vec<Bit> {
        assert_eq!(yes.len(), no.len());
        yes.iter().zip(no).map(|(&a, &b)| self.mux(select, a, b)).collect()
    }

    pub fn assert_equal(&mut self, a: Bit, b: Bit) {
        self.equalities.push((a, b));
    }

    pub fn assert_words_equal(&mut self, a: &[Bit], b: &[Bit]) {
        assert_eq!(a.len(), b.len());
        self.equalities.extend(a.iter().copied().zip(b.iter().copied()));
    }

    pub fn equals(&mut self, a: &[Bit], b: &[Bit]) -> Bit {
        assert_eq!(a.len(), b.len());
        let mut difference = Self::ZERO;
        for (&x, &y) in a.iter().zip(b) {
            let d = self.xor(x, y);
            difference = self.or(difference, d);
        }
        self.not(difference)
    }

    /// Width-preserving addition, with the carry beyond that width returned.
    pub fn add_carry(&mut self, a: &[Bit], b: &[Bit], mut carry: Bit) -> (Vec<Bit>, Bit) {
        assert_eq!(a.len(), b.len());
        let mut out = Vec::with_capacity(a.len());
        for (&x, &y) in a.iter().zip(b) {
            let propagate = self.xor(x, y);
            out.push(self.xor(propagate, carry));
            let generate = self.and(x, y);
            let propagated = self.and(propagate, carry);
            carry = self.xor(generate, propagated);
        }
        (out, carry)
    }

    pub fn add(&mut self, a: &[Bit], b: &[Bit]) -> Vec<Bit> {
        self.add_carry(a, b, Self::ZERO).0
    }

    pub fn subtract(&mut self, a: &[Bit], b: &[Bit]) -> (Vec<Bit>, Bit) {
        let complement: Vec<_> = b.iter().map(|&b| self.not(b)).collect();
        let (out, no_borrow) = self.add_carry(a, &complement, Self::ONE);
        (out, self.not(no_borrow))
    }

    pub fn negate(&mut self, a: &[Bit]) -> Vec<Bit> {
        self.subtract(&vec![Self::ZERO; a.len()], a).0
    }

    pub fn less_than(&mut self, a: &[Bit], b: &[Bit], signed: bool) -> Bit {
        assert!(!a.is_empty());
        let unsigned = self.subtract(a, b).1;
        if !signed {
            return unsigned;
        }
        let sign_difference = self.xor(a[a.len() - 1], b[b.len() - 1]);
        self.xor(unsigned, sign_difference)
    }

    /// Only the supplied low shift-amount bits participate (RV64: six, W: five).
    pub fn shift(&mut self, a: &[Bit], amount: &[Bit], right: bool, arithmetic: bool) -> Vec<Bit> {
        assert!(!a.is_empty());
        let mut value = a.to_vec();
        let fill = if right && arithmetic {
            a[a.len() - 1]
        } else {
            Self::ZERO
        };
        for (stage, &select) in amount.iter().enumerate() {
            let distance = 1usize << stage;
            let shifted: Vec<_> = (0..a.len())
                .map(|i| {
                    let source = if right {
                        i.checked_add(distance)
                    } else {
                        i.checked_sub(distance)
                    };
                    source.and_then(|j| value.get(j).copied()).unwrap_or(fill)
                })
                .collect();
            value = self.select(select, &shifted, &value);
        }
        value
    }

    pub fn extend(&self, value: &[Bit], width: usize, signed: bool) -> Vec<Bit> {
        assert!(!value.is_empty() && value.len() <= width);
        let mut out = value.to_vec();
        out.resize(width, if signed { value[value.len() - 1] } else { Self::ZERO });
        out
    }

    /// Exact double-width two's-complement product, including mixed signs.
    pub fn multiply(&mut self, a: &[Bit], b: &[Bit], signed_a: bool, signed_b: bool) -> Vec<Bit> {
        assert_eq!(a.len(), b.len());
        let width = a.len();
        let mut product = vec![Self::ZERO; width * 2];
        for (j, &multiplier) in b.iter().enumerate() {
            let partial: Vec<_> = a.iter().map(|&bit| self.and(bit, multiplier)).collect();
            let mut row = vec![Self::ZERO; width * 2];
            row[j..j + width].copy_from_slice(&partial);
            product = self.add(&product, &row);
        }
        // (a - sign(a)*2^w)(b - sign(b)*2^w), modulo 2^(2w).
        if signed_a {
            let correction: Vec<_> = b.iter().map(|&bit| self.and(bit, a[width - 1])).collect();
            let upper = self.subtract(&product[width..], &correction).0;
            product[width..].copy_from_slice(&upper);
        }
        if signed_b {
            let correction: Vec<_> = a.iter().map(|&bit| self.and(bit, b[width - 1])).collect();
            let upper = self.subtract(&product[width..], &correction).0;
            product[width..].copy_from_slice(&upper);
        }
        product
    }

    /// Restoring division. Zero divisor yields all-one quotient and unchanged
    /// dividend remainder. Signed MIN/-1 yields MIN and zero without a special
    /// unconstrained witness; these are exactly the RISC-V architectural cases.
    pub fn divide(&mut self, a: &[Bit], b: &[Bit], signed: bool) -> (Vec<Bit>, Vec<Bit>) {
        assert!(!a.is_empty() && a.len() == b.len());
        let width = a.len();
        let (dividend, divisor) = if signed {
            let negative_a = self.negate(a);
            let negative_b = self.negate(b);
            (
                self.select(a[width - 1], &negative_a, a),
                self.select(b[width - 1], &negative_b, b),
            )
        } else {
            (a.to_vec(), b.to_vec())
        };
        let wide_divisor = self.extend(&divisor, width + 1, false);
        let mut remainder = vec![Self::ZERO; width + 1];
        let mut quotient = vec![Self::ZERO; width];
        for i in (0..width).rev() {
            remainder.rotate_right(1);
            remainder[0] = dividend[i];
            let (difference, borrow) = self.subtract(&remainder, &wide_divisor);
            quotient[i] = self.not(borrow);
            remainder = self.select(quotient[i], &difference, &remainder);
        }
        remainder.truncate(width);
        if signed {
            let sign = self.xor(a[width - 1], b[width - 1]);
            let negative_q = self.negate(&quotient);
            quotient = self.select(sign, &negative_q, &quotient);
            let negative_r = self.negate(&remainder);
            remainder = self.select(a[width - 1], &negative_r, &remainder);
            let zero = vec![Self::ZERO; width];
            let divisor_zero = self.equals(b, &zero);
            quotient = self.select(divisor_zero, &vec![Self::ONE; width], &quotient);
        }
        (quotient, remainder)
    }

    /// Pack at most 64 bits into one base-field column for a bus coordinate.
    pub fn pack(&mut self, bits: &[Bit]) -> usize {
        assert!(bits.len() <= 64);
        self.gate(Gate::Pack(bits.to_vec())).0
    }

    pub fn columns(&self) -> usize {
        self.gates.len()
    }
    pub fn constraints(&self) -> usize {
        self.gates.len() + self.equalities.len()
    }
    pub fn inputs(&self) -> usize {
        self.inputs
    }

    /// Deterministic witness generation. This is not a verification procedure.
    pub fn witness(&self, inputs: &[bool]) -> Option<Vec<u64>> {
        if inputs.len() != self.inputs {
            return None;
        }
        let mut input = inputs.iter();
        let mut values = Vec::with_capacity(self.gates.len());
        for gate in &self.gates {
            let value = match gate {
                Gate::Input => u64::from(*input.next()?),
                Gate::Constant(value) => u64::from(*value),
                Gate::Xor(a, b) => values[a.0] ^ values[b.0],
                Gate::And(a, b) => values[a.0] & values[b.0],
                Gate::Pack(bits) => bits.iter().enumerate().fold(0, |word, (i, b)| word | values[b.0] << i),
            };
            values.push(value);
        }
        Some(values)
    }

    /// Evaluate one fixed identity at an arbitrary extension-field point.
    /// `quadratic_only` selects the homogeneous degree-two component used by
    /// the existing batched constraint sumcheck.
    pub fn constraint(&self, index: usize, row: &[Field], quadratic_only: bool) -> Field {
        assert_eq!(row.len(), self.columns());
        if index >= self.gates.len() {
            let (a, b) = self.equalities[index - self.gates.len()];
            return if quadratic_only {
                Field::ZERO
            } else {
                row[a.0] + row[b.0]
            };
        }
        let output = if quadratic_only { Field::ZERO } else { row[index] };
        match &self.gates[index] {
            Gate::Input => output + row[index] * row[index],
            Gate::Constant(value) => {
                if quadratic_only {
                    Field::ZERO
                } else {
                    output + Field::new(u64::from(*value), 0, 0)
                }
            }
            Gate::Xor(a, b) => {
                if quadratic_only {
                    Field::ZERO
                } else {
                    output + row[a.0] + row[b.0]
                }
            }
            Gate::And(a, b) => output + row[a.0] * row[b.0],
            Gate::Pack(bits) => {
                if quadratic_only {
                    Field::ZERO
                } else {
                    bits.iter()
                        .enumerate()
                        .fold(output, |sum, (i, b)| sum + row[b.0] * Field::new(1u64 << i, 0, 0))
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn homogeneous_quadratic_part_matches_field_scaling() {
        let mut c = Circuit::default();
        let a = c.input_word(3);
        let b = c.input_word(3);
        let sum = c.add(&a, &b);
        let selected = c.select(a[0], &sum, &b);
        c.pack(&selected);
        c.assert_equal(a[1], b[2]);
        let row: Vec<_> = (0..c.columns()).map(|i| Field::new(i as u64 + 17, 3, 9)).collect();
        let zero = vec![Field::ZERO; row.len()];
        let scale = Field::new(37, 81, 6);
        let scaled: Vec<_> = row.iter().map(|&x| x * scale).collect();
        for i in 0..c.constraints() {
            let constant = c.constraint(i, &zero, false);
            let quadratic = c.constraint(i, &row, true);
            let linear = c.constraint(i, &row, false) + constant + quadratic;
            assert_eq!(
                c.constraint(i, &scaled, false),
                constant + scale * linear + scale.square() * quadratic
            );
        }
    }

    #[test]
    fn non_boolean_input_and_unbound_pack_are_rejected() {
        let mut c = Circuit::default();
        let bits = c.input_word(8);
        let packed = c.pack(&bits);
        let values = c
            .witness(&[true, false, true, false, true, false, true, false])
            .unwrap();
        let mut row: Vec<_> = values.into_iter().map(|x| Field::new(x, 0, 0)).collect();
        assert!((0..c.constraints()).all(|i| c.constraint(i, &row, false).is_zero()));
        row[packed] += Field::ONE;
        assert!(!c.constraint(packed, &row, false).is_zero());
        row[bits[0].index()] = Field::new(2, 0, 0);
        assert!(!c.constraint(bits[0].index(), &row, false).is_zero());
    }
}
