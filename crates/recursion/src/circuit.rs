//! Trusted field-native circuit definitions and host witness generation.

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};

use leanvm_guest::Field;

use crate::Error;

/// An immutable value belonging to exactly one builder.
///
/// The owner is a construction-time guard, never circuit metadata. Tables must
/// identify wires exclusively by their dense [`Wire::index`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Wire {
    index: u32,
    owner: u64,
}

impl Wire {
    pub fn index(self) -> usize {
        self.index as usize
    }
}

#[derive(Clone, Debug)]
pub(crate) enum Operation {
    Input { output: Wire, index: usize, public: bool },
    Constant { output: Wire, value: Field },
    Add { output: Wire, lhs: Wire, rhs: Wire },
    Mul { output: Wire, lhs: Wire, rhs: Wire },
    Inverse { output: Wire, input: Wire },
    Limb { output: Wire, input: Wire, limb: u8 },
    Compose { output: Wire, limbs: [Wire; 3] },
    HintBit { output: Wire, input: Wire, bit: u8 },
    AssertEqual { lhs: Wire, rhs: Wire },
    AssertBool { input: Wire },
    Blake2s { output: [Wire; 4], input: Box<[Wire; 14]> },
}

#[derive(Default)]
struct State {
    operations: Vec<Operation>,
    // Only static constants are tracked here, never witness values.
    known: Vec<Option<Field>>,
    constants: HashMap<Field, Wire>,
    public_inputs: usize,
    private_inputs: usize,
}

impl State {
    fn allocate(&mut self, owner: u64, known: Option<Field>) -> Wire {
        let index = u32::try_from(self.known.len()).expect("circuit wire capacity exceeded");
        let wire = Wire { index, owner };
        self.known.push(known);
        wire
    }

    fn emit(&mut self, owner: u64, operation: impl FnOnce(Wire) -> Operation) -> Wire {
        let output = self.allocate(owner, None);
        self.operations.push(operation(output));
        output
    }

    fn constant(&mut self, owner: u64, value: Field) -> Wire {
        if let Some(&wire) = self.constants.get(&value) {
            return wire;
        }
        let output = self.allocate(owner, Some(value));
        self.operations.push(Operation::Constant { output, value });
        self.constants.insert(value, output);
        output
    }

    fn known(&self, owner: u64, wire: Wire) -> Option<Field> {
        assert_eq!(wire.owner, owner, "wire belongs to another builder");
        *self.known.get(wire.index()).expect("wire has not been allocated")
    }
}

/// Constructs a circuit using static definitions only.
///
/// Invalid wires or limb indexes are programming errors and panic. Inputs and
/// assertions remain in the circuit even when arithmetic around them folds.
/// Interior mutability allows nested expressions without mutable-borrow clashes.
pub struct Builder {
    owner: u64,
    state: RefCell<State>,
}

impl Default for Builder {
    fn default() -> Self {
        Self::new()
    }
}

impl Builder {
    pub fn new() -> Self {
        static NEXT_OWNER: AtomicU64 = AtomicU64::new(0);
        let owner = NEXT_OWNER
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |owner| owner.checked_add(1))
            .expect("circuit builder owner capacity exceeded");
        Self {
            owner,
            state: RefCell::new(State::default()),
        }
    }

    pub fn input(&self, public: bool) -> Wire {
        let mut state = self.state.borrow_mut();
        let index = if public {
            let index = state.public_inputs;
            state.public_inputs += 1;
            index
        } else {
            let index = state.private_inputs;
            state.private_inputs += 1;
            index
        };
        state.emit(self.owner, |output| Operation::Input { output, index, public })
    }

    pub fn constant(&self, value: Field) -> Wire {
        self.state.borrow_mut().constant(self.owner, value)
    }

    pub fn add(&self, lhs: Wire, rhs: Wire) -> Wire {
        let mut state = self.state.borrow_mut();
        let left = state.known(self.owner, lhs);
        let right = state.known(self.owner, rhs);
        if let (Some(left), Some(right)) = (left, right) {
            return state.constant(self.owner, left + right);
        }
        if lhs == rhs {
            return state.constant(self.owner, Field::ZERO);
        }
        if left == Some(Field::ZERO) {
            return rhs;
        }
        if right == Some(Field::ZERO) {
            return lhs;
        }
        state.emit(self.owner, |output| Operation::Add { output, lhs, rhs })
    }

    pub fn mul(&self, lhs: Wire, rhs: Wire) -> Wire {
        let mut state = self.state.borrow_mut();
        let left = state.known(self.owner, lhs);
        let right = state.known(self.owner, rhs);
        if let (Some(left), Some(right)) = (left, right) {
            return state.constant(self.owner, left * right);
        }
        if left == Some(Field::ZERO) || right == Some(Field::ZERO) {
            return state.constant(self.owner, Field::ZERO);
        }
        if left == Some(Field::ONE) {
            return rhs;
        }
        if right == Some(Field::ONE) {
            return lhs;
        }
        state.emit(self.owner, |output| Operation::Mul { output, lhs, rhs })
    }

    pub fn inverse(&self, input: Wire) -> Wire {
        let mut state = self.state.borrow_mut();
        if let Some(inverse) = state.known(self.owner, input).and_then(Field::inverse) {
            return state.constant(self.owner, inverse);
        }
        // Inverse(0) must remain an unsatisfiable constraint, not disappear.
        state.emit(self.owner, |output| Operation::Inverse { output, input })
    }

    pub fn limb(&self, input: Wire, limb: u8) -> Wire {
        assert!(limb < 3, "field limb index must be below three");
        let mut state = self.state.borrow_mut();
        if let Some(value) = state.known(self.owner, input) {
            return state.constant(self.owner, Field::from(value.0[limb as usize]));
        }
        state.emit(self.owner, |output| Operation::Limb { output, input, limb })
    }

    pub fn compose(&self, limbs: [Wire; 3]) -> Wire {
        let mut state = self.state.borrow_mut();
        let known = limbs.map(|wire| state.known(self.owner, wire));
        if let [Some(a), Some(b), Some(c)] = known
            && [a, b, c].iter().all(|value| value.0[1] == 0 && value.0[2] == 0)
        {
            return state.constant(self.owner, Field([a.0[0], b.0[0], c.0[0]]));
        }
        // Nonbase constants still require the rejecting Compose constraint.
        state.emit(self.owner, |output| Operation::Compose { output, limbs })
    }

    pub fn assert_equal(&self, lhs: Wire, rhs: Wire) {
        let mut state = self.state.borrow_mut();
        state.known(self.owner, lhs);
        state.known(self.owner, rhs);
        state.operations.push(Operation::AssertEqual { lhs, rhs });
    }

    pub fn assert_bool(&self, input: Wire) {
        let mut state = self.state.borrow_mut();
        state.known(self.owner, input);
        state.operations.push(Operation::AssertBool { input });
    }

    /// Decomposes low tower-basis bits and constrains every higher bit to zero.
    pub fn bits(&self, input: Wire, width: usize) -> Vec<Wire> {
        assert!(width <= 192, "bit width must fit the field");
        let bits = {
            let mut state = self.state.borrow_mut();
            let known = state.known(self.owner, input);
            (0..width)
                .map(|bit| {
                    if let Some(value) = known {
                        state.constant(self.owner, Field::from((value.0[bit / 64] >> (bit % 64)) & 1))
                    } else {
                        state.emit(self.owner, |output| Operation::HintBit {
                            output,
                            input,
                            bit: bit as u8,
                        })
                    }
                })
                .collect::<Vec<_>>()
        };
        let mut reconstructed = self.constant(Field::ZERO);
        for (bit, &wire) in bits.iter().enumerate() {
            self.assert_bool(wire);
            let mut coefficient = [0; 3];
            coefficient[bit / 64] = 1u64 << (bit % 64);
            reconstructed = self.add(reconstructed, self.mul(wire, self.constant(Field(coefficient))));
        }
        self.assert_equal(reconstructed, input);
        bits
    }

    /// Compresses message words `0..8`, chaining words `8..12`, counter `12`, and flags `13`.
    /// Words pack two little-endian u32 lanes; flags packs f0 below f1.
    pub fn blake2s(&self, input: [Wire; 14]) -> [Wire; 4] {
        let mut state = self.state.borrow_mut();
        for wire in input {
            state.known(self.owner, wire);
        }
        let output = std::array::from_fn(|_| state.allocate(self.owner, None));
        state.operations.push(Operation::Blake2s {
            output,
            input: Box::new(input),
        });
        output
    }

    pub fn finish(self) -> Circuit {
        let state = self.state.into_inner();
        Circuit {
            operations: state.operations,
            wire_count: state.known.len(),
            public_inputs: state.public_inputs,
            private_inputs: state.private_inputs,
        }
    }
}

/// An immutable trusted circuit. There is intentionally no deserialization or
/// constructor accepting arbitrary operations.
#[derive(Clone, Debug)]
pub struct Circuit {
    operations: Vec<Operation>,
    wire_count: usize,
    public_inputs: usize,
    private_inputs: usize,
}

impl Circuit {
    pub(crate) fn operations(&self) -> &[Operation] {
        &self.operations
    }

    pub(crate) fn wire_count(&self) -> usize {
        self.wire_count
    }

    pub(crate) fn public_inputs(&self) -> usize {
        self.public_inputs
    }

    pub(crate) fn private_inputs(&self) -> usize {
        self.private_inputs
    }

    /// Generates an honest witness in dense wire order. This is not a verifier:
    /// native proof constraints must enforce every predicate checked here.
    pub fn evaluate(&self, public: &[Field], private: &[Field]) -> Result<Vec<Field>, Error> {
        if public.len() != self.public_inputs || private.len() != self.private_inputs {
            return Err(Error::InvalidInput);
        }
        let mut values: Vec<Field> = Vec::with_capacity(self.wire_count);
        for operation in &self.operations {
            match *operation {
                Operation::Input {
                    index,
                    public: is_public,
                    ..
                } => {
                    values.push(if is_public { public[index] } else { private[index] });
                }
                Operation::Constant { value, .. } => values.push(value),
                Operation::Add { lhs, rhs, .. } => values.push(values[lhs.index()] + values[rhs.index()]),
                Operation::Mul { lhs, rhs, .. } => values.push(values[lhs.index()] * values[rhs.index()]),
                Operation::Inverse { input, .. } => {
                    values.push(values[input.index()].inverse().ok_or(Error::InvalidWitness)?);
                }
                Operation::Limb { input, limb, .. } => {
                    values.push(Field::from(values[input.index()].0[limb as usize]));
                }
                Operation::Compose { limbs, .. } => {
                    let [a, b, c] = limbs.map(|wire| base_word(values[wire.index()]));
                    values.push(Field([a?, b?, c?]));
                }
                Operation::HintBit { input, bit, .. } => {
                    let bit = bit as usize;
                    values.push(Field::from((values[input.index()].0[bit / 64] >> (bit % 64)) & 1));
                }
                Operation::AssertEqual { lhs, rhs } => {
                    if values[lhs.index()] != values[rhs.index()] {
                        return Err(Error::InvalidWitness);
                    }
                }
                Operation::AssertBool { input } => {
                    let value = values[input.index()];
                    if value != Field::ZERO && value != Field::ONE {
                        return Err(Error::InvalidWitness);
                    }
                }
                Operation::Blake2s { ref input, .. } => {
                    let mut words = [0u64; 14];
                    for (word, wire) in words.iter_mut().zip(input.iter()) {
                        *word = base_word(values[wire.index()])?;
                    }
                    let mut message = [0u8; 64];
                    for (bytes, word) in message.chunks_exact_mut(8).zip(&words[..8]) {
                        bytes.copy_from_slice(&word.to_le_bytes());
                    }
                    let mut chaining = std::array::from_fn(|i| (words[8 + i / 2] >> (32 * (i % 2))) as u32);
                    leanvm_guest::blake2s_compress(
                        &mut chaining,
                        &message,
                        words[12],
                        words[13] as u32,
                        (words[13] >> 32) as u32,
                    );
                    values.extend(
                        chaining
                            .chunks_exact(2)
                            .map(|pair| Field::from(u64::from(pair[0]) | (u64::from(pair[1]) << 32))),
                    );
                }
            }
        }
        Ok(values)
    }
}

fn base_word(value: Field) -> Result<u64, Error> {
    if value.0[1] != 0 || value.0[2] != 0 {
        return Err(Error::InvalidWitness);
    }
    Ok(value.0[0])
}

#[cfg(test)]
mod tests {
    use super::{Builder, Error, Field};

    #[test]
    #[should_panic(expected = "wire belongs to another builder")]
    fn cross_builder_wires_are_rejected_before_identity_folding() {
        let first = Builder::new();
        let second = Builder::new();
        second.mul(second.constant(Field::ZERO), first.input(false));
    }

    #[test]
    fn bit_decomposition_preserves_tower_boundaries() {
        let builder = Builder::new();
        let input = builder.input(false);
        let bits = builder.bits(input, 192);
        let circuit = builder.finish();
        for value in [
            Field::ZERO,
            Field([u64::MAX; 3]),
            Field([1 | (1 << 63), 1 | (1 << 63), 1 | (1 << 63)]),
            Field([0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210, 0x8181_4242_2424_1818]),
        ] {
            let values = circuit.evaluate(&[], &[value]).unwrap();
            for (bit, wire) in bits.iter().enumerate() {
                assert_eq!(values[wire.index()], Field::from((value.0[bit / 64] >> (bit % 64)) & 1));
            }
        }
    }

    #[test]
    fn blake_abi_preserves_message_chaining_counter_and_both_flags() {
        let builder = Builder::new();
        let inputs = std::array::from_fn(|_| builder.input(false));
        let outputs = builder.blake2s(inputs);
        let circuit = builder.finish();
        let message: [u32; 16] = std::array::from_fn(|i| 0x0123_4567u32.wrapping_mul(i as u32 + 1));
        let chaining: [u32; 8] = std::array::from_fn(|i| 0xfedc_ba98u32.wrapping_mul(i as u32 + 1));
        let counter = 0x9876_5432_10fe_dcba;
        let (f0, f1) = (0x1357_9bdfu32, 0x2468_ace0u32);
        let mut private = [Field::ZERO; 14];
        for (target, pair) in private[..8].iter_mut().zip(message.chunks_exact(2)) {
            *target = Field::from(u64::from(pair[0]) | (u64::from(pair[1]) << 32));
        }
        for (target, pair) in private[8..12].iter_mut().zip(chaining.chunks_exact(2)) {
            *target = Field::from(u64::from(pair[0]) | (u64::from(pair[1]) << 32));
        }
        private[12] = Field::from(counter);
        private[13] = Field::from(u64::from(f0) | (u64::from(f1) << 32));
        let values = circuit.evaluate(&[], &private).unwrap();
        let expected = flock::hash::blake2s_compress(&chaining, &message, counter, f0, f1);
        for (wire, pair) in outputs.into_iter().zip(expected.chunks_exact(2)) {
            assert_eq!(
                values[wire.index()],
                Field::from(u64::from(pair[0]) | (u64::from(pair[1]) << 32))
            );
        }
        private[13].0[2] = 1;
        assert_eq!(circuit.evaluate(&[], &private), Err(Error::InvalidWitness));
    }

    #[test]
    fn folding_preserves_inputs_and_rejecting_constraints() {
        let builder = Builder::new();
        let public = builder.input(true);
        let private = builder.input(false);
        let another_public = builder.input(true);
        builder.assert_equal(private, another_public);
        builder.assert_equal(builder.add(public, public), builder.constant(Field::ZERO));
        let circuit = builder.finish();
        assert!(circuit.evaluate(&[Field::Y, Field::ONE], &[Field::ONE]).is_ok());
        assert_eq!(circuit.evaluate(&[Field::Y], &[Field::ONE]), Err(Error::InvalidInput));
        assert_eq!(
            circuit.evaluate(&[Field::Y, Field::ONE], &[Field::ZERO]),
            Err(Error::InvalidWitness)
        );

        let inverse = Builder::new();
        inverse.inverse(inverse.constant(Field::ZERO));
        assert_eq!(inverse.finish().evaluate(&[], &[]), Err(Error::InvalidWitness));

        let compose = Builder::new();
        compose.compose([compose.constant(Field::Y); 3]);
        assert_eq!(compose.finish().evaluate(&[], &[]), Err(Error::InvalidWitness));
    }
}
