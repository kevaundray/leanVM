use bincode::Options;
use leanvm_guest::{
    Field,
    deferred::{self, Claim, MAX_CHILDREN, PUBLIC_FIELDS},
};

use crate::{
    Error, Key, Proof, Summary,
    context::{Context, Source, Symbolic, Witness},
    native::{self, KeyInfo},
    risc_layout::Templates,
    risc_verifier,
    tables::{self, NativeTable},
    transcript::hash_words,
    uint::Uint,
};

const NODE_MAGIC: [u8; 8] = *b"RVNODE01";
const MAX_NODE_BYTES: usize = 64 << 20;
const ADVICE_SOURCE: usize = MAX_CHILDREN + 1;

#[derive(Clone, Debug)]
pub struct NodeProof {
    pub height: u32,
    pub proof: Proof,
}

fn codec() -> impl Options {
    bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .reject_trailing_bytes()
}

impl NodeProof {
    pub fn to_bytes(&self) -> Vec<u8> {
        codec()
            .serialize(&(NODE_MAGIC, self.height, &self.proof))
            .expect("native proof serializes")
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        if bytes.len() > MAX_NODE_BYTES {
            return Err(Error::InvalidProof);
        }
        let (magic, height, proof): ([u8; 8], u32, Proof) = codec()
            .with_limit(bytes.len() as u64)
            .deserialize(bytes)
            .map_err(|_| Error::InvalidProof)?;
        if magic != NODE_MAGIC {
            return Err(Error::InvalidProof);
        }
        Ok(Self { height, proof })
    }
}

pub struct Child<'a> {
    pub statement: [u8; 32],
    pub proof: &'a NodeProof,
}

/// One trusted RV64IM program and one recursive verification key at every height.
/// The execution must enforce the application semantics of its deferred binding.
pub struct Recursor {
    key: Key,
    templates: Templates,
    schemas: [NativeTable; tables::KIND_COUNT],
}

type Composition<F> = ([F; 4], [(F, [F; PUBLIC_FIELDS]); MAX_CHILDREN]);

fn composition<C: Context>(ctx: &C) -> Result<Composition<C::F>, Error> {
    let public = (0..PUBLIC_FIELDS)
        .map(|i| ctx.public(i))
        .collect::<Result<Vec<_>, _>>()?;
    for &word in &public[..8] {
        ctx.bits(word, 64)?;
    }
    let parent_height = Uint::from_field(ctx, public[8], 32)?;
    let count = Uint::from_field(ctx, ctx.read_scalar(ADVICE_SOURCE, ctx.one())?, 2)?;
    ctx.assert_zero(count.eq_const(ctx, 3))?;
    let has_children = ctx.not(count.eq_const(ctx, 0));
    let mut maximum = Uint::constant(ctx, 0, 32);
    let mut message = Vec::with_capacity(5 + 9 * MAX_CHILDREN);
    message.extend(native::digest_words(
        ctx,
        primitives::hash::hash(deferred::CLAIMS_DOMAIN),
    ));
    message.push(count.value(ctx));
    let mut children = [(ctx.zero(), [ctx.zero(); PUBLIC_FIELDS]); MAX_CHILDREN];
    for (index, output) in children.iter_mut().enumerate() {
        let enabled = if index == 0 {
            has_children
        } else {
            count.eq_const(ctx, 2)
        };
        let mut child = [ctx.zero(); PUBLIC_FIELDS];
        for word in &mut child[..4] {
            *word = ctx.read_scalar(ADVICE_SOURCE, enabled)?;
            ctx.bits(*word, 64)?;
        }
        child[4..8].copy_from_slice(&public[4..8]);
        child[8] = ctx.read_scalar(ADVICE_SOURCE, enabled)?;
        let height = Uint::from_field(ctx, child[8], 32)?;
        ctx.assert_equal_if(enabled, height.lt(ctx, &parent_height), ctx.one())?;
        maximum = Uint::select(ctx, maximum.lt(ctx, &height), &height, &maximum);
        message.push(ctx.one());
        message.extend_from_slice(&public[4..8]);
        message.extend(native::public_digest(ctx, &child)?);
        *output = (enabled, child);
    }
    let (next, carry) = maximum.add(ctx, &Uint::constant(ctx, 1, 32));
    ctx.assert_zero(ctx.mul(has_children, carry))?;
    ctx.assert_equal(parent_height.value(ctx), ctx.mul(has_children, next.value(ctx)))?;
    // Three canonical lengths avoid characteristic-two addition for byte counts.
    let length = ctx.select(
        count.eq_const(ctx, 2),
        ctx.base(23),
        ctx.select(has_children, ctx.base(14), ctx.base(5)),
    );
    let claims = hash_words(ctx, &message, length)?;
    let mut binding = Vec::with_capacity(12);
    binding.extend(native::digest_words(
        ctx,
        primitives::hash::hash(deferred::BINDING_DOMAIN),
    ));
    binding.extend_from_slice(&public[..4]);
    binding.extend(claims);
    Ok((hash_words(ctx, &binding, ctx.base(12))?, children))
}

fn program<C: Context>(
    ctx: &C,
    templates: &Templates,
    schemas: &[NativeTable; tables::KIND_COUNT],
) -> Result<(), Error> {
    let digest = [ctx.public(4)?, ctx.public(5)?, ctx.public(6)?, ctx.public(7)?];
    let key = KeyInfo::read(ctx, ADVICE_SOURCE, digest, PUBLIC_FIELDS)?;
    let (binding, children) = composition(ctx)?;
    risc_verifier::verify(ctx, 0, ctx.one(), templates, binding)?;
    for (index, (enabled, public)) in children.iter().enumerate() {
        native::verify(ctx, index + 1, *enabled, &key, public, schemas)?;
    }
    Ok(())
}

impl Recursor {
    pub fn new(program_info: &riscv_proof::ProgramInfo) -> Result<Self, Error> {
        let templates = Templates::new(program_info)?;
        let schemas = native::schemas();
        let symbolic = Symbolic::new(PUBLIC_FIELDS);
        program(&symbolic, &templates, &schemas)?;
        let key = Key::new(symbolic.finish())?;
        Ok(Self {
            key,
            templates,
            schemas,
        })
    }

    pub fn key_digest(&self) -> [u8; 32] {
        self.key.digest()
    }
    pub fn summary(&self) -> Summary {
        self.key.summary()
    }

    pub fn prove(
        &self,
        statement: [u8; 32],
        execution: &riscv_proof::Proof,
        children: &[Child<'_>],
        log_inv_rate: usize,
    ) -> Result<NodeProof, Error> {
        if children.len() > MAX_CHILDREN {
            return Err(Error::InvalidInput);
        }
        let height = children
            .iter()
            .map(|child| child.proof.height)
            .max()
            .map_or(Some(0), |height| height.checked_add(1))
            .ok_or(Error::InvalidInput)?;
        let public = deferred::public_fields(&Claim {
            statement,
            key: self.key_digest(),
            height,
        });
        let mut advice: Vec<_> = self.key.descriptor().iter().copied().map(Field::from).collect();
        advice.push(Field::from(children.len() as u64));
        let mut raw = Vec::with_capacity(children.len());
        for child in children {
            let public = deferred::public_fields(&Claim {
                statement: child.statement,
                key: self.key_digest(),
                height: child.proof.height,
            });
            advice.extend_from_slice(&public[..4]);
            advice.push(public[8]);
            raw.push(self.key.raw_proof(&public, &child.proof.proof)?);
        }
        let mut sources = Vec::with_capacity(MAX_CHILDREN + 2);
        sources.push(Source::Risc(execution));
        for index in 0..MAX_CHILDREN {
            sources.push(raw.get(index).map_or(Source::Advice(&[]), Source::Native));
        }
        sources.push(Source::Advice(&advice));
        let witness = Witness::new(&public, sources);
        program(&witness, &self.templates, &self.schemas)?;
        let private = witness.finish()?;
        let proof = self.key.prove(&public, &private, log_inv_rate)?;
        Ok(NodeProof { height, proof })
    }

    pub fn verify(&self, statement: [u8; 32], proof: &NodeProof) -> Result<(), Error> {
        let public = deferred::public_fields(&Claim {
            statement,
            key: self.key_digest(),
            height: proof.height,
        });
        self.key.verify(&public, &proof.proof)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn public(height: u32) -> [Field; PUBLIC_FIELDS] {
        deferred::public_fields(&Claim {
            statement: [17; 32],
            key: [29; 32],
            height,
        })
    }

    #[test]
    fn deferred_binding_and_height_are_constrained() {
        let symbolic = Symbolic::new(PUBLIC_FIELDS);
        let (digest, _) = composition(&symbolic).unwrap();
        let circuit = symbolic.finish();
        for heights in [vec![], vec![0], vec![3, 8]] {
            let height = heights.iter().copied().max().map_or(0, |height| height + 1);
            let public = public(height);
            let mut advice = vec![Field::from(heights.len() as u64)];
            let children: Vec<_> = heights
                .iter()
                .enumerate()
                .map(|(i, &height)| Claim {
                    statement: [i as u8 + 1; 32],
                    key: [29; 32],
                    height,
                })
                .collect();
            for child in &children {
                let fields = deferred::public_fields(child);
                advice.extend_from_slice(&fields[..4]);
                advice.push(fields[8]);
            }
            let witness = Witness::new(
                &public,
                vec![
                    Source::Advice(&[]),
                    Source::Advice(&[]),
                    Source::Advice(&[]),
                    Source::Advice(&advice),
                ],
            );
            let (actual, _) = composition(&witness).unwrap();
            let expected = deferred::binding([17; 32], &children);
            let expected: [Field; 4] = std::array::from_fn(|i| {
                Field::from(u64::from_le_bytes(expected[8 * i..8 * i + 8].try_into().unwrap()))
            });
            assert_eq!(actual, expected);
            let private = witness.finish().unwrap();
            let values = circuit.evaluate(&public, &private).unwrap();
            assert_eq!(digest.map(|word| values[word.index()]), expected);
            let mut wrong = public;
            wrong[8] += Field::ONE;
            assert!(circuit.evaluate(&wrong, &private).is_err());
        }
        for (height, advice) in [
            (0, vec![Field::from(3)]),
            (
                0,
                vec![
                    Field::ONE,
                    Field::ZERO,
                    Field::ZERO,
                    Field::ZERO,
                    Field::ZERO,
                    Field::from(u32::MAX as u64),
                ],
            ),
        ] {
            let public = public(height);
            let witness = Witness::new(
                &public,
                vec![
                    Source::Advice(&[]),
                    Source::Advice(&[]),
                    Source::Advice(&[]),
                    Source::Advice(&advice),
                ],
            );
            assert!(composition(&witness).is_err());
        }
    }

    #[test]
    #[ignore]
    fn same_key_recursion_proves_zero_one_and_two_children() {
        lean_vm::init_prover_pool();
        let instructions = [
            0x00002537u32,
            0x00200893,
            0x00000073,
            0x00000513,
            0x00000893,
            0x00000073,
        ];
        let mut elf = vec![0u8; 0x100 + 4 * instructions.len()];
        elf[..7].copy_from_slice(b"\x7fELF\x02\x01\x01");
        for (at, value) in [(16, 2u16), (18, 243), (52, 64), (54, 56), (56, 1)] {
            elf[at..at + 2].copy_from_slice(&value.to_le_bytes());
        }
        elf[20..24].copy_from_slice(&1u32.to_le_bytes());
        for (at, value) in [
            (24, 0x1000u64),
            (32, 64),
            (72, 0x100),
            (80, 0x1000),
            (88, 0x1000),
            (96, (4 * instructions.len()) as u64),
            (104, 0x1000),
            (112, 0x100),
        ] {
            elf[at..at + 8].copy_from_slice(&value.to_le_bytes());
        }
        elf[64..68].copy_from_slice(&1u32.to_le_bytes());
        elf[68..72].copy_from_slice(&5u32.to_le_bytes());
        for (i, instruction) in instructions.iter().enumerate() {
            elf[0x100 + 4 * i..0x104 + 4 * i].copy_from_slice(&instruction.to_le_bytes());
        }
        let machine = riscv::Program::from_elf(&elf).unwrap();
        let recursor = Recursor::new(&riscv_proof::ProgramInfo::from_elf(&elf).unwrap()).unwrap();
        println!("same_key {:?}", recursor.summary());
        let prove = |statement, children: &[Child<'_>], rate| {
            let claims: Vec<_> = children
                .iter()
                .map(|child| Claim {
                    statement: child.statement,
                    key: recursor.key_digest(),
                    height: child.proof.height,
                })
                .collect();
            let binding = deferred::binding(statement, &claims);
            let (execution, _) = riscv_proof::host::prove(&machine, binding, &[], 100, 1).unwrap();
            let proof = recursor.prove(statement, &execution, children, rate).unwrap();
            recursor.verify(statement, &proof).unwrap();
            proof
        };
        let leaf = prove([1; 32], &[], 1);
        assert_eq!(leaf.height, 0);
        let parent = prove(
            [2; 32],
            &[Child {
                statement: [1; 32],
                proof: &leaf,
            }],
            2,
        );
        assert_eq!(parent.height, 1);
        let root = prove(
            [3; 32],
            &[
                Child {
                    statement: [1; 32],
                    proof: &leaf,
                },
                Child {
                    statement: [2; 32],
                    proof: &parent,
                },
            ],
            1,
        );
        assert_eq!(root.height, 2);
        assert!(recursor.verify([4; 32], &root).is_err());
        let encoded = root.to_bytes();
        recursor
            .verify([3; 32], &NodeProof::from_bytes(&encoded).unwrap())
            .unwrap();
        let mut trailing = encoded.clone();
        trailing.push(0);
        assert!(NodeProof::from_bytes(&trailing).is_err());
        assert!(NodeProof::from_bytes(&encoded[..encoded.len() - 1]).is_err());
        let mut changed = root.clone();
        changed.height = 1;
        assert!(recursor.verify([3; 32], &changed).is_err());
        changed = root.clone();
        changed.proof.stream[1] += primitives::field::F192::ONE;
        assert!(recursor.verify([3; 32], &changed).is_err());
        let claims = [Claim {
            statement: [1; 32],
            key: recursor.key_digest(),
            height: 0,
        }];
        let (execution, _) =
            riscv_proof::host::prove(&machine, deferred::binding([5; 32], &claims), &[], 100, 1).unwrap();
        assert!(recursor.prove([5; 32], &execution, &[], 1).is_err());
        assert!(
            recursor
                .prove(
                    [5; 32],
                    &execution,
                    &[Child {
                        statement: [2; 32],
                        proof: &leaf
                    }],
                    1
                )
                .is_err()
        );
        println!("same_key heights=0,1,2 rates=1,2 public_height_transport_and_child_binding_attacks_rejected=true");
    }
}
