use std::{
    fs,
    path::PathBuf,
    process::{Command, Output},
};

use fiat_shamir::transcript::RawProof;
use leanvm_guest::Field;
use recursion::{Builder, Key};

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!("leanvm-native-python-{}-{nonce}", std::process::id()));
        fs::create_dir(&path).unwrap();
        Self(path)
    }

    fn key(&self, key: &Key) {
        let bytes: Vec<_> = key.descriptor().iter().flat_map(|word| word.to_le_bytes()).collect();
        fs::write(self.0.join("key.bin"), bytes).unwrap();
    }

    fn public(&self, public: &[Field]) {
        let bytes: Vec<_> = public.iter().flat_map(|value| value.to_le_bytes()).collect();
        fs::write(self.0.join("public.bin"), bytes).unwrap();
    }

    fn proof(&self, raw: &RawProof) {
        // RV64PRF1 is the expanded transcript transport, not a RISC verifier call.
        let transport = riscv_proof::Proof {
            stream: raw
                .stream
                .iter()
                .map(|value| Field::new(value.c0, value.c1, value.c2))
                .collect(),
            merkle: raw
                .merkle
                .iter()
                .map(|opening| riscv_proof::Opening {
                    leaf: opening.leaf_data.iter().map(|word| word.0).collect(),
                    siblings: opening.path.clone(),
                })
                .collect(),
        };
        fs::write(self.0.join("proof.bin"), transport.to_bytes()).unwrap();
    }

    fn verify(&self) -> Output {
        let verifier = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../python-verifier/verifier.py");
        Command::new(std::env::var_os("PYTHON").unwrap_or_else(|| "python3".into()))
            .arg(verifier)
            .arg("--native-key")
            .arg(self.0.join("key.bin"))
            .arg("--public-fields")
            .arg(self.0.join("public.bin"))
            .arg("--proof")
            .arg(self.0.join("proof.bin"))
            .output()
            .expect("launch independent Python verifier")
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn accepted(output: Output) {
    assert!(
        output.status.success(),
        "independent verifier rejected authentic proof: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

fn rejected(output: Output) {
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected proof rejection, got {:?}: {}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
}

fn arithmetic_key(factor: Field) -> Key {
    let builder = Builder::new();
    let input = builder.input(false);
    let output = builder.input(true);
    builder.assert_equal(builder.mul(input, builder.constant(factor)), output);
    Key::new(builder.finish()).unwrap()
}

#[test]
fn native_key_interoperates_with_independent_python() {
    lean_vm::init_prover_pool();
    let fixture = Fixture::new();
    let builder = Builder::new();
    let x = builder.input(false);
    let word = builder.input(false);
    let bit = builder.input(false);
    builder.assert_bool(bit);
    let one = builder.constant(Field::ONE);
    builder.assert_equal(builder.mul(x, builder.inverse(x)), one);
    let limbs = std::array::from_fn(|index| builder.limb(x, index as u8));
    builder.assert_equal(builder.compose(limbs), x);
    let factor = Field::new(3, 5, 7);
    let computed = builder.add(builder.mul(x, builder.constant(factor)), x);
    builder.assert_equal(computed, builder.input(true));
    let mut compression = [word; 14];
    for index in 0..4 {
        compression[8 + index] = builder.constant(Field::from(lean_vm::hash_flock::IV[index].0));
    }
    compression[12] = builder.constant(Field::from(64));
    compression[13] = builder.constant(Field::from(u32::MAX as u64));
    for output in builder.blake2s(compression) {
        builder.assert_equal(output, builder.input(true));
    }
    let key = Key::new(builder.finish()).unwrap();
    // All thirteen tables are genuinely used, including extension-valued public data.
    assert!((0..13).all(|kind| key.descriptor()[12 + 5 * kind] == 1));
    let private = [Field::new(11, 13, 17), Field::from(3), Field::ONE];
    let message: Vec<_> = (0..8).flat_map(|_| 3u64.to_le_bytes()).collect();
    let digest = primitives::hash::hash(&message);
    let mut public = vec![private[0] * factor + private[0]];
    public.extend(
        (0..4).map(|index| Field::from(u64::from_le_bytes(digest[8 * index..8 * index + 8].try_into().unwrap()))),
    );
    let proof = key.prove(&public, &private, 2).unwrap();
    key.verify(&public, &proof).unwrap();
    let raw = key.raw_proof(&public, &proof).unwrap();
    fixture.key(&key);
    fixture.public(&public);
    fixture.proof(&raw);
    accepted(fixture.verify());

    let mut changed_public = public.clone();
    changed_public[0].0[2] ^= 1;
    assert!(key.verify(&changed_public, &proof).is_err());
    fixture.public(&changed_public);
    rejected(fixture.verify());
    fixture.public(&public);

    // Changing the trusted fixed commitment must reject even with identical dimensions.
    let mut changed_descriptor = key.descriptor().to_vec();
    changed_descriptor[8] ^= 1;
    fs::write(
        fixture.0.join("key.bin"),
        changed_descriptor
            .iter()
            .flat_map(|word| word.to_le_bytes())
            .collect::<Vec<_>>(),
    )
    .unwrap();
    rejected(fixture.verify());
    fixture.key(&key);

    let mut changed_proof = proof.clone();
    changed_proof.stream[1].c0 ^= 1;
    assert!(key.verify(&public, &changed_proof).is_err());
    let mut changed_raw = raw.clone();
    changed_raw.stream[1].c0 ^= 1;
    fixture.proof(&changed_raw);
    rejected(fixture.verify());

    let mut changed_proof = proof.clone();
    changed_proof.merkle[0].leaf_data[0].last_mut().unwrap().0 ^= 1;
    assert!(key.verify(&public, &changed_proof).is_err());
    let mut changed_raw = raw.clone();
    changed_raw.merkle[0].leaf_data.last_mut().unwrap().0 ^= 1;
    fixture.proof(&changed_raw);
    rejected(fixture.verify());

    let mut trailing = raw.clone();
    trailing.stream.push(primitives::field::F192::ZERO);
    fixture.proof(&trailing);
    rejected(fixture.verify());
    let mut trailing = raw.clone();
    trailing.merkle.push(raw.merkle[0].clone());
    fixture.proof(&trailing);
    rejected(fixture.verify());

    // No Flock: no ring-map challenges, and pruned L0 zero lanes in both stacks.
    let sparse = arithmetic_key(factor);
    let private = [Field::new(19, 23, 29)];
    let public = [private[0] * factor];
    let sparse_proof = sparse.prove(&public, &private, 4).unwrap();
    sparse.verify(&public, &sparse_proof).unwrap();
    let sparse_raw = sparse.raw_proof(&public, &sparse_proof).unwrap();
    assert!(sparse.descriptor()[2] < 64 && sparse.descriptor()[4] < 64);
    fixture.key(&sparse);
    fixture.public(&public);
    fixture.proof(&sparse_raw);
    accepted(fixture.verify());
    let other = arithmetic_key(factor + Field::ONE);
    assert!(other.verify(&public, &sparse_proof).is_err());
    fixture.key(&other);
    rejected(fixture.verify());
    fixture.key(&sparse);
    let mut changed_prefix = sparse_raw;
    assert_eq!(changed_prefix.merkle[0].leaf_data[0].0, 0);
    changed_prefix.merkle[0].leaf_data[0].0 = 1;
    fixture.proof(&changed_prefix);
    rejected(fixture.verify());
}
