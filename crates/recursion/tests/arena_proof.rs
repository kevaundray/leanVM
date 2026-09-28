use leanvm_guest::Field;
use recursion::{Builder, Key};

#[test]
fn cached_key_and_proofs_survive_phase_resets() {
    lean_vm::init_prover_pool();
    zk_alloc::enable_arena();
    let builder = Builder::new();
    let input = builder.input(false);
    let output = builder.input(true);
    let factor = Field::new(3, 5, 7);
    let multiplier = builder.constant(factor);
    let mut state = input;
    for _ in 0..64 {
        state = builder.mul(state, multiplier);
    }
    builder.assert_equal(state, output);
    let key = {
        let _phase = zk_alloc::enter_phase();
        Key::new(builder.finish()).unwrap()
    };
    let private = [Field::new(11, 13, 17)];
    let mut result = private[0];
    for _ in 0..64 {
        result *= factor;
    }
    let public = [result];
    let first = key.prove(&public, &private, 1).unwrap();
    key.verify(&public, &first).unwrap();
    let second = key.prove(&public, &private, 2).unwrap();
    key.verify(&public, &first).unwrap();
    key.verify(&public, &second).unwrap();
}
