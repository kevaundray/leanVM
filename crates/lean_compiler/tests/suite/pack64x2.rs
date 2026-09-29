use lean_compiler::{compile, parse};
use leanvm_core::cpu::{Fault, prove, verify};
use primitives::field::{F64, F192};

use crate::common::mix;

#[test]
fn pack64x2_proves_and_verifies() {
    let src = "\
@inline
def pack64x2(a, b):
    assert_in_k(a, b)
    return a + f192(0, 1, 0) * b

def main():
    a = 5
    b = 7
    packed = pack64x2(a, b)
    p = 1
    p[1] = packed
    p[GEN] = packed
    return
";
    let program = compile(&parse(src).expect("parse"));
    let want = [F192::new(5, 7, 0), F192::new(5, 7, 0)];
    let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    let counts = mix(src, want);
    assert_eq!(
        (counts[0], counts[1], counts[4]),
        (1, 2, 2),
        "XOR, MUL and JUMP lowering"
    );
    verify(&program, &want, &proof).expect("pack64x2 program verifies");
}

#[test]
fn pack64x2_rejects_extension_field_source() {
    let src = "\
@inline
def pack64x2(a, b):
    assert_in_k(a, b)
    return a + f192(0, 1, 0) * b

def main():
    a = StackBuf(1)
    hint_witness(a[0:1], \"a\")
    packed = pack64x2(a[0], 7)
    p = 1
    p[1] = packed
    p[GEN] = packed
    return
";
    let mut program = compile(&parse(src).expect("parse"));
    program.set_witness("a", vec![vec![F192::new(5, 1, 0)]]);
    let err = program
        .execute([F192::from(F64::ONE), F192::from(F64::ONE)])
        .err()
        .expect("the run must fail");
    assert!(
        matches!(
            err.fault,
            Fault::NotInK {
                what: "JUMP target",
                ..
            }
        ),
        "{err}"
    );
}
