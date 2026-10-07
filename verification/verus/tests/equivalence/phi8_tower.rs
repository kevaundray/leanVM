//! The verified φ₈ table against `primitives::field::PHI_8_TABLE_192`, entry by entry.
use leanvm_verus::phi8_tower as verified;
use primitives::field::PHI_8_TABLE_192;

#[test]
fn tables_match() {
    let built = verified::build_phi8_table_192();
    for (i, p) in PHI_8_TABLE_192.iter().enumerate() {
        for v in [built[i], verified::PHI_8_TABLE_192[i]] {
            assert_eq!((v.c0, v.c1, v.c2), (p.c0, p.c1, p.c2), "entry {i}");
        }
    }
}
