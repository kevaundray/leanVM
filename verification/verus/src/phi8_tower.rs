//! The table of `φ₈: GF(2⁸) → K`, embedded in `E`.
//!
//! The executable function is `build_phi8_table_192` of `crates/primitives/src/field/phi8_tower.rs`;
//! `tests/equivalence/phi8_tower.rs` checks the table it builds against `PHI_8_TABLE_192`.
//!
//! Specification: entry `i` is the subset sum [`phi8`] of the eight basis words selected by the bits of `i`, in
//! `K` (`c1 = c2 = 0`). So the table is `F_2`-linear in its index ([`lemma_phi8_xor`]) and, the basis being
//! independent, zero only at index 0 ([`lemma_phi8_nonzero`]). Its first `2^k` entries are therefore an
//! `F_2`-subspace of `K` of `2^k` distinct elements, the skip domain. That `φ₈` is also multiplicative (a field
//! embedding) is not used here and not proven.
use crate::gf2_64x3::F192;
use vstd::prelude::*;

verus! {

/// φ₈(2ᵏ) for k ∈ [0,8): the images of the GF(2⁸) polynomial basis. All in
/// `F64` (`c1 == c2 == 0`).
pub const PHI_8_BASIS: [u64; 8] = [
    0x0000000000000001,
    0x033ce8beddc8a656,
    0x512620375ed2a108,
    0x0c9e636090aafc01,
    0xba4f3cd82801769c,
    0xba26e7904adb4a47,
    0x467698598926dc01,
    0x4418ae808b28bdd0,
];

/// The basis word `b` as a spec value (the constant's entries, spelled out for the solver).
pub open spec fn basis(b: int) -> u64 {
    if b == 0 {
        0x0000000000000001
    } else if b == 1 {
        0x033ce8beddc8a656
    } else if b == 2 {
        0x512620375ed2a108
    } else if b == 3 {
        0x0c9e636090aafc01
    } else if b == 4 {
        0xba4f3cd82801769c
    } else if b == 5 {
        0xba26e7904adb4a47
    } else if b == 6 {
        0x467698598926dc01
    } else {
        0x4418ae808b28bdd0
    }
}

/// The XOR of the basis words selected by bits `0..nb` of `i`.
pub open spec fn phi8_bits(i: usize, nb: nat) -> u64
    decreases nb,
{
    if nb == 0 {
        0
    } else {
        phi8_bits(i, (nb - 1) as nat) ^ (if (i >> ((nb - 1) as usize)) & 1 == 1 {
            basis(nb - 1)
        } else {
            0
        })
    }
}

/// `φ₈(i)`, in `K`.
pub open spec fn phi8(i: usize) -> u64 {
    phi8_bits(i, 8)
}

/// `φ₈(i)` as an element of `E`.
pub open spec fn phi8_e(i: usize) -> F192 {
    F192 { c0: phi8(i), c1: 0, c2: 0 }
}

proof fn lemma_basis_const()
    ensures
        forall|b: int| 0 <= b < 8 ==> #[trigger] PHI_8_BASIS[b] == basis(b),
{
}

proof fn lemma_xor_select(a: u64, b: u64, sa: u64, sb: u64, s: u64, t: u64)
    requires
        (sa == 0 || sa == t),
        (sb == 0 || sb == t),
        s == (if (sa == t) != (sb == t) { t } else { 0 }),
        t != 0,
    ensures
        (a ^ b) ^ s == (a ^ sa) ^ (b ^ sb),
{
    assert((sa == 0 || sa == t) && (sb == 0 || sb == t) && s == (if (sa == t) != (sb == t) { t } else { 0 }) && t
        != 0 ==> (a ^ b) ^ s == (a ^ sa) ^ (b ^ sb)) by (bit_vector);
}

/// `φ₈` is `F_2`-linear: `φ₈(i ^ j) = φ₈(i) + φ₈(j)`.
pub proof fn lemma_phi8_xor_bits(i: usize, j: usize, nb: nat)
    requires
        nb <= 8,
    ensures
        phi8_bits(i ^ j, nb) == phi8_bits(i, nb) ^ phi8_bits(j, nb),
    decreases nb,
{
    if nb > 0 {
        lemma_phi8_xor_bits(i, j, (nb - 1) as nat);
        let k = (nb - 1) as usize;
        assert(((i ^ j) >> k) & 1 == 1 <==> (((i >> k) & 1 == 1) != ((j >> k) & 1 == 1))) by (bit_vector);
        let t = basis(nb - 1);
        let sa = if (i >> k) & 1 == 1 { t } else { 0 };
        let sb = if (j >> k) & 1 == 1 { t } else { 0 };
        let s = if ((i ^ j) >> k) & 1 == 1 { t } else { 0 };
        assert(t != 0);
        lemma_xor_select(phi8_bits(i, (nb - 1) as nat), phi8_bits(j, (nb - 1) as nat), sa, sb, s, t);
    } else {
        assert(0u64 ^ 0u64 == 0u64) by (bit_vector);
    }
}

pub proof fn lemma_phi8_xor(i: usize, j: usize)
    ensures
        phi8(i ^ j) == phi8(i) ^ phi8(j),
{
    lemma_phi8_xor_bits(i, j, 8);
}

/// `phi8(i)` for `i < 256` is nonzero exactly when `i` is: the basis is independent over `F_2`.
pub open spec fn all_nonzero_upto(n: nat) -> bool
    decreases n,
{
    if n <= 1 {
        true
    } else {
        all_nonzero_upto((n - 1) as nat) && phi8((n - 1) as usize) != 0
    }
}

proof fn lemma_all_nonzero_get(n: nat, i: nat)
    requires
        all_nonzero_upto(n),
        1 <= i < n,
    ensures
        phi8(i as usize) != 0,
    decreases n,
{
    if i < n - 1 {
        lemma_all_nonzero_get((n - 1) as nat, i);
    }
}

pub proof fn lemma_phi8_nonzero(i: usize)
    requires
        1 <= i < 256,
    ensures
        phi8(i) != 0,
{
    assert(all_nonzero_upto(256)) by (compute_only);
    lemma_all_nonzero_get(256, i as nat);
}

pub proof fn lemma_phi8_zero()
    ensures
        phi8(0) == 0,
{
    assert(phi8(0) == 0) by (compute_only);
}

/// The table: entry `value` is the XOR of the basis words selected by its bits.
///
/// The same body as production.
pub const fn build_phi8_table_192() -> (table: [F192; 256])
    ensures
        forall|i: int| 0 <= i < 256 ==> #[trigger] table[i] == phi8_e(i as usize),
{
    let mut table = [F192::ZERO; 256];
    proof {
        lemma_phi8_zero();
        lemma_basis_const();
    }
    let mut value = 1;
    while value < table.len()
        invariant
            1 <= value <= 256,
            table[0] == phi8_e(0),
            forall|i: int| 1 <= i < value ==> #[trigger] table[i] == phi8_e(i as usize),
            forall|b: int| 0 <= b < 8 ==> #[trigger] PHI_8_BASIS[b] == basis(b),
        decreases 256 - value,
    {
        let mut c0 = 0u64;
        let mut bit = 0;
        while bit < PHI_8_BASIS.len()
            invariant
                1 <= value < 256,
                bit <= 8,
                c0 == phi8_bits(value, bit as nat),
                forall|b: int| 0 <= b < 8 ==> #[trigger] PHI_8_BASIS[b] == basis(b),
            decreases 8 - bit,
        {
            assert((value & (1usize << bit) != 0) == ((value >> bit) & 1 == 1)) by (bit_vector)
                requires
                    bit < 8,
            ;
            if value & (1 << bit) != 0 {
                c0 ^= PHI_8_BASIS[bit];
            }
            proof {
                assert(c0 ^ 0 == c0) by (bit_vector);
            }
            bit += 1;
        }
        table[value] = F192::new(c0, 0, 0);
        value += 1;
    }
    table
}

/// The unique GF(2^8) subfield embedded in F192. It lies in the F64 base, so
/// both higher extension coordinates are zero.
///
/// Verus's `exec static` form, to state what the table holds.
pub exec static PHI_8_TABLE_192: [F192; 256]
    ensures
        forall|i: int| 0 <= i < 256 ==> #[trigger] PHI_8_TABLE_192[i] == phi8_e(i as usize),
{
    build_phi8_table_192()
}

} // verus!
