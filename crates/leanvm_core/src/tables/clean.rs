// Generated from LeanVMCircuits.ExtensionProduct.rows by GenerateTables.lean. Do not edit.
// The Clean assertion and arbitrary-row soundness theorem use these exact identities.

use crate::leaf::BusForm;
use primitives::field::F192;

/// EXT's three committed field identities, bound to the table's local columns.
pub(crate) fn extension_identities(n_columns: usize, accumulate: usize, limbs: usize, new: usize) -> Vec<BusForm> {
    let mut f0 = BusForm::new(n_columns, F192::ZERO);
    f0.coeffs[new] = F192::ONE;
    f0.prods = vec![
        (accumulate, limbs + 6, F192::ONE),
        (limbs, limbs + 3, F192::ONE),
        (limbs + 1, limbs + 5, F192::ONE),
        (limbs + 2, limbs + 4, F192::ONE),
    ];
    let mut f1 = BusForm::new(n_columns, F192::ZERO);
    f1.coeffs[new + 1] = F192::ONE;
    f1.prods = vec![
        (accumulate, limbs + 7, F192::ONE),
        (limbs, limbs + 4, F192::ONE),
        (limbs + 1, limbs + 3, F192::ONE),
        (limbs + 1, limbs + 5, F192::ONE),
        (limbs + 2, limbs + 4, F192::ONE),
        (limbs + 2, limbs + 5, F192::ONE),
    ];
    let mut f2 = BusForm::new(n_columns, F192::ZERO);
    f2.coeffs[new + 2] = F192::ONE;
    f2.prods = vec![
        (accumulate, limbs + 8, F192::ONE),
        (limbs, limbs + 5, F192::ONE),
        (limbs + 1, limbs + 4, F192::ONE),
        (limbs + 2, limbs + 3, F192::ONE),
        (limbs + 2, limbs + 5, F192::ONE),
    ];
    vec![f0, f1, f2]
}
