use std::{collections::BTreeMap, fs::File, io::BufReader, path::Path};

use anyhow::{ensure, Context, Result};
use ark_ff::{AdditiveGroup, Field, PrimeField};
use provekit_backend_bn254::FieldElement;
use provekit_common::R1CS;
use serde::Deserialize;

type LinearCombination = BTreeMap<String, String>;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Export {
    prime: String,
    n_vars: usize,
    n_outputs: usize,
    n_pub_inputs: usize,
    n_prv_inputs: usize,
    n_constraints: usize,
    constraints: Vec<[LinearCombination; 3]>,
}

pub struct ImportedCircuit {
    pub r1cs: R1CS<FieldElement>,
    pub witness: Vec<FieldElement>,
    pub public_values: Vec<FieldElement>,
}

fn field(value: &str) -> Result<FieldElement> {
    ensure!(
        !value.is_empty() && value.bytes().all(|b| b.is_ascii_digit()),
        "expected a decimal field element"
    );
    let element = value
        .parse::<FieldElement>()
        .map_err(|_| anyhow::anyhow!("invalid field element"))?;
    ensure!(
        element.into_bigint().to_string() == value,
        "field element must be canonical and less than the BN254 scalar modulus"
    );
    Ok(element)
}

fn terms(lc: LinearCombination, n_vars: usize) -> Result<Vec<(FieldElement, usize)>> {
    lc.into_iter()
        .map(|(index, coefficient)| {
            let column: usize = index.parse().context("invalid signal index")?;
            ensure!(
                column.to_string() == index && column < n_vars,
                "signal index out of range or noncanonical"
            );
            Ok((field(&coefficient)?, column))
        })
        .collect()
}

fn import(export: Export, values: Vec<String>) -> Result<ImportedCircuit> {
    ensure!(
        export.prime == FieldElement::MODULUS.to_string(),
        "R1CS must use the BN254 scalar field"
    );
    ensure!(
        export.n_vars > 0 && export.n_vars <= u32::MAX as usize,
        "invalid R1CS signal count"
    );
    ensure!(
        export.n_constraints > 0 && export.n_constraints == export.constraints.len(),
        "invalid R1CS constraint count"
    );
    let public_count = export
        .n_outputs
        .checked_add(export.n_pub_inputs)
        .context("public input count overflow")?;
    let input_count = public_count
        .checked_add(export.n_prv_inputs)
        .context("input count overflow")?;
    ensure!(
        input_count < export.n_vars,
        "input and output signals exceed available signals"
    );
    ensure!(values.len() == export.n_vars, "witness length does not match R1CS");
    let witness = values.iter().map(|v| field(v)).collect::<Result<Vec<_>>>()?;
    ensure!(witness[0] == FieldElement::ONE, "constant signal must equal one");
    let mut r1cs = R1CS::new();
    r1cs.add_witnesses(export.n_vars);
    r1cs.num_public_inputs = public_count;
    for (row, [a, b, c]) in export.constraints.into_iter().enumerate() {
        let a = terms(a, export.n_vars)?;
        let b = terms(b, export.n_vars)?;
        let c = terms(c, export.n_vars)?;
        let evaluate = |lc: &[(FieldElement, usize)]| {
            lc.iter().fold(FieldElement::ZERO, |sum, &(coefficient, column)| {
                sum + coefficient * witness[column]
            })
        };
        ensure!(
            evaluate(&a) * evaluate(&b) == evaluate(&c),
            "witness does not satisfy constraint {row}"
        );
        r1cs.add_constraint(&a, &b, &c);
    }
    let public_values = witness[1..=public_count].to_vec();
    Ok(ImportedCircuit {
        r1cs,
        witness,
        public_values,
    })
}

pub fn load(r1cs_path: &Path, witness_path: &Path) -> Result<ImportedCircuit> {
    let export = serde_json::from_reader(BufReader::new(File::open(r1cs_path).context("opening R1CS JSON")?))
        .context("reading R1CS JSON")?;
    let values = serde_json::from_reader(BufReader::new(
        File::open(witness_path).context("opening witness JSON")?,
    ))
    .context("reading witness JSON")?;
    import(export, values)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn square() -> Export {
        serde_json::from_value(serde_json::json!({
            "prime": FieldElement::MODULUS.to_string(),
            "nVars": 3, "nOutputs": 1, "nPubInputs": 1, "nPrvInputs": 0,
            "nConstraints": 1, "constraints": [[{"2": "1"}, {"2": "1"}, {"1": "1"}]]
        }))
        .unwrap()
    }

    fn values(one: &str, y: &str, x: &str) -> Vec<String> {
        [one, y, x].map(str::to_owned).to_vec()
    }

    #[test]
    fn rejects_invalid_assignment_and_constant_wire() {
        assert!(import(square(), values("1", "10", "3")).is_err());
        assert!(import(square(), values("0", "9", "3")).is_err());
        let imported = import(square(), values("1", "9", "3")).unwrap();
        assert_eq!(
            imported.public_values,
            vec![FieldElement::from(9), FieldElement::from(3)]
        );
    }

    #[test]
    fn rejects_field_aliases_and_wrong_modulus() {
        assert!(field(&FieldElement::MODULUS.to_string()).is_err());
        assert!(field("-1").is_err());
        assert!(field("01").is_err());
        let mut export = square();
        export.prime = "17".into();
        assert!(import(export, values("1", "9", "3")).is_err());
    }

    #[test]
    fn rejects_out_of_range_signals_and_wrong_lengths() {
        let mut export = square();
        export.constraints[0][0].insert("3".into(), "1".into());
        assert!(import(export, values("1", "9", "3")).is_err());
        assert!(import(square(), vec!["1".into()]).is_err());
    }
}
