use anyhow::{ensure, Context, Result};
use ark_ff::{AdditiveGroup, Field};
use provekit_backend_bn254::{spark::SparkQueryBatch, Bn254Field, FieldElement};
use provekit_common::{
    FieldHash, HashConfig, PublicInputs, PublicInputsHash, WhirR1CSScheme, WitnessCommitmentMode, R1CS,
};
use provekit_prover::WhirR1CSProver;
use provekit_spark::{
    preprocess_spark, SparkMatrix, SparkProof, SparkProverContext, SparkProverScheme, SparkVerifierScheme,
};
use provekit_verifier::WhirR1CSVerifier;
use whir::transcript::ProverState;

use crate::import::ImportedCircuit;

const HASH: HashConfig = HashConfig::Sha256;

pub fn run(circuit: ImportedCircuit, self_check: bool) -> Result<()> {
    let ImportedCircuit {
        mut r1cs,
        witness,
        public_values,
    } = circuit;
    let original_constraints = r1cs.num_constraints();
    let original_witnesses = r1cs.num_witnesses();
    println!(
        "Imported Clean R1CS: {original_constraints} constraints, {original_witnesses} witness signals, {} public values (excluding constant)",
        public_values.len()
    );
    ensure!(!public_values.is_empty(), "this example requires a public statement");
    print!("Public statement (constant, outputs, inputs): [1");
    for value in &public_values {
        print!(", {value}");
    }
    println!("]");
    let public_inputs = PublicInputs::from_vec(public_values);

    // SPARK's upstream WHIR row commitment has a 16-element minimum. Its
    // packed matrix has twice as many rows as each R1CS matrix. Add only
    // identically-zero constraints, before hashing/constructing the scheme,
    // so the Spartan query and the SPARK row domain are exactly the same.
    let padded_rows = original_constraints.max(8).next_power_of_two();
    r1cs.grow_matrices(padded_rows, original_witnesses);
    let scheme = WhirR1CSScheme::<Bn254Field>::new_for_r1cs(
        &r1cs,
        witness.len(),
        0,
        Vec::new(),
        true,
        HASH,
        WitnessCommitmentMode::default(),
    )
    .context("constructing Spartan/WHIR scheme")?;
    println!(
        "Proof domains: {} padded constraint rows, {} padded witness slots",
        1usize << scheme.m_0,
        scheme.domain_size()
    );
    println!("Transcript circuit hash: {:?}", scheme.r1cs_hash);

    // Preprocessing derives the trusted verifier setup solely from the loaded
    // circuit, never from a proof, query, or attacker-supplied setup artifact.
    let matrix = spark_matrix(&r1cs, &scheme);
    println!(
        "SPARK packed matrix: {} rows, {} columns, {} padded sparse entries",
        matrix.timestamps.final_row.len(),
        matrix.timestamps.final_col.len(),
        matrix.coo.val.len()
    );
    let (setup, witnesses) = preprocess_spark(&matrix, HASH);
    let spark_scheme = SparkProverScheme {
        whir_configs: setup.whir_configs.clone(),
        matrix_dimensions: setup.matrix_dimensions.clone(),
    };
    let spark_context = SparkProverContext {
        matrix,
        witnesses,
        setup: setup.clone(),
    };

    // The scheme domain separator contains the circuit hash. The instance
    // contains the public-input hash. Upstream's public covector also binds
    // witness[0] = 1 and the following output/input prefix, not just its hash.
    let instance = public_inputs.hash_bytes::<Bn254Field>(HASH);
    let ds = scheme.create_domain_separator().instance(&instance);
    let mut merlin = ProverState::new(&ds, Bn254Field::transcript_sponge(HASH));
    let commitment = scheme
        .commit(
            &mut merlin,
            r1cs.num_witnesses(),
            r1cs.num_constraints(),
            witness.clone(),
            true,
        )
        .context("committing the exported witness")?;
    // Despite the historical method name, this API consumes an R1CS directly;
    // it neither invokes Noir nor synthesizes a replacement circuit/witness.
    let (native_proof, query_data) = scheme
        .prove_noir_with_spark(merlin, r1cs.clone(), vec![commitment], witness, &public_inputs)
        .context("proving Spartan/WHIR and extracting its matrix queries")?;
    scheme
        .verify(&native_proof, &public_inputs, &r1cs)
        .context("native Spartan/WHIR verification")?;
    println!(
        "Native Spartan/WHIR verification: OK ({} transcript bytes, {} hint bytes; full matrices)",
        native_proof.narg_string.len(),
        native_proof.hints.len()
    );

    let batch = SparkQueryBatch::from(query_data);
    ensure!(batch.row.len() == scheme.m_0, "unexpected SPARK row query dimension");
    ensure!(
        batch.queries.len() == 1 && batch.queries[0].col.len() == scheme.m,
        "unexpected SPARK column query dimension for single witness commitment"
    );
    let spark_proof = spark_scheme
        .prove(&spark_context, &batch)
        .context("proving SPARK for the actual Spartan/WHIR queries")?;
    let spark_bytes = spark_proof.0.narg_string.len();
    let spark_hint_bytes = spark_proof.0.hints.len();
    let negative_proof = self_check.then(|| SparkProof(spark_proof.0.clone()));
    SparkVerifierScheme
        .verify(spark_proof, &setup, &batch)
        .context("SPARK verification against circuit-derived setup")?;
    println!(
        "SPARK verification: OK ({} actual query, {spark_bytes} transcript bytes, {spark_hint_bytes} hint bytes)",
        batch.queries.len()
    );
    println!(
        "SPARK is an additional verified matrix-evaluation proof; native verification still uses full matrices. No succinct composition or full zero-knowledge claim."
    );

    if let Some(mut tampered_proof) = negative_proof {
        let mut changed_public = public_inputs.clone();
        changed_public.0[0] += FieldElement::ONE;
        ensure!(
            scheme.verify(&native_proof, &changed_public, &r1cs).is_err(),
            "self-check failed: native verifier accepted a changed public output"
        );
        println!("Self-check: native verifier rejected changed public output");

        let mut changed_batch = batch.clone();
        changed_batch.queries[0].claimed_a += FieldElement::ONE;
        ensure!(
            SparkVerifierScheme
                .verify(SparkProof(tampered_proof.0.clone()), &setup, &changed_batch)
                .is_err(),
            "self-check failed: SPARK verifier accepted a changed query"
        );
        println!("Self-check: SPARK verifier rejected changed query");

        let first_byte = tampered_proof
            .0
            .narg_string
            .first_mut()
            .context("SPARK transcript unexpectedly empty")?;
        *first_byte ^= 1;
        ensure!(
            SparkVerifierScheme.verify(tampered_proof, &setup, &batch).is_err(),
            "self-check failed: SPARK verifier accepted a tampered proof"
        );
        println!("Self-check: SPARK verifier rejected tampered proof");
    }
    Ok(())
}

fn spark_matrix(r1cs: &R1CS<FieldElement>, scheme: &WhirR1CSScheme<Bn254Field>) -> SparkMatrix {
    let row_count = 1usize << scheme.m_0;
    let col_count = scheme.domain_size();
    let entries = r1cs.a().iter().count() + r1cs.b().iter().count() + r1cs.c().iter().count();
    // Match upstream prepare's Z = [[A, B], [0, C]] layout. The COO domain
    // also has a 16-element WHIR minimum; padding contributes only zero values.
    let padded_entries = entries.max(16).next_power_of_two();
    let mut rows = Vec::with_capacity(padded_entries);
    let mut cols = Vec::with_capacity(padded_entries);
    let mut values = Vec::with_capacity(padded_entries);
    for (matrix, row_offset, col_offset) in [
        (r1cs.a(), 0, 0),
        (r1cs.b(), 0, col_count),
        (r1cs.c(), row_count, col_count),
    ] {
        for ((row, col), value) in matrix.iter() {
            rows.push(row + row_offset);
            cols.push(col + col_offset);
            values.push(value);
        }
    }
    rows.resize(padded_entries, 0);
    cols.resize(padded_entries, 0);
    values.resize(padded_entries, FieldElement::ZERO);
    SparkMatrix::new(rows, cols, values, 2 * row_count, 2 * col_count)
}
