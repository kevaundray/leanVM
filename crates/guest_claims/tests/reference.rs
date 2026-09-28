//! Cross-check the portable verifiers against the repository's concrete schemes.
use leanvm_guest::Field;
use leanvm_guest_claims::{Error, da, sphincs as guest_sphincs, xmss as guest_xmss};
use xmss::Encode;

#[test]
fn xmss_ssz_reference_and_authentication_failures() {
    let seed = core::array::from_fn(|i| i as u8);
    let message = core::array::from_fn(|i| (i * 3 + 7) as u8);
    for epoch in [0, 1234, u32::MAX] {
        let (sk, pk) = xmss::key_gen_from_seed(seed, epoch, epoch).unwrap();
        let signature = xmss::sign(&sk, &message, epoch).unwrap();
        xmss::verify(&pk, &message, &signature, epoch).unwrap();
        let key = pk.as_ssz_bytes();
        let mut bytes = signature.as_ssz_bytes();
        guest_xmss::verify(&key, &message, &bytes, epoch).unwrap();
        assert_eq!(
            guest_xmss::verify(&key, &message, &bytes[..bytes.len() - 1], epoch),
            Err(Error::SignatureLength)
        );
        bytes[guest_xmss::WOTS_SIG_SIZE + 10 * 16 + 3] ^= 1;
        assert_eq!(
            guest_xmss::verify(&key, &message, &bytes, epoch),
            Err(Error::RootMismatch)
        );
    }
}

#[test]
fn sphincs_reference_and_authentication_failures() {
    let message = core::array::from_fn(|i| (i * 5 + 3) as u8);
    let (sk, pk) = sphincs::key_gen_from_seed([7; 32]);
    let signature = sphincs::sign(&sk, &message).unwrap();
    sphincs::verify(&pk, &message, &signature).unwrap();
    guest_sphincs::verify(&pk.flatten(), &message, &signature.to_bytes()).unwrap();
    let mut bad = signature.clone();
    bad.paths[0][0] ^= 1;
    assert_eq!(
        guest_sphincs::verify(&pk.flatten(), &message, &bad.to_bytes()),
        Err(Error::RootMismatch)
    );
    let mut bad = signature.clone();
    bad.fts.secrets[5][0] ^= 1;
    assert!(guest_sphincs::verify(&pk.flatten(), &message, &bad.to_bytes()).is_err());
    assert_eq!(
        guest_sphincs::verify(&pk.flatten()[..31], &message, &signature.to_bytes()),
        Err(Error::PublicKeyLength)
    );
}

#[test]
fn leanda_encoding_commitment_transcript_and_membership_match_reference() {
    // Three rows exercise non-power-of-two padding and both commitment branches.
    let payload: Vec<u64> = (0..3 * da::BLOB_SYMBOLS)
        .map(|i| 0x9E37_79B9_7F4A_7C15u64.wrapping_mul(i as u64 + 1))
        .collect();
    let (reference, witness) = lean_da::commit(&payload);
    let mut row = vec![0; da::CODEWORD_SYMBOLS];
    da::encode_row(&payload[..da::BLOB_SYMBOLS], &mut row).unwrap();
    assert_eq!(row, witness.codewords[..da::CODEWORD_SYMBOLS]);
    let actual = da::commitment(&witness.codewords).unwrap();
    assert_eq!(actual.root, reference.root);
    assert_eq!(actual.root_row, reference.root_row);
    assert_eq!(actual.root_col, reference.root_col);
    let challenges = lean_da::membership_challenges(&reference.root);
    assert_eq!(
        da::membership_challenges(&reference.root).as_slice(),
        challenges.iter().map(|v| Field([v.c0, v.c1, v.c2])).collect::<Vec<_>>()
    );
    let reference_vector = lean_da::membership_vector(&reference.root);
    let vector = da::membership_vector(&reference.root).unwrap();
    assert_eq!(
        vector,
        reference_vector
            .iter()
            .map(|v| Field([v.c0, v.c1, v.c2]))
            .collect::<Vec<_>>()
    );
    let digest = lean_da::vector_digest(&reference_vector);
    assert_eq!(da::vector_digest(&vector).unwrap(), digest);
    da::verify(&witness.codewords, &reference.root, &digest).unwrap();
    let bytes: Vec<u8> = witness.codewords.iter().flat_map(|x| x.to_le_bytes()).collect();
    da::verify_bytes(&bytes, &reference.root, &digest).unwrap();
    let mut wrong_digest = digest;
    wrong_digest[0] ^= 1;
    assert_eq!(
        da::verify(&witness.codewords, &reference.root, &wrong_digest),
        Err(Error::MembershipDigestMismatch)
    );

    // Recommit the corrupted matrix: commitment validation alone cannot catch this.
    let mut corrupted = witness.codewords;
    corrupted[2 * da::CODEWORD_SYMBOLS + da::BLOB_SYMBOLS] ^= 1;
    let invalid = da::commitment(&corrupted).unwrap();
    let invalid_vector = da::membership_vector(&invalid.root).unwrap();
    let invalid_digest = da::vector_digest(&invalid_vector).unwrap();
    assert_eq!(
        da::verify(&corrupted, &invalid.root, &invalid_digest),
        Err(Error::InvalidMembership)
    );
}

#[test]
fn leanda_rejects_malformed_shapes_before_allocating() {
    for input in [&[][..], &[0][..]] {
        assert_eq!(da::verify(input, &[0; 32], &[0; 32]), Err(Error::InvalidShape));
    }
    assert_eq!(da::verify_bytes(&[0; 7], &[0; 32], &[0; 32]), Err(Error::InvalidShape));
    assert_eq!(da::vector_digest(&[Field::ZERO]), Err(Error::InvalidShape));
}
