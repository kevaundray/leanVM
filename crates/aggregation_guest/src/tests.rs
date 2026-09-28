use super::*;
use alloc::vec;

fn group(epoch: u32, message: u8, keys: &[u8]) -> XmssGroup {
    XmssGroup {
        epoch,
        message: [message; 32],
        keys: keys.iter().map(|key| [*key; 32]).collect(),
    }
}
fn statement() -> Statement {
    Statement {
        xmss: vec![group(3, 9, &[1, 2])],
        sphincs: vec![SphincsClaim {
            key: [1; 32],
            message: [9; 32],
        }],
        da_roots: vec![[4; 32]],
    }
}
fn coverage(statement: &Statement) -> Coverage<'_> {
    let mut coverage = Coverage::default();
    coverage.statement(statement).unwrap();
    coverage
}

#[test]
fn narrowed_claims_need_exact_scheme_epoch_message_and_key() {
    let available = statement();
    let narrowed = Statement {
        xmss: vec![group(3, 9, &[2])],
        ..Statement::default()
    };
    coverage(&available).check(&narrowed).unwrap();
    for bad in [group(4, 9, &[2]), group(3, 8, &[2]), group(3, 9, &[3])] {
        let declared = Statement {
            xmss: vec![bad],
            ..Statement::default()
        };
        assert!(matches!(coverage(&available).check(&declared), Err(Error::NotCovered)));
    }
    let xmss_only = Statement {
        xmss: vec![group(3, 9, &[1])],
        ..Statement::default()
    };
    let sphincs_only = Statement {
        sphincs: vec![SphincsClaim {
            key: [1; 32],
            message: [9; 32],
        }],
        ..Statement::default()
    };
    assert!(matches!(
        coverage(&xmss_only).check(&sphincs_only),
        Err(Error::NotCovered)
    ));
    assert!(matches!(
        coverage(&sphincs_only).check(&xmss_only),
        Err(Error::NotCovered)
    ));
}

#[test]
fn ordered_coverage_merges_disjoint_children_and_rejects_gaps() {
    let mut input = Input {
        statement: Statement {
            xmss: vec![group(3, 9, &[2, 4])],
            ..Statement::default()
        },
        children: vec![
            Child {
                statement: Statement {
                    xmss: vec![group(3, 9, &[1, 2])],
                    ..Statement::default()
                },
                key: [7; 32],
                height: 0,
            },
            Child {
                statement: Statement {
                    xmss: vec![group(3, 9, &[3, 4])],
                    ..Statement::default()
                },
                key: [7; 32],
                height: 0,
            },
        ],
        ..Input::default()
    };
    verify_input(&input, public_input(&input.statement, &input.children).unwrap()).unwrap();
    input.statement.xmss[0].keys.push([5; 32]);
    assert!(matches!(
        verify_input(&input, public_input(&input.statement, &input.children).unwrap()),
        Err(Error::NotCovered)
    ));
}

#[test]
fn omitted_epoch_conflicts_are_still_rejected() {
    let declared = Statement {
        da_roots: vec![[4; 32]],
        ..Statement::default()
    };
    let original = statement();
    let mut available = coverage(&original);
    available.xmss.push(XmssSupport {
        epoch: 3,
        message: &[8; 32],
        keys: &[[7; 32]],
    });
    assert!(matches!(available.check(&declared), Err(Error::ConflictingMessages)));
}

#[test]
fn duplicate_verified_contributions_do_not_change_coverage() {
    let available = statement();
    let mut covered = coverage(&available);
    covered.statement(&available).unwrap();
    covered.check(&available).unwrap();
    let mut missing_root = available.clone();
    missing_root.da_roots[0] = [5; 32];
    assert!(matches!(
        coverage(&available).check(&missing_root),
        Err(Error::NotCovered)
    ));
}

#[test]
fn narrowed_roots_allow_a_larger_verified_union() {
    let declared = Statement {
        da_roots: vec![[0; 32]],
        ..Statement::default()
    };
    let roots: Vec<_> = (0..=MAX_DA_ROOTS).map(|i| [i as u8; 32]).collect();
    let available = Coverage {
        roots: roots.iter().collect(),
        ..Coverage::default()
    };
    declared.validate().unwrap();
    available.check(&declared).unwrap();
}

#[test]
fn canonical_statement_rejects_duplicates_and_empty_groups() {
    let valid = statement();
    let mut duplicate_epoch = valid.clone();
    duplicate_epoch.xmss.push(duplicate_epoch.xmss[0].clone());
    let mut duplicate_key = valid.clone();
    duplicate_key.xmss[0].keys[1] = duplicate_key.xmss[0].keys[0];
    let mut duplicate_pair = valid.clone();
    duplicate_pair.sphincs.push(duplicate_pair.sphincs[0]);
    let mut duplicate_root = valid.clone();
    duplicate_root.da_roots.push(duplicate_root.da_roots[0]);
    let mut empty_group = valid.clone();
    empty_group.xmss[0].keys.clear();
    for invalid in [
        duplicate_epoch,
        duplicate_key,
        duplicate_pair,
        duplicate_root,
        empty_group,
    ] {
        assert!(matches!(invalid.validate(), Err(Error::NonCanonicalStatement)));
    }
    assert!(matches!(Statement::default().validate(), Err(Error::EmptyStatement)));
}

#[test]
fn statement_hash_binds_canonical_claims() {
    let original = statement();
    let mut narrowed = original.clone();
    narrowed.xmss[0].keys.pop();
    assert_ne!(original.digest().unwrap(), narrowed.digest().unwrap());
    let encoding = original.to_bytes().unwrap();
    assert_eq!(Statement::from_bytes(&encoding).unwrap(), original);
    let mut trailing = encoding;
    trailing.push(0);
    assert!(matches!(Statement::from_bytes(&trailing), Err(Error::TrailingBytes)));
}

#[test]
fn decoder_rejects_oversized_or_truncated_lengths_before_allocation() {
    assert!(matches!(
        Statement::from_bytes(&u32::MAX.to_le_bytes()),
        Err(Error::TooLarge)
    ));
    assert!(matches!(
        Statement::from_bytes(&1u32.to_le_bytes()),
        Err(Error::Truncated)
    ));
    let mut payload = INPUT_MAGIC.to_vec();
    payload.extend_from_slice(&u32::MAX.to_le_bytes());
    assert!(matches!(Input::from_bytes(&payload), Err(Error::TooLarge)));
}

#[test]
fn wire_framing_and_optional_tag_are_unambiguous() {
    // Dummy cryptographic bytes exercise only the codec, never proof acceptance.
    let input = Input {
        statement: statement(),
        children: vec![Child {
            statement: statement(),
            key: [7; 32],
            height: 3,
        }],
        xmss: vec![RawXmss {
            epoch: 3,
            message: [9; 32],
            key: [1; 32],
            signature: vec![0; XMSS_SIGNATURE_BYTES],
        }],
        ..Input::default()
    };
    let payload = input.to_bytes().unwrap();
    assert_eq!(Input::from_bytes(&payload).unwrap(), input);
    let mut old_version = payload.clone();
    old_version[..8].copy_from_slice(b"RVAGG001");
    assert!(matches!(Input::from_bytes(&old_version), Err(Error::InvalidEncoding)));
    let framed = input.to_witness().unwrap();
    assert_eq!(
        u64::from_le_bytes(framed[..8].try_into().unwrap()) as usize,
        payload.len()
    );
    assert_eq!(&framed[8..], payload);
    let mut bad_tag = payload.clone();
    let n = bad_tag.len();
    bad_tag[n - 4..].copy_from_slice(&2u32.to_le_bytes());
    assert!(matches!(Input::from_bytes(&bad_tag), Err(Error::InvalidEncoding)));
    let mut trailing = payload;
    trailing.push(0);
    assert!(matches!(Input::from_bytes(&trailing), Err(Error::TrailingBytes)));
}

#[test]
fn duplicate_and_unpublished_slots_count_towards_exclusive_limit() {
    let mut input = Input {
        statement: statement(),
        children: vec![Child {
            statement: Statement {
                sphincs: (0..(MAX_KEYS / 2))
                    .map(|i| {
                        let mut key = [0; 32];
                        key[..4].copy_from_slice(&(i as u32).to_be_bytes());
                        SphincsClaim { key, message: [9; 32] }
                    })
                    .collect(),
                ..Statement::default()
            },
            key: [7; 32],
            height: 0,
        }],
        ..Input::default()
    };
    input.validate_shape().unwrap();
    input.children.push(input.children[0].clone());
    assert!(matches!(input.validate_shape(), Err(Error::TooLarge)));
}

#[test]
fn epoch_and_internal_root_caps_are_inclusive() {
    let epochs = Statement {
        xmss: (0..MAX_EPOCHS).map(|epoch| group(epoch as u32, 9, &[1])).collect(),
        ..Statement::default()
    };
    epochs.validate().unwrap();
    let roots = Statement {
        da_roots: (0..MAX_STATEMENT_DA_ROOTS)
            .map(|i| {
                let mut root = [0; 32];
                root[..4].copy_from_slice(&(i as u32).to_be_bytes());
                root
            })
            .collect(),
        ..Statement::default()
    };
    roots.validate().unwrap();
    assert_eq!(Statement::from_bytes(&roots.to_bytes().unwrap()).unwrap(), roots);
    let mut too_many = roots;
    too_many.da_roots.push([255; 32]);
    assert!(matches!(too_many.validate(), Err(Error::TooLarge)));
}

#[test]
fn execution_binds_every_child_even_when_its_claims_are_omitted() {
    let declared = Statement {
        da_roots: vec![[4; 32]],
        ..Statement::default()
    };
    let input = Input {
        statement: declared.clone(),
        children: vec![
            Child {
                statement: declared,
                key: [7; 32],
                height: 0,
            },
            Child {
                statement: statement(),
                key: [7; 32],
                height: 2,
            },
        ],
        ..Input::default()
    };
    let public = public_input(&input.statement, &input.children).unwrap();
    // Only execution checks succeed here; child proof validity is native recursion's job.
    verify_input(&input, public).unwrap();
    let mutations: &[fn(&mut Input)] = &[
        |input| input.children[1].key[0] ^= 1,
        |input| input.children[1].height += 1,
        |input| input.children[1].statement.xmss[0].message[0] ^= 1,
        |input| input.children.swap(0, 1),
        |input| {
            input.children.pop();
        },
        |input| input.children[1] = input.children[0].clone(),
    ];
    for mutate in mutations {
        let mut changed = input.clone();
        mutate(&mut changed);
        assert!(matches!(
            verify_input(&changed, public),
            Err(Error::PublicInputMismatch)
        ));
    }
    let mut uncovered = input;
    uncovered.statement.da_roots[0] = [5; 32];
    let public = public_input(&uncovered.statement, &uncovered.children).unwrap();
    assert!(matches!(verify_input(&uncovered, public), Err(Error::NotCovered)));
}

#[test]
fn internal_fan_in_is_bounded_before_child_decoding() {
    let child = Child {
        statement: statement(),
        key: [7; 32],
        height: 0,
    };
    let mut input = Input {
        statement: statement(),
        children: vec![child; deferred::MAX_CHILDREN],
        ..Input::default()
    };
    let mut payload = input.to_bytes().unwrap();
    assert_eq!(Input::from_bytes(&payload).unwrap(), input);
    input.children.push(input.children[0].clone());
    assert!(matches!(input.to_bytes(), Err(Error::TooLarge)));
    assert!(matches!(
        public_input(&input.statement, &input.children),
        Err(Error::TooLarge)
    ));
    let offset = INPUT_MAGIC.len() + input.statement.to_bytes().unwrap().len();
    payload.truncate(offset);
    payload.extend_from_slice(&((deferred::MAX_CHILDREN + 1) as u32).to_le_bytes());
    assert!(matches!(Input::from_bytes(&payload), Err(Error::TooLarge)));
}

#[test]
fn bound_child_coverage_does_not_skip_invalid_raw_claims() {
    let input = Input {
        statement: statement(),
        children: vec![Child {
            statement: statement(),
            key: [7; 32],
            height: 0,
        }],
        ..Input::default()
    };
    let public = public_input(&input.statement, &input.children).unwrap();
    // Each raw contribution is already covered or unpublished; neither excuses verification.
    let mut bad_xmss = input.clone();
    bad_xmss.xmss.push(RawXmss {
        epoch: 3,
        message: [9; 32],
        key: [1; 32],
        signature: vec![0; XMSS_SIGNATURE_BYTES],
    });
    assert!(matches!(verify_input(&bad_xmss, public), Err(Error::Claims(_))));
    let mut bad_sphincs = input.clone();
    bad_sphincs.sphincs.push(RawSphincs {
        message: [9; 32],
        key: [2; 32],
        signature: vec![0; SPHINCS_SIGNATURE_BYTES],
    });
    assert!(matches!(verify_input(&bad_sphincs, public), Err(Error::Claims(_))));
    let mut bad_da = input;
    bad_da.da = Some(DirectDa {
        root: [5; 32],
        membership_digest: [0; 32],
        codewords_le: vec![0; DA_ROW_BYTES],
    });
    assert!(matches!(verify_input(&bad_da, public), Err(Error::Claims(_))));
}
