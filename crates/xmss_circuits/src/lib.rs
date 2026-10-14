//! XMSS signature aggregation as a dedicated leanVM program, `guests/xmss_node.py`, proven and verified
//! through the VM's exposed entry points: `lean_compiler::compile`, `leanvm_core::cpu::prove` and the
//! `verifier` crate, none of them changed.
//!
//! A node verifies raw XMSS signatures grouped by `(leaf_index, message)` and merges the signer sets of up
//! to [`MAX_RECURSIONS`] children, with the semantics of `rec_aggregation::aggregation`: the published set
//! is the sorted deduplicated union by default or any declared subset of it, and every declared claim is
//! covered by a raw signature verified at its own `(leaf_index, message)` or by a child's claim of the
//! same group. A leaf's statement is the signer-set digest itself, byte-identical to `rec_aggregation`'s
//! `signers_hash` of an XMSS-only set ([`signers_hash`]); a merge binds its own set digest and each
//! child's ([`XmssAggregate::statement`]).
//!
//! The VM does not verify a child's proof: the recursion guest verifies proofs of its own bytecode only.
//! An [`XmssAggregate`] therefore carries its children, and [`XmssAggregate::verify`] checks every proof
//! of the tree natively.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::LazyLock;

use lean_compiler::{compile, parse_with_replacements};
use leanvm_core::cpu::{Program, Proof, ProveError, Stats, from_scalar, prove, scalar_proof};
use primitives::field::{F192, G, g_pow};
pub use rec_aggregation::{MAX_KEYS, MAX_LEAF_INDICES, MAX_RECURSIONS, XmssClaimGroup};
use xmss::{LeafIndex, Message, XmssPublicKey, XmssSignature};

/// Blocks the program absorbs per loop frame when it hashes a list; the window split is a hint.
const SIGNERS_WINDOW: usize = 32;
const _: () = assert!(SIGNERS_WINDOW.is_power_of_two());
const SIGNERS_MAX_WINDOWS: usize = MAX_KEYS / SIGNERS_WINDOW;
const _: () = assert!((MAX_KEYS - 1) / SIGNERS_WINDOW < SIGNERS_MAX_WINDOWS);
const _: () = assert!((2 * MAX_LEAF_INDICES + 1) / SIGNERS_WINDOW < SIGNERS_MAX_WINDOWS);
const SIGNERS_COUNT_BITS: u32 = MAX_KEYS.ilog2();
const _: () = assert!(MAX_KEYS.is_power_of_two() && 2 * MAX_LEAF_INDICES + 2 < 1 << SIGNERS_COUNT_BITS);
const _: () = assert!(SIGNERS_COUNT_BITS + 6 + SIGNERS_WINDOW.ilog2() <= 64);
const _: () = assert!(MAX_KEYS <= 1 << leanvm_core::cpu::MIN_LOG_MEM);
const _: () = assert!(xmss::LOG_LIFETIME <= 32 && (2 + xmss::V).is_multiple_of(4));

/// One raw signature: the signer's key, the leaf index and message it signed, and the signature.
pub type RawSignature = (XmssPublicKey, LeafIndex, Message, XmssSignature);

/// A proof that every claim of [`Self::signers`] is covered by a valid XMSS signature, directly or through
/// one of [`Self::children`].
#[derive(Clone, Debug)]
pub struct XmssAggregate {
    signers: Vec<XmssClaimGroup>,
    children: Vec<XmssAggregate>,
    proof: Proof,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyError {
    /// A signer set is not strictly sorted by `(leaf_index, message)` and key, has an empty group, or is
    /// too large.
    MalformedSignerSet,
    /// More than [`MAX_RECURSIONS`] children.
    TooManyChildren,
    /// A proof of the tree did not verify.
    Snark(verifier::VerifierError),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AggregationError {
    /// More than [`MAX_LEAF_INDICES`] `(leaf_index, message)` groups.
    TooManyLeafIndices,
    /// More than [`MAX_RECURSIONS`] children, or [`MAX_KEYS`] coverage slots or more.
    TooLarge,
    /// A child's signer set is malformed.
    InvalidChild(VerifyError),
    /// Nothing to publish.
    Empty,
    /// A declared claim is covered by neither a raw signature nor a child.
    NotCovered,
    /// A raw signature's randomness does not give a target-sum encoding.
    MalformedRawSignature,
    /// `log_inv_rate` is outside what the PCS accepts.
    InvalidRate { log_inv_rate: usize },
    /// The program rejects its input (an invalid signature) or the prover failed.
    ProofError(ProveError),
}

impl std::fmt::Display for VerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MalformedSignerSet => write!(f, "malformed signer set"),
            Self::TooManyChildren => write!(f, "more than {MAX_RECURSIONS} children"),
            Self::Snark(e) => write!(f, "the snark did not verify: {e}"),
        }
    }
}

impl std::error::Error for VerifyError {}

impl std::fmt::Display for AggregationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TooManyLeafIndices => write!(f, "more than {MAX_LEAF_INDICES} XMSS groups"),
            Self::TooLarge => write!(f, "too many children or signature claims"),
            Self::InvalidChild(e) => write!(f, "invalid child aggregate: {e}"),
            Self::Empty => write!(f, "no signature claims to publish"),
            Self::NotCovered => write!(f, "a declared claim is not covered by the children and raw signatures"),
            Self::MalformedRawSignature => write!(f, "a raw signature does not decode to a target-sum encoding"),
            Self::InvalidRate { log_inv_rate } => write!(f, "invalid log_inv_rate {log_inv_rate}"),
            Self::ProofError(e) => write!(f, "proving failed: {e}"),
        }
    }
}

impl std::error::Error for AggregationError {}

impl XmssAggregate {
    /// A received aggregate, as its parts. Nothing is checked until [`Self::verify`].
    pub fn new(signers: Vec<XmssClaimGroup>, children: Vec<XmssAggregate>, proof: Proof) -> Self {
        Self {
            signers,
            children,
            proof,
        }
    }

    pub fn into_parts(self) -> (Vec<XmssClaimGroup>, Vec<XmssAggregate>, Proof) {
        (self.signers, self.children, self.proof)
    }

    /// The published claims: strictly increasing `(leaf_index, message)` groups of strictly sorted keys.
    pub fn signers(&self) -> &[XmssClaimGroup] {
        &self.signers
    }

    pub fn children(&self) -> &[XmssAggregate] {
        &self.children
    }

    pub fn proof(&self) -> &Proof {
        &self.proof
    }

    /// Every proof of the tree, this node's first.
    pub fn proofs(&self) -> Vec<&Proof> {
        let mut out = vec![&self.proof];
        for child in &self.children {
            out.extend(child.proofs());
        }
        out
    }

    /// What this node's proof publishes: [`signers_hash`] for a leaf, and for a merge the BLAKE2s of
    /// `[count(k), 0, set digest]` followed by one `[child set digest, 0, 0]` block per child.
    pub fn statement(&self) -> [u8; 32] {
        let children: Vec<[u8; 32]> = self.children.iter().map(|child| signers_hash(&child.signers)).collect();
        node_statement(signers_hash(&self.signers), &children)
    }

    /// Check every proof of the tree against the signer sets it carries.
    pub fn verify(&self) -> Result<(), VerifyError> {
        check_signer_set(&self.signers)?;
        if self.children.len() > MAX_RECURSIONS {
            return Err(VerifyError::TooManyChildren);
        }
        for child in &self.children {
            child.verify()?;
        }
        verifier::verify_execution(&BYTECODE, &self.statement(), &scalar_proof(&self.proof))
            .map_err(VerifyError::Snark)?;
        Ok(())
    }
}

static PROGRAM: LazyLock<Program> = LazyLock::new(|| {
    compile(
        &parse_with_replacements(include_str!("../guests/xmss_node.py"), &placeholders())
            .expect("the XMSS node program must parse"),
    )
});

static BYTECODE: LazyLock<verifier::Bytecode> = LazyLock::new(|| {
    let table: Vec<u64> = leanvm_core::cpu::bytecode_table(&PROGRAM.prog)
        .iter()
        .map(|word| word.0)
        .collect();
    verifier::Bytecode::new(&table)
});

/// The node program, compiled on first use.
pub fn program() -> &'static Program {
    &PROGRAM
}

/// Compile the program and prepare its verifier bytecode now rather than inside the first proof or check.
pub fn warm_up() {
    LazyLock::force(&BYTECODE);
}

/// A count in the exponent, `g^n`, as the program carries it.
fn count(n: usize) -> F192 {
    F192::new(g_pow(n).0, 0, 0)
}

/// A count as `rec_aggregation`'s statement writes it.
fn scalar_count(n: usize) -> F192 {
    from_scalar(verifier::gpow(n as u64))
}

fn dsl_u128(value: F192) -> u128 {
    assert_eq!(value.c2, 0, "u128 DSL literal cannot encode the top F192 limb");
    (value.c0 as u128) | ((value.c1 as u128) << 64)
}

fn f192_literal(f: F192) -> String {
    format!("f192({},{},{})", f.c0, f.c1, f.c2)
}

fn pack_hash_state(hash: &[u8; 32]) -> [F192; 2] {
    [pack_16_bytes(&hash[..16]), pack_16_bytes(&hash[16..])]
}

fn pack_16_bytes(bytes: &[u8]) -> F192 {
    let word_at = |offset: usize| u64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap());
    F192::new(word_at(0), word_at(8), 0)
}

fn key_cells(pk: &XmssPublicKey) -> [F192; 2] {
    [pack_16_bytes(&pk.merkle_root), pack_16_bytes(&pk.public_param)]
}

fn cell_bytes(cells: impl IntoIterator<Item = F192>) -> Vec<u8> {
    let mut bytes = Vec::new();
    for cell in cells {
        bytes.extend_from_slice(&cell.c0.to_le_bytes());
        bytes.extend_from_slice(&cell.c1.to_le_bytes());
    }
    bytes
}

fn tweak_cell(tweak_type: u8, sub_position: u32) -> F192 {
    pack_16_bytes(&xmss::make_tweak(tweak_type, sub_position, 0))
}

fn tweak_index_weight(b: usize) -> F192 {
    pack_16_bytes(&xmss::make_tweak(0, 0, 1 << b)) + pack_16_bytes(&xmss::make_tweak(0, 0, 0))
}

fn empty_sphincs_digest() -> [F192; 2] {
    pack_hash_state(&primitives::hash::hash(&[]))
}

/// The signer-set digest of `rec_aggregation::aggregation` for a set with no SPHINCS claims: BLAKE2s of
/// `[count(groups), count(0), digest of the empty SPHINCS list]`, then per group `[leaf_index, count(keys),
/// message]` and `[digest of its keys, 0, 0]`, a key list's digest being BLAKE2s of its 32-byte keys.
pub fn signers_hash(groups: &[XmssClaimGroup]) -> [u8; 32] {
    let sphincs = empty_sphincs_digest();
    let mut cells = vec![scalar_count(groups.len()), scalar_count(0), sphincs[0], sphincs[1]];
    for group in groups {
        cells.extend([
            F192::new(u64::from(group.leaf_index), 0, 0),
            scalar_count(group.keys.len()),
            pack_16_bytes(&group.message[..16]),
            pack_16_bytes(&group.message[16..]),
        ]);
        let keys = pack_hash_state(&primitives::hash::hash(&cell_bytes(
            group.keys.iter().flat_map(key_cells),
        )));
        cells.extend([keys[0], keys[1], F192::ZERO, F192::ZERO]);
    }
    primitives::hash::hash(&cell_bytes(cells))
}

fn node_statement(set: [u8; 32], children: &[[u8; 32]]) -> [u8; 32] {
    if children.is_empty() {
        return set;
    }
    let own = pack_hash_state(&set);
    let mut cells = vec![count(children.len()), F192::ZERO, own[0], own[1]];
    for child in children {
        let digest = pack_hash_state(child);
        cells.extend([digest[0], digest[1], F192::ZERO, F192::ZERO]);
    }
    primitives::hash::hash(&cell_bytes(cells))
}

/// The same rule as `rec_aggregation`'s `check_signer_set` with no SPHINCS claims.
fn check_signer_set(groups: &[XmssClaimGroup]) -> Result<(), VerifyError> {
    let total: usize = groups.iter().map(|group| group.keys.len()).sum();
    if total >= MAX_KEYS
        || groups.len() > MAX_LEAF_INDICES
        || !groups
            .windows(2)
            .all(|w| (w[0].leaf_index, w[0].message) < (w[1].leaf_index, w[1].message))
        || groups
            .iter()
            .any(|group| group.keys.is_empty() || !group.keys.windows(2).all(|w| w[0] < w[1]))
    {
        return Err(VerifyError::MalformedSignerSet);
    }
    Ok(())
}

fn signers_split(blocks: usize) -> Vec<F192> {
    assert!(blocks > 0, "an empty list has no window split");
    let leading = blocks - 1;
    vec![count(leading / SIGNERS_WINDOW), count(leading % SIGNERS_WINDOW)]
}

fn placeholders() -> BTreeMap<String, String> {
    let flds = |v: &[F192]| {
        let items: Vec<String> = v.iter().map(|&x| f192_literal(x)).collect();
        format!("[{}]", items.join(", "))
    };
    let mut rep = BTreeMap::new();
    let mut ps = |k: &str, v: String| {
        rep.insert(format!("{k}_PLACEHOLDER"), v);
    };
    ps("INV_GEN", dsl_u128(F192::new(G.inv().0, 0, 0)).to_string());
    ps("Y_TOWER", dsl_u128(F192::new(0, 1, 0)).to_string());
    let coord_basis: Vec<F192> = (0..64).map(|i| F192::new(1u64 << i, 0, 0)).collect();
    ps("COORD_BASIS", flds(&coord_basis));
    ps("SIGNERS_WINDOW", SIGNERS_WINDOW.to_string());
    ps("SIGNERS_WINDOW_LOG", SIGNERS_WINDOW.ilog2().to_string());
    ps("SIGNERS_MAX_WINDOWS", SIGNERS_MAX_WINDOWS.to_string());
    ps("SIGNERS_COUNT_BITS", SIGNERS_COUNT_BITS.to_string());
    ps(
        "BLAKE2S_IV_0",
        dsl_u128(leanvm_core::hash_flock::IV_CELLS[0]).to_string(),
    );
    ps(
        "BLAKE2S_IV_1",
        dsl_u128(leanvm_core::hash_flock::IV_CELLS[1]).to_string(),
    );
    let md_final = leanvm_core::hash_flock::metadata(0, leanvm_core::hash_flock::FINAL_FLAG, 0);
    ps("MD_FINAL", dsl_u128(md_final).to_string());
    let [sp_0, sp_1] = empty_sphincs_digest();
    ps("SP_EMPTY_0", dsl_u128(sp_0).to_string());
    ps("SP_EMPTY_1", dsl_u128(sp_1).to_string());
    ps("V", xmss::V.to_string());
    ps("W", xmss::W.to_string());
    ps("TARGET_SUM", xmss::TARGET_SUM.to_string());
    ps("LOG_LIFETIME", xmss::LOG_LIFETIME.to_string());
    ps(
        "XM_ENC_TWEAK",
        dsl_u128(tweak_cell(xmss::TWEAK_TYPE_ENCODING, 0)).to_string(),
    );
    ps(
        "XM_PK_TWEAK",
        dsl_u128(tweak_cell(xmss::TWEAK_TYPE_WOTS_PK, 0)).to_string(),
    );
    let chain_tweaks: Vec<F192> = (0..xmss::V)
        .flat_map(|i| {
            (0..xmss::CHAIN_LENGTH - 1)
                .map(move |s| tweak_cell(xmss::TWEAK_TYPE_CHAIN, (i * xmss::CHAIN_LENGTH + s) as u32))
        })
        .collect();
    ps("XM_CHAIN_TWEAKS", flds(&chain_tweaks));
    let merkle_tweaks: Vec<F192> = (0..xmss::LOG_LIFETIME)
        .map(|level| tweak_cell(xmss::TWEAK_TYPE_MERKLE, (level + 1) as u32))
        .collect();
    ps("XM_MERKLE_TWEAKS", flds(&merkle_tweaks));
    let index_weights: Vec<F192> = (0..xmss::LOG_LIFETIME).map(tweak_index_weight).collect();
    ps("XM_INDEX_WEIGHT", flds(&index_weights));
    ps("MAX_KEYS", MAX_KEYS.to_string());
    ps("MAX_RECURSIONS", MAX_RECURSIONS.to_string());
    ps("MAX_LEAF_INDICES", MAX_LEAF_INDICES.to_string());
    rep
}

/// Every coverage slot the node's walk writes, as `rec_aggregation`'s `plan_coverage` lays it out with
/// no SPHINCS region: one region per group, declared groups first, each its keys then its duplicates.
struct Coverage {
    groups: Vec<XmssClaimGroup>,
    n_declared: usize,
    dups: Vec<Vec<XmssPublicKey>>,
    /// Each raw signature's offset within its group's region, indexed as the sorted raw list.
    raw: Vec<usize>,
    /// Raw signatures in the walk's order: group by group, as the table orders them.
    raw_walk: Vec<usize>,
    /// Per child, per child group: the node group it maps to and each key's offset in that region.
    children: Vec<Vec<(usize, Vec<usize>)>>,
}

impl Coverage {
    fn n_total(&self) -> usize {
        self.groups.iter().map(|group| group.keys.len()).sum::<usize>() + self.dups.iter().map(Vec::len).sum::<usize>()
    }
}

/// A claim takes its declared slot once; later or undeclared occurrences take fresh duplicate slots.
fn take_slot(
    claims: &[XmssPublicKey],
    claimed: &mut [bool],
    duplicates: &mut Vec<XmssPublicKey>,
    claim: &XmssPublicKey,
) -> usize {
    match claims.binary_search(claim) {
        Ok(pos) if !claimed[pos] => {
            claimed[pos] = true;
            pos
        }
        _ => {
            duplicates.push(claim.clone());
            claims.len() + duplicates.len() - 1
        }
    }
}

fn plan_coverage(
    raw: &[(XmssPublicKey, LeafIndex, Message)],
    children: &[XmssAggregate],
    declare: Option<&[XmssClaimGroup]>,
) -> Result<Coverage, AggregationError> {
    let mut claims: Vec<(LeafIndex, Message, XmssPublicKey)> = raw
        .iter()
        .map(|(pk, leaf_index, message)| (*leaf_index, *message, pk.clone()))
        .collect();
    for child in children {
        for group in &child.signers {
            claims.extend(
                group
                    .keys
                    .iter()
                    .map(|pk| (group.leaf_index, group.message, pk.clone())),
            );
        }
    }
    claims.sort();
    claims.dedup();
    let mut union: Vec<XmssClaimGroup> = Vec::new();
    for (leaf_index, message, pk) in claims {
        match union.last_mut() {
            Some(group) if (group.leaf_index, group.message) == (leaf_index, message) => group.keys.push(pk),
            _ => union.push(XmssClaimGroup {
                leaf_index,
                message,
                keys: vec![pk],
            }),
        }
    }
    let mut wanted: BTreeSet<(LeafIndex, Message, XmssPublicKey)> = BTreeSet::new();
    for group in declare.unwrap_or_default() {
        wanted.extend(
            group
                .keys
                .iter()
                .map(|key| (group.leaf_index, group.message, key.clone())),
        );
    }
    let mut groups: Vec<XmssClaimGroup> = Vec::new();
    let mut covered_only: Vec<XmssClaimGroup> = Vec::new();
    for mut group in union {
        group
            .keys
            .retain(|key| declare.is_none() || wanted.remove(&(group.leaf_index, group.message, key.clone())));
        if group.keys.is_empty() {
            covered_only.push(group);
        } else {
            groups.push(group);
        }
    }
    if !wanted.is_empty() {
        return Err(AggregationError::NotCovered);
    }
    let n_declared = groups.len();
    if n_declared == 0 {
        return Err(AggregationError::Empty);
    }
    groups.append(&mut covered_only);
    if groups.len() > MAX_LEAF_INDICES {
        return Err(AggregationError::TooManyLeafIndices);
    }
    let region_of: BTreeMap<(LeafIndex, Message), usize> = groups
        .iter()
        .enumerate()
        .map(|(j, group)| ((group.leaf_index, group.message), j))
        .collect();
    let mut claimed: Vec<Vec<bool>> = groups.iter().map(|group| vec![false; group.keys.len()]).collect();
    let mut dups: Vec<Vec<XmssPublicKey>> = vec![Vec::new(); groups.len()];
    let raw_slots: Vec<usize> = raw
        .iter()
        .map(|(pk, leaf_index, message)| {
            let g = region_of[&(*leaf_index, *message)];
            take_slot(&groups[g].keys, &mut claimed[g], &mut dups[g], pk)
        })
        .collect();
    let child_slots = children
        .iter()
        .map(|child| {
            child
                .signers
                .iter()
                .map(|group| {
                    let g = region_of[&(group.leaf_index, group.message)];
                    let offsets = group
                        .keys
                        .iter()
                        .map(|pk| take_slot(&groups[g].keys, &mut claimed[g], &mut dups[g], pk))
                        .collect();
                    (g, offsets)
                })
                .collect()
        })
        .collect();
    let mut raw_walk: Vec<usize> = (0..raw.len()).collect();
    raw_walk.sort_by_key(|&i| region_of[&(raw[i].1, raw[i].2)]);
    let cover = Coverage {
        groups,
        n_declared,
        dups,
        raw: raw_slots,
        raw_walk,
        children: child_slots,
    };
    if cover.n_total() >= MAX_KEYS {
        return Err(AggregationError::TooLarge);
    }
    Ok(cover)
}

#[derive(Default)]
struct Hints(BTreeMap<&'static str, Vec<Vec<F192>>>);

impl Hints {
    fn push(&mut self, name: &'static str, entry: Vec<F192>) {
        self.0.entry(name).or_default().push(entry);
    }
}

fn push_signature_hints(
    hints: &mut Hints,
    pk: &XmssPublicKey,
    sig: &XmssSignature,
    message: &Message,
    leaf_index: LeafIndex,
) -> Result<(), AggregationError> {
    let wots = &sig.wots_signature;
    let encoding = xmss::wots_encode(message, leaf_index, &pk.public_param, &wots.randomness)
        .ok_or(AggregationError::MalformedRawSignature)?;
    let mut randomness = [0u8; xmss::STATE_LEN];
    randomness[..xmss::RANDOMNESS_LEN].copy_from_slice(&wots.randomness);
    hints.push(
        "rand",
        vec![pack_16_bytes(&randomness[..16]), pack_16_bytes(&randomness[16..])],
    );
    // Per digest lane, neighbouring chains in pairs `e_c + CHAIN_LENGTH·e_{c+1}`, then the odd one out.
    for lane in encoding.chunks(xmss::V / 2) {
        for digits in lane.chunks(2) {
            let packed = digits
                .iter()
                .rev()
                .fold(0, |acc, &e| acc * xmss::CHAIN_LENGTH + e as usize);
            hints.push("digits", vec![count(packed)]);
        }
    }
    for tip in &wots.chain_tips {
        hints.push("chain_starts", vec![pack_16_bytes(tip)]);
    }
    for sibling in &sig.merkle_proof {
        hints.push("siblings", vec![pack_16_bytes(sibling)]);
    }
    Ok(())
}

/// Every hint stream of one node, in the order the program pops each.
fn node_hints(cover: &Coverage, raw: &[RawSignature], children: &[XmssAggregate]) -> Result<Hints, AggregationError> {
    let mut hints = Hints::default();
    hints.push(
        "meta",
        vec![
            count(cover.n_declared),
            count(cover.groups.len() - cover.n_declared),
            count(children.len()),
        ],
    );
    let group_cells = |group: &XmssClaimGroup| {
        [
            F192::new(u64::from(group.leaf_index), 0, 0),
            pack_16_bytes(&group.message[..16]),
            pack_16_bytes(&group.message[16..]),
        ]
    };
    for (j, group) in cover.groups.iter().enumerate() {
        let n_raw = raw
            .iter()
            .filter(|(_, leaf_index, message, _)| (*leaf_index, *message) == (group.leaf_index, group.message))
            .count();
        let mut entry = group_cells(group).to_vec();
        entry.extend([count(group.keys.len()), count(cover.dups[j].len()), count(n_raw)]);
        hints.push("group", entry);
    }
    for group in &cover.groups[..cover.n_declared] {
        let keys = &group.keys;
        hints.push("pk_halves", vec![count(keys.len() / 2), count(keys.len() % 2)]);
        hints.push("signers_split", signers_split(keys.len().div_ceil(2)));
        for pair in keys.chunks(2) {
            hints.push("pubkeys", pair.iter().flat_map(key_cells).collect());
        }
    }
    for dups in &cover.dups {
        for pk in dups {
            hints.push("dup_pubkeys", key_cells(pk).to_vec());
        }
    }
    hints.push("signers_split", signers_split(1 + 2 * cover.n_declared));
    for &i in &cover.raw_walk {
        let (pk, leaf_index, message, sig) = &raw[i];
        hints.push("raw_index", vec![count(cover.raw[i])]);
        push_signature_hints(&mut hints, pk, sig, message, *leaf_index)?;
    }
    for (child, groups) in children.iter().zip(&cover.children) {
        hints.push("child_meta", vec![count(child.signers.len())]);
        for (group, (parent, offsets)) in child.signers.iter().zip(groups) {
            let mut entry = group_cells(group).to_vec();
            entry.push(count(group.keys.len()));
            hints.push("child_group", entry);
            hints.push("child_group_map", vec![count(*parent)]);
            hints.push("child_halves", vec![count(offsets.len() / 2), count(offsets.len() % 2)]);
            hints.push("signers_split", signers_split(offsets.len().div_ceil(2)));
            for pair in offsets.chunks(2) {
                hints.push("child_index", pair.iter().map(|&idx| count(idx)).collect());
            }
        }
        hints.push("signers_split", signers_split(1 + 2 * child.signers.len()));
    }
    if !children.is_empty() {
        hints.push("signers_split", signers_split(1 + children.len()));
    }
    Ok(hints)
}

/// Prove a node over raw signatures and child aggregates. `declare` is `None` to publish the whole union,
/// or exactly the claims to publish, each of which the inputs must cover. Children are not verified here;
/// [`XmssAggregate::verify`] checks the whole tree.
pub fn aggregate(
    children: Vec<XmssAggregate>,
    raw: Vec<RawSignature>,
    declare: Option<&[XmssClaimGroup]>,
    log_inv_rate: usize,
) -> Result<XmssAggregate, AggregationError> {
    aggregate_with_stats(children, raw, declare, log_inv_rate).map(|(aggregate, _)| aggregate)
}

/// [`aggregate`], also returning the prover's statistics.
pub fn aggregate_with_stats(
    children: Vec<XmssAggregate>,
    raw: Vec<RawSignature>,
    declare: Option<&[XmssClaimGroup]>,
    log_inv_rate: usize,
) -> Result<(XmssAggregate, Stats), AggregationError> {
    if !(leanvm_core::pcs::MIN_LOG_INV_RATE..=leanvm_core::pcs::MAX_LOG_INV_RATE).contains(&log_inv_rate) {
        return Err(AggregationError::InvalidRate { log_inv_rate });
    }
    if children.len() > MAX_RECURSIONS {
        return Err(AggregationError::TooLarge);
    }
    for child in &children {
        check_signer_set(&child.signers).map_err(AggregationError::InvalidChild)?;
    }
    let mut raw = raw;
    raw.sort_by(|(a, ai, am, _), (b, bi, bm, _)| (ai, am, a).cmp(&(bi, bm, b)));
    raw.dedup_by(|(a, ai, am, _), (b, bi, bm, _)| (ai, am, a) == (bi, bm, b));
    let claims: Vec<(XmssPublicKey, LeafIndex, Message)> = raw
        .iter()
        .map(|(pk, leaf_index, message, _)| (pk.clone(), *leaf_index, *message))
        .collect();
    let cover = plan_coverage(&claims, &children, declare)?;
    let hints = node_hints(&cover, &raw, &children)?;
    let signers = cover.groups[..cover.n_declared].to_vec();
    prove_node(signers, children, hints, log_inv_rate)
}

fn prove_node(
    signers: Vec<XmssClaimGroup>,
    children: Vec<XmssAggregate>,
    hints: Hints,
    log_inv_rate: usize,
) -> Result<(XmssAggregate, Stats), AggregationError> {
    let child_sets: Vec<[u8; 32]> = children.iter().map(|child| signers_hash(&child.signers)).collect();
    let statement = node_statement(signers_hash(&signers), &child_sets);
    let mut program = program().clone();
    for (name, entries) in hints.0 {
        program.set_witness(name, entries);
    }
    let (proof, stats) =
        prove(&program, pack_hash_state(&statement), log_inv_rate).map_err(AggregationError::ProofError)?;
    Ok((
        XmssAggregate {
            signers,
            children,
            proof,
        },
        stats,
    ))
}

#[cfg(test)]
mod tests;
