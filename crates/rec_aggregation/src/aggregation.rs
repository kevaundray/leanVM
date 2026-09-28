//! Recursive XMSS, SPHINCS and LeanDA claims with RV64IM application execution.
//!
//! Every raw input is checked by guest execution and every supplied child by
//! the same field-native recursive verifier, including unpublished claims.
//! Native proofs bind the canonical statement and trusted aggregate ELF.

use bincode::Options as _;
use leanvm_aggregation_guest as guest;
use sphincs::{SphincsPublicKey, SphincsSignature};
use ssz::Encode as _;
use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;
use std::sync::{Arc, Mutex};
use xmss::{XmssPublicKey, XmssSignature};

pub use guest::{MAX_DA_ROOTS, MAX_EPOCHS, MAX_KEYS};
/// Public fan-in. Internal native recursion nodes are binary.
pub const MAX_RECURSIONS: usize = 16;
pub use lean_da::{BLOB_SYMBOLS, DA_LOG_CELL, DA_LOG_K, DA_MAX_ROWS};

/// A key and the message it signed under SPHINCS.
pub type SphincsClaim = (SphincsPublicKey, sphincs::Message);

/// Strictly sorted XMSS keys sharing one epoch and message.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct XmssClaimGroup {
    pub epoch: xmss::Epoch,
    pub message: xmss::Message,
    pub keys: Vec<XmssPublicKey>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct SignatureClaims {
    pub xmss: Vec<XmssClaimGroup>,
    pub sphincs: Vec<SphincsClaim>,
}

/// Exactly the claims to publish; input ordering and duplicates are normalized.
#[derive(Clone, Copy)]
pub struct ClaimSelection<'a> {
    pub signatures: &'a SignatureClaims,
    pub da_commitments: &'a [[u8; 32]],
}

/// An unavailable image is different from a present image with an invalid ABI.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GuestImageError {
    Missing {
        variable: &'static str,
        path: Option<PathBuf>,
    },
    Unreadable {
        path: PathBuf,
        reason: String,
    },
    Malformed(String),
}

impl std::fmt::Display for GuestImageError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Missing { variable, path } => write!(
                f,
                "guest image missing; set {variable} to a built RV64IM ELF (path: {path:?})"
            ),
            Self::Unreadable { path, reason } => write!(f, "cannot read guest image {}: {reason}", path.display()),
            Self::Malformed(reason) => write!(f, "malformed RV64IM guest image: {reason}"),
        }
    }
}
impl std::error::Error for GuestImageError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AggregateVerifyError {
    MalformedSignerSet,
    MalformedDaCommitments,
    MalformedEncoding,
    GuestImage(GuestImageError),
    Snark(recursion::Error),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AggregationError {
    ConflictingMessages,
    TooManyEpochs,
    InvalidChild(AggregateVerifyError),
    Empty,
    NotCovered,
    /// A supplied signature is invalid, including an omitted or duplicate one.
    MalformedRawSignature,
    TooLarge,
    InvalidBlobSize {
        symbols: usize,
    },
    BlobNotCovered,
    InvalidRate {
        log_inv_rate: usize,
    },
    GuestImage(GuestImageError),
    WitnessEncoding(String),
    Proving(riscv_proof::Error),
    Recursion(recursion::Error),
}

impl std::fmt::Display for AggregateVerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MalformedSignerSet => write!(f, "malformed signer set"),
            Self::MalformedDaCommitments => write!(f, "malformed DA commitment list"),
            Self::MalformedEncoding => write!(f, "not a valid native aggregate encoding"),
            Self::GuestImage(e) => e.fmt(f),
            Self::Snark(e) => write!(f, "native recursive proof did not verify: {e:?}"),
        }
    }
}
impl std::error::Error for AggregateVerifyError {}
impl std::fmt::Display for AggregationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ConflictingMessages => write!(f, "two claims at one epoch carry different messages"),
            Self::TooManyEpochs => write!(f, "more than MAX_EPOCHS ({MAX_EPOCHS}) epochs"),
            Self::InvalidChild(e) => write!(f, "invalid child aggregate: {e}"),
            Self::Empty => write!(f, "no signature claims or DA roots to publish"),
            Self::NotCovered => write!(f, "a declared signature claim is not covered"),
            Self::MalformedRawSignature => write!(f, "invalid raw signature"),
            Self::TooLarge => write!(f, "too many children, signature contributions, or DA roots"),
            Self::InvalidBlobSize { symbols } => write!(
                f,
                "{symbols} blob symbols do not form at most {DA_MAX_ROWS} rows of {BLOB_SYMBOLS} symbols"
            ),
            Self::BlobNotCovered => write!(f, "a requested DA commitment is not covered"),
            Self::InvalidRate { log_inv_rate } => write!(f, "invalid inverse code rate logarithm {log_inv_rate}"),
            Self::GuestImage(e) => e.fmt(f),
            Self::WitnessEncoding(e) => write!(f, "cannot encode guest witness: {e}"),
            Self::Proving(e) => write!(f, "RV64IM proving failed: {e:?}"),
            Self::Recursion(e) => write!(f, "native recursive proving failed: {e:?}"),
        }
    }
}
impl std::error::Error for AggregationError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::InvalidChild(e) => Some(e),
            Self::GuestImage(e) => Some(e),
            _ => None,
        }
    }
}

pub(crate) struct GuestImage {
    pub elf: Vec<u8>,
    pub program: riscv::Program,
    pub info: riscv_proof::ProgramInfo,
}

/// Reload the trusted image on every operation. Cached recursion keys are
/// invalidated by the digest of these exact bytes, never by wire metadata.
pub(crate) fn load_guest(variable: &'static str) -> Result<GuestImage, GuestImageError> {
    let elf = if let Some(path) = std::env::var_os(variable).map(PathBuf::from) {
        std::fs::read(&path).map_err(|error| {
            if error.kind() == std::io::ErrorKind::NotFound {
                GuestImageError::Missing {
                    variable,
                    path: Some(path.clone()),
                }
            } else {
                GuestImageError::Unreadable {
                    path,
                    reason: error.to_string(),
                }
            }
        })?
    } else {
        let bytes: &[u8] = match variable {
            "LEANVM_GUEST_ELF" => include_bytes!(concat!(env!("OUT_DIR"), "/aggregate.elf")),
            "LEANVM_FIBONACCI_ELF" => include_bytes!(concat!(env!("OUT_DIR"), "/fibonacci.elf")),
            "LEANVM_HASH_CHAIN_ELF" => include_bytes!(concat!(env!("OUT_DIR"), "/hash_chain.elf")),
            _ => return Err(GuestImageError::Missing { variable, path: None }),
        };
        bytes.to_vec()
    };
    let program = riscv::Program::from_elf(&elf).map_err(|e| GuestImageError::Malformed(e.to_string()))?;
    let info = riscv_proof::ProgramInfo::from_elf(&elf).map_err(|e| GuestImageError::Malformed(format!("{e:?}")))?;
    Ok(GuestImage { elf, program, info })
}

type CachedRecursor = Option<([u8; 32], Arc<recursion::Recursor>)>;
static RECURSOR: Mutex<CachedRecursor> = Mutex::new(None);

fn recursor(image: &GuestImage) -> Result<Arc<recursion::Recursor>, recursion::Error> {
    let digest = primitives::hash::hash(&image.elf);
    let mut cached = RECURSOR.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    if let Some((previous, key)) = cached.as_ref()
        && *previous == digest
    {
        return Ok(Arc::clone(key));
    }
    let key = Arc::new(recursion::Recursor::new(&image.info)?);
    *cached = Some((digest, Arc::clone(&key)));
    Ok(key)
}

/// Check that the configured aggregate guest is available and well formed.
/// Prove/verify return typed image errors; this benchmark convenience panics.
pub fn warm_up() {
    let image = load_guest("LEANVM_GUEST_ELF").expect("load aggregate RV64IM guest");
    recursor(&image).expect("compile native aggregate recursion key");
}

fn statement(xmss: &[XmssClaimGroup], sphincs: &[SphincsClaim], roots: &[[u8; 32]]) -> guest::Statement {
    guest::Statement {
        xmss: xmss
            .iter()
            .map(|g| guest::XmssGroup {
                epoch: g.epoch,
                message: g.message,
                keys: g.keys.iter().map(|key| key.flatten()).collect(),
            })
            .collect(),
        sphincs: sphincs
            .iter()
            .map(|(key, message)| guest::SphincsClaim {
                key: key.flatten(),
                message: *message,
            })
            .collect(),
        da_roots: roots.to_vec(),
    }
}

fn native_claims(statement: &guest::Statement) -> SignatureClaims {
    SignatureClaims {
        xmss: statement
            .xmss
            .iter()
            .map(|g| XmssClaimGroup {
                epoch: g.epoch,
                message: g.message,
                keys: g
                    .keys
                    .iter()
                    .map(|key| XmssPublicKey {
                        merkle_root: key[..16].try_into().expect("fixed-size root"),
                        public_param: key[16..].try_into().expect("fixed-size parameter"),
                    })
                    .collect(),
            })
            .collect(),
        sphincs: statement
            .sphincs
            .iter()
            .map(|claim| (SphincsPublicKey::from_bytes(&claim.key), claim.message))
            .collect(),
    }
}

fn check_signer_set(xmss: &[XmssClaimGroup], sphincs: &[SphincsClaim]) -> Result<(), AggregateVerifyError> {
    let total = xmss.iter().map(|g| g.keys.len()).sum::<usize>() + sphincs.len();
    if total >= MAX_KEYS
        || xmss.len() > MAX_EPOCHS
        || xmss.windows(2).any(|w| w[0].epoch >= w[1].epoch)
        || xmss
            .iter()
            .any(|g| g.keys.is_empty() || g.keys.windows(2).any(|w| w[0] >= w[1]))
        || sphincs.windows(2).any(|w| w[0] >= w[1])
    {
        return Err(AggregateVerifyError::MalformedSignerSet);
    }
    Ok(())
}
fn check_da_roots(roots: &[[u8; 32]]) -> Result<(), AggregateVerifyError> {
    if roots.len() > MAX_DA_ROOTS || roots.windows(2).any(|w| w[0] >= w[1]) {
        return Err(AggregateVerifyError::MalformedDaCommitments);
    }
    Ok(())
}
fn da_list_digest(roots: &[[u8; 32]]) -> [u8; 32] {
    let mut bytes = Vec::with_capacity(64 * roots.len());
    for root in roots {
        bytes.extend_from_slice(root);
        bytes.extend_from_slice(&lean_da::vector_digest(&lean_da::membership_vector(root)));
    }
    primitives::hash::hash(&bytes)
}

/// Verified claims, once `verify` succeeds. Epochs/messages are chosen by the
/// prover; applications must compare them and the DA roots to their expectations.
/// The claim count is not a distinct-key count across messages or epochs.
#[derive(Clone, Debug)]
pub struct EthereumProof {
    xmss_signers: Vec<XmssClaimGroup>,
    sphincs_signers: Vec<SphincsClaim>,
    da_roots: Vec<[u8; 32]>,
    proof: recursion::NodeProof,
}

const WIRE_FULL: [u8; 8] = *b"RVAGG002";
const WIRE_OMITTED: [u8; 8] = *b"RVAGGO02";
type WireFull = ([u8; 8], Vec<u8>, Vec<u8>);
type WireCore = ([u8; 8], Vec<[u8; 32]>, Vec<u8>);
fn wire() -> impl bincode::Options {
    bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .reject_trailing_bytes()
}

impl EthereumProof {
    fn statement(&self) -> guest::Statement {
        statement(&self.xmss_signers, &self.sphincs_signers, &self.da_roots)
    }
    pub fn xmss_signers(&self) -> &[XmssClaimGroup] {
        &self.xmss_signers
    }
    pub fn sphincs_signers(&self) -> &[SphincsClaim] {
        &self.sphincs_signers
    }
    pub fn da_commitments(&self) -> &[[u8; 32]] {
        &self.da_roots
    }
    /// BLAKE2s of the root/vector-digest pairs, preserving the public DA API.
    pub fn da_commitments_digest(&self) -> [u8; 32] {
        da_list_digest(&self.da_roots)
    }
    pub fn num_signature_claims(&self) -> usize {
        self.xmss_signers.iter().map(|g| g.keys.len()).sum::<usize>() + self.sphincs_signers.len()
    }
    pub(crate) fn proof(&self) -> &recursion::NodeProof {
        &self.proof
    }

    /// Versioned native proof encoding. Parsing alone is not verification.
    pub fn to_bytes(&self) -> Vec<u8> {
        let statement = self.statement().to_bytes().expect("canonical aggregate statement");
        wire()
            .serialize(&(WIRE_FULL, statement, self.proof.to_bytes()))
            .expect("aggregate serializes")
    }
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, AggregateVerifyError> {
        let (magic, encoded, proof): WireFull = wire()
            .with_limit(bytes.len() as u64)
            .deserialize(bytes)
            .map_err(|_| AggregateVerifyError::MalformedEncoding)?;
        if magic != WIRE_FULL {
            return Err(AggregateVerifyError::MalformedEncoding);
        }
        let statement = guest::Statement::from_bytes(&encoded).map_err(|_| AggregateVerifyError::MalformedEncoding)?;
        let keys = native_claims(&statement);
        Self::from_parts(keys, statement.da_roots, proof)
    }
    pub fn to_bytes_without_pubkeys(&self) -> Vec<u8> {
        wire()
            .serialize(&(WIRE_OMITTED, &self.da_roots, self.proof.to_bytes()))
            .expect("aggregate serializes")
    }
    pub fn from_bytes_without_pubkeys(bytes: &[u8], keys: SignatureClaims) -> Result<Self, AggregateVerifyError> {
        let (magic, roots, proof): WireCore = wire()
            .with_limit(bytes.len() as u64)
            .deserialize(bytes)
            .map_err(|_| AggregateVerifyError::MalformedEncoding)?;
        if magic != WIRE_OMITTED {
            return Err(AggregateVerifyError::MalformedEncoding);
        }
        Self::from_parts(keys, roots, proof)
    }
    fn from_parts(
        keys: SignatureClaims,
        da_roots: Vec<[u8; 32]>,
        encoded: Vec<u8>,
    ) -> Result<Self, AggregateVerifyError> {
        check_signer_set(&keys.xmss, &keys.sphincs)?;
        check_da_roots(&da_roots)?;
        let count = keys.xmss.iter().map(|g| g.keys.len()).sum::<usize>() + keys.sphincs.len() + da_roots.len();
        if count == 0 || count >= MAX_KEYS {
            return Err(AggregateVerifyError::MalformedSignerSet);
        }
        let proof = recursion::NodeProof::from_bytes(&encoded).map_err(|_| AggregateVerifyError::MalformedEncoding)?;
        Ok(Self {
            xmss_signers: keys.xmss,
            sphincs_signers: keys.sphincs,
            da_roots,
            proof,
        })
    }
    fn verify_with(&self, recursor: &recursion::Recursor) -> Result<(), AggregateVerifyError> {
        check_signer_set(&self.xmss_signers, &self.sphincs_signers)?;
        check_da_roots(&self.da_roots)?;
        let digest = self
            .statement()
            .digest()
            .map_err(|_| AggregateVerifyError::MalformedSignerSet)?;
        recursor
            .verify(digest, &self.proof)
            .map_err(AggregateVerifyError::Snark)?;
        Ok(())
    }
    /// Verify against the trusted aggregate ELF, never an image from the wire.
    pub fn verify(&self) -> Result<(), AggregateVerifyError> {
        check_signer_set(&self.xmss_signers, &self.sphincs_signers)?;
        check_da_roots(&self.da_roots)?;
        let image = load_guest("LEANVM_GUEST_ELF").map_err(AggregateVerifyError::GuestImage)?;
        self.verify_with(recursor(&image).map_err(AggregateVerifyError::Snark)?.as_ref())
    }
}

fn bind_message(
    messages: &mut BTreeMap<xmss::Epoch, xmss::Message>,
    epoch: xmss::Epoch,
    message: xmss::Message,
) -> Result<(), AggregationError> {
    match messages.insert(epoch, message) {
        Some(previous) if previous != message => Err(AggregationError::ConflictingMessages),
        _ => Ok(()),
    }
}

/// Normalize only the published claims, never the inputs whose validity must be checked.
fn plan_coverage(
    raw_xmss: &[(XmssPublicKey, xmss::Epoch, xmss::Message)],
    raw_sphincs: &[SphincsClaim],
    children: &[EthereumProof],
    declare: Option<&SignatureClaims>,
) -> Result<SignatureClaims, AggregationError> {
    let total =
        raw_xmss.len() + raw_sphincs.len() + children.iter().map(EthereumProof::num_signature_claims).sum::<usize>();
    if total >= MAX_KEYS {
        return Err(AggregationError::TooLarge);
    }
    let mut messages = BTreeMap::new();
    let mut keys = BTreeSet::new();
    let mut sphincs: BTreeSet<_> = raw_sphincs.iter().copied().collect();
    for (key, epoch, message) in raw_xmss {
        bind_message(&mut messages, *epoch, *message)?;
        keys.insert((*epoch, key.clone()));
    }
    for child in children {
        check_signer_set(&child.xmss_signers, &child.sphincs_signers).map_err(AggregationError::InvalidChild)?;
        for group in &child.xmss_signers {
            bind_message(&mut messages, group.epoch, group.message)?;
            keys.extend(group.keys.iter().map(|key| (group.epoch, key.clone())));
        }
        sphincs.extend(child.sphincs_signers.iter().copied());
    }
    if messages.len() > MAX_EPOCHS {
        return Err(AggregationError::TooManyEpochs);
    }
    if let Some(declared) = declare {
        let mut wanted = BTreeSet::new();
        for group in &declared.xmss {
            if messages.get(&group.epoch) != Some(&group.message) {
                return Err(AggregationError::NotCovered);
            }
            for key in &group.keys {
                if !keys.contains(&(group.epoch, key.clone())) {
                    return Err(AggregationError::NotCovered);
                }
                wanted.insert((group.epoch, key.clone()));
            }
        }
        let wanted_sphincs: BTreeSet<_> = declared.sphincs.iter().copied().collect();
        if !wanted_sphincs.is_subset(&sphincs) {
            return Err(AggregationError::NotCovered);
        }
        keys = wanted;
        sphincs = wanted_sphincs;
    }
    let mut xmss: Vec<XmssClaimGroup> = Vec::new();
    for (epoch, key) in keys {
        match xmss.last_mut() {
            Some(group) if group.epoch == epoch => group.keys.push(key),
            _ => xmss.push(XmssClaimGroup {
                epoch,
                message: messages[&epoch],
                keys: vec![key],
            }),
        }
    }
    Ok(SignatureClaims {
        xmss,
        sphincs: sphincs.into_iter().collect(),
    })
}

#[derive(Clone, Copy, Default)]
pub(crate) struct DaInput<'a> {
    pub rows: &'a [u64],
    pub roots: Option<&'a [[u8; 32]]>,
}

/// Prove every raw signature and whole-blob commitment with RV64IM execution,
/// then fold all supplied children with the field-native same-key verifier.
/// `declare` only selects final claims. All contributions must total < MAX_KEYS.
pub fn aggregate(
    children: &[EthereumProof],
    raw_xmss: Vec<(XmssPublicKey, xmss::Epoch, xmss::Message, XmssSignature)>,
    raw_sphincs: Vec<(SphincsPublicKey, sphincs::Message, SphincsSignature)>,
    blobs: &[u64],
    declare: Option<ClaimSelection<'_>>,
    log_inv_rate: usize,
) -> Result<EthereumProof, AggregationError> {
    aggregate_with_stats(
        children,
        raw_xmss,
        raw_sphincs,
        declare.map(|d| d.signatures),
        DaInput {
            rows: blobs,
            roots: declare.map(|d| d.da_commitments),
        },
        log_inv_rate,
    )
    .map(|(proof, _)| proof)
}

fn build_input(
    children: &[EthereumProof],
    raw_xmss: Vec<(XmssPublicKey, xmss::Epoch, xmss::Message, XmssSignature)>,
    raw_sphincs: Vec<(SphincsPublicKey, sphincs::Message, SphincsSignature)>,
    declare: Option<&SignatureClaims>,
    da_input: DaInput<'_>,
    log_inv_rate: usize,
) -> Result<(GuestImage, guest::Input), AggregationError> {
    if !(pcs::whir::MIN_LOG_INV_RATE..=pcs::whir::MAX_LOG_INV_RATE).contains(&log_inv_rate) {
        return Err(AggregationError::InvalidRate { log_inv_rate });
    }
    if children.len() > MAX_RECURSIONS {
        return Err(AggregationError::TooLarge);
    }
    if !da_input.rows.len().is_multiple_of(BLOB_SYMBOLS) || da_input.rows.len() / BLOB_SYMBOLS > DA_MAX_ROWS {
        return Err(AggregationError::InvalidBlobSize {
            symbols: da_input.rows.len(),
        });
    }
    let raw_claims: Vec<_> = raw_xmss
        .iter()
        .map(|(key, epoch, message, _)| (key.clone(), *epoch, *message))
        .collect();
    let raw_sphincs_claims: Vec<_> = raw_sphincs.iter().map(|(key, message, _)| (*key, *message)).collect();
    let claims = plan_coverage(&raw_claims, &raw_sphincs_claims, children, declare)?;
    let contributions = raw_xmss.len()
        + raw_sphincs.len()
        + usize::from(!da_input.rows.is_empty())
        + children
            .iter()
            .map(|c| c.num_signature_claims() + c.da_roots.len())
            .sum::<usize>();
    if contributions >= MAX_KEYS {
        return Err(AggregationError::TooLarge);
    }
    let mut available = BTreeSet::new();
    for child in children {
        check_da_roots(&child.da_roots).map_err(AggregationError::InvalidChild)?;
        available.extend(child.da_roots.iter().copied());
    }
    let selected = da_input
        .roots
        .map(|roots| roots.iter().copied().collect::<BTreeSet<_>>());
    if selected.as_ref().unwrap_or(&available).len() > MAX_DA_ROOTS {
        return Err(AggregationError::TooLarge);
    }
    let da = if da_input.rows.is_empty() {
        None
    } else {
        let (commitment, witness) = lean_da::commit(da_input.rows);
        available.insert(commitment.root);
        Some(guest::DirectDa {
            root: commitment.root,
            membership_digest: lean_da::vector_digest(&lean_da::membership_vector(&commitment.root)),
            codewords_le: witness.codewords.into_iter().flat_map(u64::to_le_bytes).collect(),
        })
    };
    let roots = selected.unwrap_or_else(|| available.clone());
    if roots.len() > MAX_DA_ROOTS {
        return Err(AggregationError::TooLarge);
    }
    if !roots.is_subset(&available) {
        return Err(AggregationError::BlobNotCovered);
    }
    if claims.xmss.is_empty() && claims.sphincs.is_empty() && roots.is_empty() {
        return Err(AggregationError::Empty);
    }

    // Early diagnostics only. Raw bytes remain in execution witnesses and
    // every supplied child remains an input to a native verifier circuit.
    for (key, epoch, message, signature) in &raw_xmss {
        xmss::verify(key, message, signature, *epoch).map_err(|_| AggregationError::MalformedRawSignature)?;
    }
    for (key, message, signature) in &raw_sphincs {
        sphincs::verify(key, message, signature).map_err(|_| AggregationError::MalformedRawSignature)?;
    }
    let image = load_guest("LEANVM_GUEST_ELF").map_err(AggregationError::GuestImage)?;
    let recursor = recursor(&image).map_err(AggregationError::Recursion)?;
    for child in children {
        child.verify_with(&recursor).map_err(AggregationError::InvalidChild)?;
    }
    let input = guest::Input {
        statement: statement(&claims.xmss, &claims.sphincs, &roots.into_iter().collect::<Vec<_>>()),
        children: children
            .iter()
            .map(|child| guest::Child {
                statement: child.statement(),
                key: recursor.key_digest(),
                height: child.proof.height,
            })
            .collect(),
        xmss: raw_xmss
            .into_iter()
            .map(|(key, epoch, message, signature)| guest::RawXmss {
                key: key.flatten(),
                epoch,
                message,
                signature: signature.as_ssz_bytes(),
            })
            .collect(),
        sphincs: raw_sphincs
            .into_iter()
            .map(|(key, message, signature)| guest::RawSphincs {
                key: key.flatten(),
                message,
                signature: signature.to_bytes().to_vec(),
            })
            .collect(),
        da,
    };
    Ok((image, input))
}

/// Total execution work across all nodes, not dimensions of the final proof.
#[derive(Default)]
pub(crate) struct AggregateStats {
    pub executions: usize,
    pub cycles: u64,
    pub memory_events: u64,
    pub committed_words: u64,
}

fn prove_node(
    image: &GuestImage,
    recursor: &recursion::Recursor,
    input: guest::Input,
    children: &[&EthereumProof],
    log_inv_rate: usize,
    stats: &mut AggregateStats,
) -> Result<EthereumProof, AggregationError> {
    let public = guest::public_input(&input.statement, &input.children)
        .map_err(|e| AggregationError::WitnessEncoding(e.to_string()))?;
    let digest = input
        .statement
        .digest()
        .map_err(|e| AggregationError::WitnessEncoding(e.to_string()))?;
    let witness = input
        .to_witness()
        .map_err(|e| AggregationError::WitnessEncoding(e.to_string()))?;
    let (execution, summary) = riscv_proof::host::prove(&image.program, public, &witness, u64::MAX, log_inv_rate as u8)
        .map_err(AggregationError::Proving)?;
    let native_children = children
        .iter()
        .map(|child| {
            Ok(recursion::Child {
                statement: child
                    .statement()
                    .digest()
                    .map_err(|e| AggregationError::WitnessEncoding(e.to_string()))?,
                proof: &child.proof,
            })
        })
        .collect::<Result<Vec<_>, AggregationError>>()?;
    let proof = recursor
        .prove(digest, &execution, &native_children, log_inv_rate)
        .map_err(AggregationError::Recursion)?;
    stats.executions += 1;
    stats.cycles += summary.cycles;
    stats.memory_events += summary.memory_events;
    stats.committed_words += summary.committed_words;
    let keys = native_claims(&input.statement);
    Ok(EthereumProof {
        xmss_signers: keys.xmss,
        sphincs_signers: keys.sphincs,
        da_roots: input.statement.da_roots,
        proof,
    })
}

fn child_input(children: &[&EthereumProof], key: [u8; 32]) -> Result<guest::Input, AggregationError> {
    let mut messages = BTreeMap::new();
    let mut xmss = BTreeSet::new();
    let mut sphincs = BTreeSet::new();
    let mut roots = BTreeSet::new();
    for child in children {
        for group in &child.xmss_signers {
            bind_message(&mut messages, group.epoch, group.message)?;
            xmss.extend(group.keys.iter().map(|key| (group.epoch, key.flatten())));
        }
        sphincs.extend(child.sphincs_signers.iter().map(|(key, message)| guest::SphincsClaim {
            key: key.flatten(),
            message: *message,
        }));
        roots.extend(child.da_roots.iter().copied());
    }
    let mut groups: Vec<guest::XmssGroup> = Vec::new();
    for (epoch, key) in xmss {
        match groups.last_mut() {
            Some(group) if group.epoch == epoch => group.keys.push(key),
            _ => groups.push(guest::XmssGroup {
                epoch,
                message: messages[&epoch],
                keys: vec![key],
            }),
        }
    }
    Ok(guest::Input {
        statement: guest::Statement {
            xmss: groups,
            sphincs: sphincs.into_iter().collect(),
            da_roots: roots.into_iter().collect(),
        },
        children: children
            .iter()
            .map(|child| guest::Child {
                statement: child.statement(),
                key,
                height: child.proof.height,
            })
            .collect(),
        ..guest::Input::default()
    })
}

pub(crate) fn aggregate_with_stats(
    children: &[EthereumProof],
    raw_xmss: Vec<(XmssPublicKey, xmss::Epoch, xmss::Message, XmssSignature)>,
    raw_sphincs: Vec<(SphincsPublicKey, sphincs::Message, SphincsSignature)>,
    declare: Option<&SignatureClaims>,
    da_input: DaInput<'_>,
    log_inv_rate: usize,
) -> Result<(EthereumProof, AggregateStats), AggregationError> {
    let (image, input) = build_input(children, raw_xmss, raw_sphincs, declare, da_input, log_inv_rate)?;
    let recursor = recursor(&image).map_err(AggregationError::Recursion)?;
    let mut stats = AggregateStats::default();
    // The host's capacity preflight is execution-derived, not a signature-count
    // estimator. Isolate raw verifications conservatively; even a single item
    // can return its precise Capacity error. Never split a multi-row DA root.
    let raw_count = input.xmss.len() + input.sphincs.len() + usize::from(input.da.is_some());
    if children.len() <= 2 && raw_count <= 1 {
        let refs: Vec<_> = children.iter().collect();
        return prove_node(&image, &recursor, input, &refs, log_inv_rate, &mut stats).map(|proof| (proof, stats));
    }
    let final_statement = input.statement;
    let mut layer: Vec<std::borrow::Cow<'_, EthereumProof>> = children.iter().map(std::borrow::Cow::Borrowed).collect();
    for raw in input.xmss {
        let statement = guest::Statement {
            xmss: vec![guest::XmssGroup {
                epoch: raw.epoch,
                message: raw.message,
                keys: vec![raw.key],
            }],
            ..guest::Statement::default()
        };
        let leaf = guest::Input {
            statement,
            xmss: vec![raw],
            ..guest::Input::default()
        };
        layer.push(std::borrow::Cow::Owned(prove_node(
            &image,
            &recursor,
            leaf,
            &[],
            log_inv_rate,
            &mut stats,
        )?));
    }
    for raw in input.sphincs {
        let statement = guest::Statement {
            sphincs: vec![guest::SphincsClaim {
                key: raw.key,
                message: raw.message,
            }],
            ..guest::Statement::default()
        };
        let leaf = guest::Input {
            statement,
            sphincs: vec![raw],
            ..guest::Input::default()
        };
        layer.push(std::borrow::Cow::Owned(prove_node(
            &image,
            &recursor,
            leaf,
            &[],
            log_inv_rate,
            &mut stats,
        )?));
    }
    if let Some(da) = input.da {
        // TODO: Prove direct LeanDA with native circuits and authenticated row coverage.
        let statement = guest::Statement {
            da_roots: vec![da.root],
            ..guest::Statement::default()
        };
        let leaf = guest::Input {
            statement,
            da: Some(da),
            ..guest::Input::default()
        };
        layer.push(std::borrow::Cow::Owned(prove_node(
            &image,
            &recursor,
            leaf,
            &[],
            log_inv_rate,
            &mut stats,
        )?));
    }
    while layer.len() > 2 {
        let mut next = Vec::with_capacity(layer.len().div_ceil(2));
        let mut nodes = layer.into_iter();
        while let Some(left) = nodes.next() {
            if let Some(right) = nodes.next() {
                let refs = [left.as_ref(), right.as_ref()];
                let parent = child_input(&refs, recursor.key_digest())?;
                next.push(std::borrow::Cow::Owned(prove_node(
                    &image,
                    &recursor,
                    parent,
                    &refs,
                    log_inv_rate,
                    &mut stats,
                )?));
            } else {
                next.push(left);
            }
        }
        layer = next;
    }
    let refs: Vec<_> = layer.iter().map(std::borrow::Cow::as_ref).collect();
    let mut root = child_input(&refs, recursor.key_digest())?;
    root.statement = final_statement;
    prove_node(&image, &recursor, root, &refs, log_inv_rate, &mut stats).map(|proof| (proof, stats))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::signers_cache::{
        KEY_START, XMSS_EPOCH_A, XMSS_EPOCH_B, get_signers, get_signers_at, get_sphincs_signers, message, message_for,
    };
    use rand::{SeedableRng, rngs::StdRng};
    const SMALL_LEAF_SIZE: usize = 6;
    const LOG_INV_RATE: usize = 2;
    /// Cached `(key, signature)` pairs as the API takes them, every one at
    /// `epoch` over the cache's message for it.
    fn at_epoch(
        signers: &[(XmssPublicKey, XmssSignature)],
        epoch: xmss::Epoch,
    ) -> Vec<(XmssPublicKey, xmss::Epoch, xmss::Message, XmssSignature)> {
        signers
            .iter()
            .map(|(pk, sig)| (pk.clone(), epoch, message_for(epoch), sig.clone()))
            .collect()
    }

    fn xmss_claims(sig: &EthereumProof) -> usize {
        sig.xmss_signers.iter().map(|group| group.keys.len()).sum()
    }

    /// Distinct keys, strictly increasing, without generating any.
    fn signer_set(len: usize) -> Vec<XmssPublicKey> {
        (0..len)
            .map(|i| XmssPublicKey {
                merkle_root: (i as u128).to_be_bytes(),
                public_param: [0; xmss::PUBLIC_PARAM_LEN],
            })
            .collect()
    }

    /// `MAX_KEYS` is exclusive at both host checks: one key short of it passes,
    /// the cap itself is the documented error. The cap counts both schemes, so
    /// one XMSS key short of it plus one SPHINCS claim is already over. No proof
    /// involved, and the epoch cap has its own error alongside.
    #[test]
    fn max_keys_bound_is_exclusive() {
        let full = signer_set(MAX_KEYS);
        let group = |keys: &[XmssPublicKey]| {
            vec![XmssClaimGroup {
                epoch: XMSS_EPOCH_A,
                message: message(),
                keys: keys.to_vec(),
            }]
        };
        let claims = |keys: &[XmssPublicKey]| -> Vec<(XmssPublicKey, xmss::Epoch, xmss::Message)> {
            keys.iter().map(|pk| (pk.clone(), XMSS_EPOCH_A, message())).collect()
        };
        let claim = [(
            SphincsPublicKey::from_bytes(&[0; sphincs::PUB_KEY_SIZE]),
            [0; sphincs::MESSAGE_LEN],
        )];
        check_signer_set(&group(&full[..MAX_KEYS - 1]), &[]).expect("one short of the cap");
        assert_eq!(
            check_signer_set(&group(&full), &[]),
            Err(AggregateVerifyError::MalformedSignerSet)
        );
        assert_eq!(
            check_signer_set(&group(&full[..MAX_KEYS - 1]), &claim),
            Err(AggregateVerifyError::MalformedSignerSet)
        );
        // One group per epoch: MAX_EPOCHS groups pass, one more is malformed.
        let spread = |n: usize| -> Vec<XmssClaimGroup> {
            (0..n)
                .map(|e| XmssClaimGroup {
                    epoch: e as u32,
                    message: message(),
                    keys: vec![full[e].clone()],
                })
                .collect()
        };
        check_signer_set(&spread(MAX_EPOCHS), &[]).expect("at the epoch cap");
        assert_eq!(
            check_signer_set(&spread(MAX_EPOCHS + 1), &[]),
            Err(AggregateVerifyError::MalformedSignerSet)
        );
        plan_coverage(&claims(&full[..MAX_KEYS - 1]), &[], &[], None).expect("one short of the cap");
        assert_eq!(
            plan_coverage(&claims(&full), &[], &[], None).err(),
            Some(AggregationError::TooLarge)
        );
        assert_eq!(
            plan_coverage(&claims(&full[..MAX_KEYS - 1]), &claim, &[], None).err(),
            Some(AggregationError::TooLarge)
        );
        let spread_claims = |n: usize| -> Vec<(XmssPublicKey, xmss::Epoch, xmss::Message)> {
            (0..n).map(|e| (full[e].clone(), e as u32, message())).collect()
        };
        plan_coverage(&spread_claims(MAX_EPOCHS), &[], &[], None).expect("at the epoch cap");
        assert_eq!(
            plan_coverage(&spread_claims(MAX_EPOCHS + 1), &[], &[], None).err(),
            Some(AggregationError::TooManyEpochs)
        );
    }

    fn prove_leaf(signers: &[(XmssPublicKey, XmssSignature)]) -> EthereumProof {
        aggregate(&[], at_epoch(signers, XMSS_EPOCH_A), vec![], &[], None, LOG_INV_RATE).expect("leaf aggregates")
    }

    #[test]
    fn keygen_and_verification_hash_domains_are_disjoint() {
        let xmss_tags = [
            xmss::TWEAK_TYPE_PRF,
            xmss::TWEAK_TYPE_CHAIN,
            xmss::TWEAK_TYPE_WOTS_PK,
            xmss::TWEAK_TYPE_MERKLE,
            xmss::TWEAK_TYPE_ENCODING,
            xmss::TWEAK_TYPE_PARAMETER,
            xmss::TWEAK_TYPE_FILLER,
        ];
        let sphincs_tags = [
            sphincs::TWEAK_PRF,
            sphincs::TWEAK_CHAIN,
            sphincs::TWEAK_LEAF,
            sphincs::TWEAK_NODE,
            sphincs::TWEAK_ENC,
            sphincs::TWEAK_FTS_PRF,
            sphincs::TWEAK_FTS_LEAF,
            sphincs::TWEAK_FTS_NODE,
            sphincs::TWEAK_FTS_ROOTS,
            sphincs::TWEAK_MSG,
            sphincs::TWEAK_PARAMETER,
        ];
        let domains: BTreeSet<_> = xmss_tags
            .into_iter()
            .map(|tag| xmss::make_tweak(tag, 0, 0))
            .chain(sphincs_tags.into_iter().map(|tag| sphincs::tweak(tag, 0, 0, 0, 0)))
            .collect();
        assert_eq!(domains.len(), xmss_tags.len() + sphincs_tags.len());
    }

    type RawSphincs = (SphincsPublicKey, sphincs::Message, SphincsSignature);

    fn prove_sphincs_leaf(signers: &[RawSphincs]) -> EthereumProof {
        aggregate(&[], vec![], signers.to_vec(), &[], None, LOG_INV_RATE).expect("leaf aggregates")
    }

    #[test]
    fn aggregate_one_sphincs_signer() {
        parallel::init();
        let aggregate = prove_sphincs_leaf(&get_sphincs_signers(1));
        aggregate.verify().expect("verifies");
        assert!(aggregate.xmss_signers.is_empty());
        assert_eq!(aggregate.sphincs_signers.len(), 1);
    }

    #[test]
    fn aggregate_one_signer() {
        parallel::init();
        let aggregate = prove_leaf(&get_signers(1));
        aggregate.verify().expect("verifies");
        assert_eq!(aggregate.xmss_signers[0].epoch, XMSS_EPOCH_A);
        assert_eq!(aggregate.xmss_signers[0].message, message());
    }

    /// Both schemes coexist in one canonical statement.
    #[test]
    fn aggregate_mixed_leaf() {
        parallel::init();
        let aggregate = aggregate(
            &[],
            at_epoch(&get_signers(3), XMSS_EPOCH_A),
            get_sphincs_signers(3),
            &[],
            None,
            LOG_INV_RATE,
        )
        .expect("leaf aggregates");
        aggregate.verify().expect("verifies");
        assert_eq!((xmss_claims(&aggregate), aggregate.sphincs_signers.len()), (3, 3));
    }

    /// A node over children of both schemes, overlapping in one signer of each:
    /// the coverage table then needs a duplicate slot in both regions, and each
    /// child's two key lists have to land in their own.
    #[test]
    fn aggregate_mixed_two_to_one() {
        parallel::init();
        let xmss = get_signers(6);
        let sphincs = get_sphincs_signers(4);
        let leaf = |x: &[(XmssPublicKey, XmssSignature)], s: &[RawSphincs]| {
            aggregate(&[], at_epoch(x, XMSS_EPOCH_A), s.to_vec(), &[], None, LOG_INV_RATE).expect("leaf aggregates")
        };
        let left = leaf(&xmss[..4], &sphincs[..3]);
        let right = leaf(&xmss[3..], &sphincs[2..]);
        let node = aggregate(&[left, right], vec![], vec![], &[], None, LOG_INV_RATE).expect("node aggregates");
        node.verify().expect("node verifies");
        assert_eq!((xmss_claims(&node), node.sphincs_signers.len()), (6, 4));
        assert!(node.xmss_signers[0].keys.windows(2).all(|w| w[0] < w[1]));
        assert!(node.sphincs_signers.windows(2).all(|w| w[0] < w[1]));
    }

    /// Each child may carry only one scheme while the parent publishes both.
    #[test]
    fn aggregate_one_scheme_per_child() {
        parallel::init();
        let xmss_child = prove_leaf(&get_signers(3));
        let sphincs_child = prove_sphincs_leaf(&get_sphincs_signers(2));
        let node =
            aggregate(&[xmss_child, sphincs_child], vec![], vec![], &[], None, LOG_INV_RATE).expect("node aggregates");
        node.verify().expect("node verifies");
        assert_eq!((xmss_claims(&node), node.sphincs_signers.len()), (3, 2));
    }

    /// The repeat the statement allows: one key signing two messages is two
    /// claims, ordered by the pair, each needing its own signature. Generated
    /// here rather than cached, the cache holding one message per key.
    #[test]
    fn aggregate_one_key_two_messages() {
        parallel::init();
        let mut rng = StdRng::seed_from_u64(77);
        let (secret_key, public_key) = sphincs::key_gen(&mut rng);
        let raw: Vec<RawSphincs> = [3u8, 9]
            .into_iter()
            .map(|tag| {
                let signed: sphincs::Message = std::array::from_fn(|i| tag.wrapping_mul(i as u8 + 1));
                let signature = sphincs::sign(&secret_key, &signed).expect("signs");
                (public_key, signed, signature)
            })
            .collect();
        let aggregate = prove_sphincs_leaf(&raw);
        aggregate.verify().expect("verifies");
        assert_eq!(aggregate.sphincs_signers.len(), 2);
        let (first, second) = (aggregate.sphincs_signers[0], aggregate.sphincs_signers[1]);
        assert_eq!(first.0, second.0, "the same key, twice");
        assert!(first.1 < second.1, "ordered by the message");
    }

    #[test]
    fn aggregate_two_to_one() {
        parallel::init();
        let big = 70;
        let signers = get_signers(SMALL_LEAF_SIZE + big);
        let left = prove_leaf(&signers[..SMALL_LEAF_SIZE]);
        let right = prove_leaf(&signers[SMALL_LEAF_SIZE..]);
        let node = aggregate(&[left, right], vec![], vec![], &[], None, LOG_INV_RATE).expect("node aggregates");
        node.verify().expect("node verifies");
        assert_eq!(xmss_claims(&node), SMALL_LEAF_SIZE + big);
    }

    fn da_rows(n_rows: usize, seed: u64) -> Vec<u64> {
        let mut rng = <rand::rngs::StdRng as rand::SeedableRng>::seed_from_u64(seed);
        (0..n_rows * (1 << DA_LOG_K))
            .map(|_| rand::Rng::random(&mut rng))
            .collect()
    }

    /// A LeanDA payload, proven without signatures and published in the
    /// statement. The node has to reach the native committer's root, and the
    /// aggregate has to verify against a statement that carries it.
    #[test]
    #[ignore = "Native DA proving is deferred; direct RV64IM execution exceeds proof capacity"]
    fn aggregate_with_a_da_payload() {
        parallel::init();
        let rows = da_rows(3, 97);

        let node = aggregate(&[], vec![], vec![], &rows, None, LOG_INV_RATE).expect("node aggregates");
        node.verify().expect("node verifies");
        assert_eq!(node.num_signature_claims(), 0);

        let (commitment, _) = lean_da::commit(&rows);
        assert_eq!(
            node.da_roots,
            vec![commitment.root],
            "the guest committed to something else"
        );
        let received = EthereumProof::from_bytes(&node.to_bytes()).unwrap();
        assert_eq!(received.da_commitments(), &[commitment.root]);
        received.verify().unwrap();
        let keys = SignatureClaims {
            xmss: node.xmss_signers.clone(),
            sphincs: node.sphincs_signers.clone(),
        };
        let mut core: WireCore = wire().deserialize(&node.to_bytes_without_pubkeys()).unwrap();
        core.1[0][0] ^= 1;
        let bad = EthereumProof::from_bytes_without_pubkeys(&wire().serialize(&core).unwrap(), keys).unwrap();
        assert!(bad.verify().is_err(), "the DA root must bind the VM proof");
    }

    #[test]
    fn invalid_da_selections_are_rejected_before_building_the_proof() {
        let unknown = [[0xa5; 32]];
        assert_eq!(
            aggregate(
                &[],
                vec![],
                vec![],
                &[],
                Some(ClaimSelection {
                    signatures: &SignatureClaims::default(),
                    da_commitments: &unknown
                }),
                LOG_INV_RATE
            )
            .unwrap_err(),
            AggregationError::BlobNotCovered
        );
        let too_many: Vec<_> = (0..=MAX_DA_ROOTS).map(|i| [i as u8; 32]).collect();
        assert_eq!(
            aggregate(
                &[],
                vec![],
                vec![],
                &[],
                Some(ClaimSelection {
                    signatures: &SignatureClaims::default(),
                    da_commitments: &too_many
                }),
                LOG_INV_RATE
            )
            .unwrap_err(),
            AggregationError::TooLarge
        );
    }

    #[test]
    #[ignore = "Native DA proving is deferred; direct RV64IM execution exceeds proof capacity"]
    fn da_roots_accumulate_and_can_be_selected_or_omitted() {
        parallel::init();
        let signers = get_signers(SMALL_LEAF_SIZE);
        let mut children = Vec::new();
        for seed in [509, 510] {
            let rows = da_rows(1, seed);
            children.push(aggregate(&[], at_epoch(&signers, XMSS_EPOCH_A), vec![], &rows, None, LOG_INV_RATE).unwrap());
        }
        let signatures = SignatureClaims {
            xmss: children[0].xmss_signers.clone(),
            sphincs: children[0].sphincs_signers.clone(),
        };
        let first = children[0].da_roots[0];
        let second = children[1].da_roots[0];
        assert_ne!(first, second);
        let mut both = vec![first, second];
        both.sort();
        for selected in [
            None,
            Some(vec![]),
            Some(vec![first]),
            Some(vec![second]),
            Some(vec![second, first, second]),
        ] {
            let node = aggregate(
                &children,
                vec![],
                vec![],
                &[],
                selected.as_deref().map(|roots| ClaimSelection {
                    signatures: &signatures,
                    da_commitments: roots,
                }),
                LOG_INV_RATE,
            )
            .unwrap();
            node.verify().unwrap();
            let mut expected = selected.unwrap_or_else(|| both.clone());
            expected.sort();
            expected.dedup();
            assert_eq!(node.da_roots, expected);
            assert_eq!(node.da_commitments_digest(), da_list_digest(&expected));
            let mut tampered = node.clone();
            tampered.da_roots = vec![[0xa5; 32]];
            assert!(
                tampered.verify().is_err(),
                "changing the root list requires a new proof"
            );
        }
        let repeated = aggregate(
            &[children[0].clone(), children[0].clone()],
            vec![],
            vec![],
            &[],
            None,
            LOG_INV_RATE,
        )
        .unwrap();
        repeated.verify().unwrap();
        assert_eq!(repeated.da_roots, vec![first]);
        let same_rows = da_rows(1, 509);
        let repeated_direct = aggregate(
            std::slice::from_ref(&repeated),
            vec![],
            vec![],
            &same_rows,
            None,
            LOG_INV_RATE,
        )
        .unwrap();
        repeated_direct.verify().unwrap();
        assert_eq!(repeated_direct.da_roots, vec![first]);

        let rows = da_rows(1, 511);
        let new_root = lean_da::commit(&rows).0.root;
        for selected in [vec![new_root], vec![first], vec![]] {
            let node = aggregate(
                &children,
                vec![],
                vec![],
                &rows,
                Some(ClaimSelection {
                    signatures: &signatures,
                    da_commitments: &selected,
                }),
                LOG_INV_RATE,
            )
            .unwrap();
            node.verify().unwrap();
            assert_eq!(node.da_roots, selected);
        }
        assert!(matches!(
            aggregate(
                &children,
                vec![],
                vec![],
                &rows,
                Some(ClaimSelection {
                    signatures: &signatures,
                    da_commitments: &[[0xa5; 32]]
                }),
                LOG_INV_RATE
            ),
            Err(AggregationError::BlobNotCovered)
        ));
        let direct = aggregate(&children, vec![], vec![], &rows, None, LOG_INV_RATE).unwrap();
        direct.verify().unwrap();
        let mut three = both.clone();
        three.push(new_root);
        three.sort();
        assert_eq!(direct.da_roots, three);
        let received = EthereumProof::from_bytes(&direct.to_bytes()).unwrap();
        received.verify().unwrap();
        let nested = aggregate(&[received, repeated], vec![], vec![], &[], None, LOG_INV_RATE).unwrap();
        nested.verify().unwrap();
        assert_eq!(nested.da_roots, three);
        let narrowed = aggregate(
            &[nested],
            vec![],
            vec![],
            &[],
            Some(ClaimSelection {
                signatures: &signatures,
                da_commitments: &[second],
            }),
            LOG_INV_RATE,
        )
        .unwrap();
        narrowed.verify().unwrap();
        assert_eq!(narrowed.da_roots, vec![second]);
        let dropped = aggregate(
            &[narrowed],
            vec![],
            vec![],
            &[],
            Some(ClaimSelection {
                signatures: &signatures,
                da_commitments: &[],
            }),
            LOG_INV_RATE,
        )
        .unwrap();
        dropped.verify().unwrap();
        assert!(dropped.da_roots.is_empty());
        assert_eq!(dropped.da_commitments_digest(), primitives::hash::hash(&[]));
        assert!(matches!(
            aggregate(
                &[dropped],
                vec![],
                vec![],
                &[],
                Some(ClaimSelection {
                    signatures: &signatures,
                    da_commitments: &[second]
                }),
                LOG_INV_RATE
            ),
            Err(AggregationError::BlobNotCovered)
        ));
        assert!(matches!(
            aggregate(
                &children,
                vec![],
                vec![],
                &[],
                Some(ClaimSelection {
                    signatures: &signatures,
                    da_commitments: &[[0xa5; 32]]
                }),
                LOG_INV_RATE
            ),
            Err(AggregationError::BlobNotCovered)
        ));

        for roots in [
            vec![second, second],
            vec![both[1], both[0]],
            vec![[0; 32]; MAX_DA_ROOTS],
        ] {
            let mut bad = direct.clone();
            bad.da_roots = roots;
            assert_eq!(bad.verify(), Err(AggregateVerifyError::MalformedDaCommitments));
        }
    }

    #[test]
    #[ignore = "Native DA proving is deferred; direct RV64IM execution exceeds proof capacity"]
    fn da_root_lists_merge_two_and_three() {
        parallel::init();
        let mut leaves = Vec::new();
        let mut expected = Vec::new();
        for seed in 600..605 {
            let rows = da_rows(1, seed);
            let leaf = aggregate(&[], vec![], vec![], &rows, None, LOG_INV_RATE).unwrap();
            expected.extend_from_slice(leaf.da_commitments());
            leaves.push(leaf);
        }
        let left = aggregate(&leaves[..2], vec![], vec![], &[], None, LOG_INV_RATE).unwrap();
        let right = aggregate(&leaves[2..], vec![], vec![], &[], None, LOG_INV_RATE).unwrap();
        assert_eq!(left.da_commitments().len(), 2);
        assert_eq!(right.da_commitments().len(), 3);
        let root = aggregate(&[left, right], vec![], vec![], &[], None, LOG_INV_RATE).unwrap();
        let root = EthereumProof::from_bytes(&root.to_bytes()).unwrap();
        root.verify().unwrap();
        expected.sort();
        assert_eq!(root.num_signature_claims(), 0);
        assert_eq!(root.da_commitments().len(), 5);
        assert_eq!(root.da_commitments(), expected);
        assert_eq!(root.da_commitments_digest(), da_list_digest(&expected));

        let boundary: Vec<_> = (0..=MAX_DA_ROOTS).map(|i| [i as u8; 32]).collect();
        check_da_roots(&boundary[..MAX_DA_ROOTS]).unwrap();
        let mut full = root.clone();
        full.da_roots = boundary[..MAX_DA_ROOTS].to_vec();
        let mut extra = root.clone();
        extra.da_roots = boundary[MAX_DA_ROOTS..].to_vec();
        assert_eq!(
            aggregate(&[full, extra], vec![], vec![], &[], None, LOG_INV_RATE).unwrap_err(),
            AggregationError::TooLarge,
            "reject the oversized union before verifying the modified child statements"
        );
        let mut too_many = root;
        too_many.da_roots = boundary;
        assert_eq!(too_many.verify(), Err(AggregateVerifyError::MalformedDaCommitments));
    }

    #[test]
    fn invalid_blob_sizes_are_rejected() {
        for symbols in [1, BLOB_SYMBOLS - 1, BLOB_SYMBOLS + 1, (DA_MAX_ROWS + 1) * BLOB_SYMBOLS] {
            let rows = vec![0; symbols];
            assert!(matches!(
                aggregate(&[], vec![], vec![], &rows, None, LOG_INV_RATE),
                Err(AggregationError::InvalidBlobSize { symbols: n }) if n == symbols
            ));
        }
    }

    /// Powers of two and intermediate row counts use the same native guest.
    #[test]
    #[ignore = "Native DA proving is deferred; direct RV64IM execution exceeds proof capacity"]
    fn da_row_count_is_a_run_time_parameter() {
        parallel::init();
        let signers = get_signers(SMALL_LEAF_SIZE);
        for n_rows in [1usize, 3, 4, 5] {
            let rows = da_rows(n_rows, 200 + n_rows as u64);
            let node = aggregate(&[], at_epoch(&signers, XMSS_EPOCH_A), vec![], &rows, None, LOG_INV_RATE)
                .expect("node aggregates");
            node.verify().expect("node verifies");
            let (commitment, _) = lean_da::commit(&rows);
            assert_eq!(node.da_roots, vec![commitment.root], "{n_rows} rows");
        }
    }

    /// A leaf carrying no payload publishes the digest of an empty root list.
    #[test]
    fn no_payload_publishes_the_empty_root_list() {
        parallel::init();
        let signers = get_signers(SMALL_LEAF_SIZE);
        let node = prove_leaf(&signers);
        assert!(node.da_roots.is_empty());
        assert_eq!(node.da_commitments_digest(), primitives::hash::hash(&[]));
    }

    /// The same key can carry a distinct claim at each of many epochs.
    #[test]
    fn aggregate_many_epoch_groups() {
        parallel::init();
        let groups = 16;
        let raw: Vec<_> = (0..groups)
            .map(|i| {
                let epoch = KEY_START + i as xmss::Epoch;
                let (public_key, signature) = get_signers_at(1, epoch).remove(0);
                (public_key, epoch, message_for(epoch), signature)
            })
            .collect();
        let leaf = aggregate(&[], raw, vec![], &[], None, LOG_INV_RATE).expect("many-group leaf aggregates");
        leaf.verify().expect("it verifies");
        assert_eq!(leaf.xmss_signers.len(), groups);
        assert!(leaf.xmss_signers.iter().all(|group| group.keys.len() == 1));
    }

    /// Select whole groups and then individual keys without allowing rewidening.
    #[test]
    fn a_node_may_publish_less_than_it_covers() {
        parallel::init();
        let at_a = get_signers(3);
        let at_b = get_signers_at(2, XMSS_EPOCH_B);
        let mut raw = at_epoch(&at_a, XMSS_EPOCH_A);
        raw.extend(at_epoch(&at_b, XMSS_EPOCH_B));
        let wide = aggregate(&[], raw, vec![], &[], None, LOG_INV_RATE).expect("the wide leaf aggregates");
        wide.verify().expect("the wide leaf verifies");
        assert_eq!(wide.xmss_signers.len(), 2);
        assert_eq!(xmss_claims(&wide), 5);

        let narrowed = |wide: &EthereumProof, declare: &SignatureClaims| {
            aggregate(
                std::slice::from_ref(wide),
                vec![],
                vec![],
                &[],
                Some(ClaimSelection {
                    signatures: declare,
                    da_commitments: &[],
                }),
                LOG_INV_RATE,
            )
        };
        let (group_a, group_b) = (wide.xmss_signers[0].clone(), wide.xmss_signers[1].clone());

        // One group declared: the other's epoch and message go with it.
        let narrow = narrowed(
            &wide,
            &SignatureClaims {
                xmss: vec![group_b.clone()],
                sphincs: vec![],
            },
        )
        .expect("narrows to one group");
        narrow.verify().expect("the one-group narrowing verifies");
        assert_eq!(narrow.xmss_signers, vec![group_b.clone()]);

        // One key of one group: B goes whole, A keeps one of three.
        let one_of_a = XmssClaimGroup {
            epoch: XMSS_EPOCH_A,
            message: message(),
            keys: vec![group_a.keys[0].clone()],
        };
        let part = narrowed(
            &wide,
            &SignatureClaims {
                xmss: vec![one_of_a.clone()],
                sphincs: vec![],
            },
        )
        .expect("narrows to one key");
        part.verify().expect("the one-key narrowing verifies");
        assert_eq!(part.xmss_signers, vec![one_of_a]);

        assert_eq!(
            narrowed(&wide, &SignatureClaims::default()).err(),
            Some(AggregationError::Empty),
            "a declaration has to publish something"
        );
        // A key A holds and B does not, declared at B: the cache reuses keys.
        let only_at_a = group_a
            .keys
            .iter()
            .find(|key| !group_b.keys.contains(key))
            .expect("A holds a key B does not")
            .clone();
        assert_eq!(
            narrowed(
                &wide,
                &SignatureClaims {
                    xmss: vec![XmssClaimGroup {
                        epoch: XMSS_EPOCH_B,
                        message: message_for(XMSS_EPOCH_B),
                        keys: vec![only_at_a],
                    }],
                    sphincs: vec![],
                }
            )
            .err(),
            Some(AggregationError::NotCovered)
        );
        // A covered key, against another message.
        assert_eq!(
            narrowed(
                &wide,
                &SignatureClaims {
                    xmss: vec![XmssClaimGroup {
                        epoch: XMSS_EPOCH_A,
                        message: message_for(XMSS_EPOCH_B),
                        keys: group_a.keys.clone(),
                    }],
                    sphincs: vec![],
                }
            )
            .err(),
            Some(AggregationError::NotCovered)
        );

        // Putting the group back is a different signer set, whatever it covered.
        let mut rewidened = narrow.clone();
        rewidened.xmss_signers.insert(0, wide.xmss_signers[0].clone());
        assert!(
            rewidened.verify().is_err(),
            "a split may not be re-widened after the fact"
        );
    }

    #[test]
    fn raw_signatures_follow_the_table_not_the_epochs() {
        parallel::init();
        const _: () = assert!(XMSS_EPOCH_A < XMSS_EPOCH_B, "A must sort first for this to bite");
        let a = get_signers(1);
        let b = get_signers_at(1, XMSS_EPOCH_B);
        let mut raw = at_epoch(&a, XMSS_EPOCH_A);
        raw.extend(at_epoch(&b, XMSS_EPOCH_B));
        let group_b = XmssClaimGroup {
            epoch: XMSS_EPOCH_B,
            message: message_for(XMSS_EPOCH_B),
            keys: vec![b[0].0.clone()],
        };
        let sig = aggregate(
            &[],
            raw,
            vec![],
            &[],
            Some(ClaimSelection {
                signatures: &SignatureClaims {
                    xmss: vec![group_b.clone()],
                    sphincs: vec![],
                },
                da_commitments: &[],
            }),
            LOG_INV_RATE,
        )
        .expect("the narrowing leaf aggregates");
        sig.verify().expect("it verifies");
        assert_eq!(sig.xmss_signers, vec![group_b]);
    }

    #[test]
    fn aggregate_two_epochs() {
        parallel::init();
        let at_a = get_signers(4);
        let at_b = get_signers_at(2, XMSS_EPOCH_B);
        assert_eq!(at_a[0].0, at_b[0].0, "the cache reuses keys across epochs");
        let left = aggregate(&[], at_epoch(&at_a[..3], XMSS_EPOCH_A), vec![], &[], None, LOG_INV_RATE).expect("left");
        let mut right_raw = at_epoch(&at_a[2..], XMSS_EPOCH_A);
        right_raw.extend(at_epoch(&at_b, XMSS_EPOCH_B));
        let right = aggregate(&[], right_raw, vec![], &[], None, LOG_INV_RATE).expect("right");
        right.verify().expect("the two-epoch leaf verifies");
        // A claim at epoch A under B's message conflicts with `left`'s group:
        // within an aggregate the message is a function of the epoch.
        let (pk, _, _, sig) = at_epoch(&at_a[3..], XMSS_EPOCH_A).remove(0);
        assert_eq!(
            aggregate(
                std::slice::from_ref(&left),
                vec![(pk, XMSS_EPOCH_A, message_for(XMSS_EPOCH_B), sig)],
                vec![],
                &[],
                None,
                LOG_INV_RATE
            )
            .err(),
            Some(AggregationError::ConflictingMessages)
        );
        let node = aggregate(&[left, right], vec![], vec![], &[], None, LOG_INV_RATE).expect("node");
        node.verify().expect("the two-epoch node verifies");
        let messages: Vec<xmss::Message> = node.xmss_signers.iter().map(|group| group.message).collect();
        assert_eq!(messages, vec![message(), message_for(XMSS_EPOCH_B)]);
        let epochs: Vec<xmss::Epoch> = node.xmss_signers.iter().map(|group| group.epoch).collect();
        assert_eq!(epochs, vec![XMSS_EPOCH_A, XMSS_EPOCH_B]);
        assert_eq!(node.xmss_signers[0].keys.len(), 4);
        let mut b_keys: Vec<XmssPublicKey> = at_b.iter().map(|(pk, _)| pk.clone()).collect();
        b_keys.sort();
        assert_eq!(
            node.xmss_signers[1].keys, b_keys,
            "the same keys, at B, are their own claims"
        );
        // Statement tampers: no proving, the mutated aggregate just has to fail.
        let tampered = |mutate: &dyn Fn(&mut EthereumProof)| {
            let mut bad = node.clone();
            mutate(&mut bad);
            assert!(bad.verify().is_err(), "a tampered aggregate must not verify");
        };
        tampered(&|s| s.xmss_signers.swap(0, 1));
        tampered(&|s| s.xmss_signers[1].epoch = XMSS_EPOCH_B + 1);
        tampered(&|s| {
            let moved = s.xmss_signers[1].keys.pop().expect("a key to move");
            s.xmss_signers[0].keys.push(moved);
            s.xmss_signers[0].keys.sort();
            s.xmss_signers[0].keys.dedup();
        });
        tampered(&|s| {
            // Relabel group B's claims as group A's: B's keys are already among
            // A's, so this folds the two groups into one.
            let XmssClaimGroup { keys, .. } = s.xmss_signers.remove(1);
            s.xmss_signers[0].keys.extend(keys);
            s.xmss_signers[0].keys.sort();
            s.xmss_signers[0].keys.dedup();
        });
    }

    #[test]
    fn aggregate_overlapping_signers() {
        parallel::init();
        let signers = get_signers(40);
        let left = prove_leaf(&signers[..25]);
        let right = prove_leaf(&signers[15..]);
        let node = aggregate(&[left, right], vec![], vec![], &[], None, LOG_INV_RATE).expect("node aggregates");
        node.verify().expect("node verifies");
        assert_eq!(xmss_claims(&node), 40);
        assert!(node.xmss_signers[0].keys.windows(2).all(|w| w[0] < w[1]));
    }

    /// Three levels merge overlapping claims from both schemes and add raw claims at the root.
    #[test]
    #[ignore]
    fn aggregate_three_levels() {
        parallel::init();
        let signers = get_signers(4 * SMALL_LEAF_SIZE);
        let claims = get_sphincs_signers(5);
        let leaf = |index: usize, sphincs: &[RawSphincs]| {
            aggregate(
                &[],
                at_epoch(
                    &signers[index * SMALL_LEAF_SIZE..(index + 1) * SMALL_LEAF_SIZE],
                    XMSS_EPOCH_A,
                ),
                sphincs.to_vec(),
                &[],
                None,
                LOG_INV_RATE,
            )
            .expect("leaf aggregates")
        };
        let node = |children: &[EthereumProof]| {
            aggregate(children, vec![], vec![], &[], None, LOG_INV_RATE).expect("node aggregates")
        };
        // Claim 1 is under both nodes; claim 4 arrives raw at the root, and so
        // do two XMSS signatures at a second epoch, so the root holds a group
        // its children never carried.
        let left = node(&[leaf(0, &claims[..2]), leaf(1, &[])]);
        let right = node(&[leaf(2, &claims[1..3]), leaf(3, &[])]);
        let root = aggregate(
            &[left, right],
            at_epoch(&get_signers_at(2, XMSS_EPOCH_B), XMSS_EPOCH_B),
            claims[4..].to_vec(),
            &[],
            None,
            LOG_INV_RATE,
        )
        .expect("root aggregates");
        root.verify().expect("root verifies");
        assert_eq!(xmss_claims(&root), 4 * SMALL_LEAF_SIZE + 2);
        assert_eq!(root.xmss_signers.len(), 2, "the raw epoch-B group joins the children's");
        assert_eq!(root.sphincs_signers.len(), 4, "claims 0, 1, 2 and 4, the repeat merged");
        assert!(
            root.xmss_signers
                .iter()
                .all(|group| group.keys.windows(2).all(|w| w[0] < w[1]))
        );
        assert!(root.sphincs_signers.windows(2).all(|w| w[0] < w[1]));
    }

    #[test]
    #[ignore]
    fn aggregate_statement_binds() {
        parallel::init();
        let signers = get_signers(2 * SMALL_LEAF_SIZE);
        let left = prove_leaf(&signers[..SMALL_LEAF_SIZE]);
        let right = prove_leaf(&signers[SMALL_LEAF_SIZE..]);
        // Mixed, so both published lists are non-empty and every tampering
        // below has a SPHINCS counterpart.
        let node = aggregate(&[left, right], vec![], get_sphincs_signers(3), &[], None, LOG_INV_RATE).expect("node");
        node.verify().expect("the honest node verifies");

        assert_eq!(
            EthereumProof::from_bytes(&node.to_bytes())
                .expect("round trip")
                .to_bytes(),
            node.to_bytes(),
            "the wire format round-trips, recomputed claim values included"
        );
        let without = EthereumProof::from_bytes_without_pubkeys(
            &node.to_bytes_without_pubkeys(),
            SignatureClaims {
                xmss: node.xmss_signers.clone(),
                sphincs: node.sphincs_signers.clone(),
            },
        )
        .expect("round trip");
        without.verify().expect("a caller-supplied signer set verifies");

        let tampered = |mutate: &dyn Fn(&mut EthereumProof)| {
            let mut bad = node.clone();
            mutate(&mut bad);
            assert!(bad.verify().is_err(), "a tampered aggregate must not verify");
        };
        tampered(&|s| s.xmss_signers[0].keys[0] = s.xmss_signers[0].keys[1].clone());
        tampered(&|s| {
            s.xmss_signers[0].keys.swap(0, 1);
        });
        tampered(&|s| {
            s.xmss_signers[0].keys.pop();
        });
        tampered(&|s| s.sphincs_signers[0] = s.sphincs_signers[1]);
        tampered(&|s| {
            s.sphincs_signers.swap(0, 1);
        });
        tampered(&|s| {
            s.sphincs_signers.pop();
        });
        // Relabelling a signer's scheme: the same 32 bytes moved to the other
        // list. Every count and the splits between them are in the statement, and
        // the guest holds each region's writers to that region, so this is
        // not a free relabelling of what the aggregate claims.
        tampered(&|s| {
            let moved = s.xmss_signers[0].keys.remove(0);
            let claimed = (
                SphincsPublicKey::from_bytes(&moved.flatten()),
                s.xmss_signers[0].message,
            );
            s.sphincs_signers.push(claimed);
            s.sphincs_signers.sort();
        });
        tampered(&|s| s.xmss_signers[0].epoch += 1);
        tampered(&|s| s.xmss_signers[0].message[0] ^= 1);
        // A signer's own message is in the statement too, so editing it is not a
        // free re-attribution of that signature to another message.
        tampered(&|s| s.sphincs_signers[0].1[0] ^= 1);
        tampered(&|s| s.xmss_signers[0].keys[0] = get_signers(2 * SMALL_LEAF_SIZE + 1)[2 * SMALL_LEAF_SIZE].0.clone());
        // Splitting one group's keys across two epochs: the same claims cannot
        // be re-attributed to an epoch nothing signed at.
        tampered(&|s| {
            let moved = s.xmss_signers[0].keys.pop().expect("a key to move");
            let epoch = s.xmss_signers[0].epoch;
            let message = s.xmss_signers[0].message;
            s.xmss_signers.push(XmssClaimGroup {
                epoch: epoch + 1,
                message,
                keys: vec![moved],
            });
        });

        let mut trailing = node.to_bytes();
        trailing.push(0);
        assert!(EthereumProof::from_bytes(&trailing).is_err());
        let mut trailing = node.to_bytes_without_pubkeys();
        trailing.push(0);
        assert!(
            EthereumProof::from_bytes_without_pubkeys(
                &trailing,
                SignatureClaims {
                    xmss: node.xmss_signers.clone(),
                    sphincs: node.sphincs_signers.clone(),
                }
            )
            .is_err()
        );
    }

    #[test]
    #[ignore]
    fn aggregate_rejects_a_bad_signature() {
        parallel::init();
        let mut raw_signatures = at_epoch(&get_signers(3), XMSS_EPOCH_A);
        raw_signatures[1].3.wots_signature.chain_tips[0][0] ^= 1;
        let built = std::panic::catch_unwind(|| {
            aggregate(&[], raw_signatures, vec![], &[], None, LOG_INV_RATE).map(|signature| signature.verify().is_ok())
        });
        assert!(
            !matches!(built, Ok(Ok(true))),
            "a forged signature must not produce a verifying aggregate"
        );

        let mut raw_sphincs = get_sphincs_signers(2);
        raw_sphincs[1].2.ots[2][0][0] ^= 1;
        let built = std::panic::catch_unwind(|| {
            aggregate(&[], vec![], raw_sphincs, &[], None, LOG_INV_RATE).map(|signature| signature.verify().is_ok())
        });
        assert!(
            !matches!(built, Ok(Ok(true))),
            "a forged SPHINCS signature must not produce a verifying aggregate"
        );
    }

    /// Invalid XMSS randomness returns a typed error rather than panicking.
    #[test]
    fn malformed_raw_signature_is_an_error() {
        let message = message();
        let pk = XmssPublicKey {
            merkle_root: [0; xmss::DIGEST_LEN],
            public_param: [0; xmss::PUBLIC_PARAM_LEN],
        };
        let randomness = (0..=u8::MAX)
            .find_map(|byte| {
                let mut randomness = [0; xmss::RANDOMNESS_LEN];
                randomness[0] = byte;
                xmss::wots_encode(&message, XMSS_EPOCH_A, &pk.public_param, &randomness)
                    .is_none()
                    .then_some(randomness)
            })
            .expect("some randomness fails the target sum");
        let sig = XmssSignature {
            wots_signature: xmss::WotsSignature {
                chain_tips: [[0; xmss::DIGEST_LEN]; xmss::V],
                randomness,
            },
            merkle_proof: [[0; xmss::DIGEST_LEN]; xmss::LOG_LIFETIME],
        };

        assert_eq!(
            aggregate(
                &[],
                vec![(pk, XMSS_EPOCH_A, message, sig)],
                vec![],
                &[],
                None,
                LOG_INV_RATE
            )
            .err(),
            Some(AggregationError::MalformedRawSignature)
        );
    }

    /// Invalid SPHINCS counters return a typed error rather than panicking.
    #[test]
    fn malformed_raw_sphincs_signature_is_an_error() {
        let (public_key, signed, mut signature) = get_sphincs_signers(1).pop().expect("one signer");
        signature.counters[sphincs::D - 1] ^= 1;
        assert!(sphincs::verify(&public_key, &signed, &signature).is_err());
        let raw = vec![(public_key, signed, signature)];
        assert_eq!(
            aggregate(&[], vec![], raw, &[], None, LOG_INV_RATE).err(),
            Some(AggregationError::MalformedRawSignature)
        );
    }

    /// Execute the compiled guest directly, bypassing all host preflight checks.
    fn execute_input(image: &GuestImage, input: &guest::Input) -> Result<(), String> {
        let public = guest::public_input(&input.statement, &input.children).map_err(|e| e.to_string())?;
        let witness = input.to_witness().map_err(|e| e.to_string())?;
        image
            .program
            .execute(public, &witness, u64::MAX)
            .map_err(|e| e.to_string())?;
        Ok(())
    }

    #[test]
    fn aggregate_witness_binds_raw_signatures_and_declared_claims() {
        let (image, input) = build_input(
            &[],
            at_epoch(&get_signers(2), XMSS_EPOCH_A),
            get_sphincs_signers(1),
            None,
            DaInput::default(),
            LOG_INV_RATE,
        )
        .unwrap();
        execute_input(&image, &input).unwrap();
        let rejects = |change: &dyn Fn(&mut guest::Input)| {
            let mut forged = input.clone();
            change(&mut forged);
            assert!(execute_input(&image, &forged).is_err());
        };
        rejects(&|i| i.xmss[0].signature[0] ^= 1);
        rejects(&|i| i.xmss[0].signature[1207] ^= 1);
        rejects(&|i| i.xmss[0].message[0] ^= 1);
        rejects(&|i| i.xmss[0].epoch += 1);
        rejects(&|i| i.sphincs[0].signature[100] ^= 1);
        rejects(&|i| i.sphincs[0].message[0] ^= 1);
        // Changing the public statement itself must still fail coverage.
        rejects(&|i| i.statement.xmss[0].message[0] ^= 1);
        rejects(&|i| {
            i.statement.xmss[0].keys[0][0] ^= 1;
            i.statement.xmss[0].keys.sort();
        });
        rejects(&|i| i.statement.sphincs[0].message[0] ^= 1);
        rejects(&|i| {
            let key = i.statement.xmss[0].keys.remove(0);
            i.statement.sphincs.push(guest::SphincsClaim {
                key,
                message: i.statement.xmss[0].message,
            });
            i.statement.sphincs.sort();
        });
        rejects(&|i| {
            i.xmss.push(i.xmss[0].clone());
            i.xmss.last_mut().unwrap().signature[0] ^= 1;
        });
        rejects(&|i| {
            i.statement.xmss.clear();
            i.xmss[0].signature[0] ^= 1;
        });
        rejects(&|i| {
            i.statement.sphincs.clear();
            i.sphincs[0].signature[0] ^= 1;
        });
        let public = guest::public_input(&input.statement, &input.children).unwrap();
        let mut payload = input.to_bytes().unwrap();
        payload.push(0);
        let mut framed = (payload.len() as u64).to_le_bytes().to_vec();
        framed.extend_from_slice(&payload);
        assert!(image.program.execute(public, &framed, u64::MAX).is_err());
    }

    #[test]
    fn native_recursion_authenticates_complete_child_statements() {
        let child = aggregate(
            &[],
            at_epoch(&get_signers(1), XMSS_EPOCH_A),
            get_sphincs_signers(1),
            &[],
            None,
            LOG_INV_RATE,
        )
        .unwrap();
        let selected = SignatureClaims {
            xmss: child.xmss_signers.clone(),
            sphincs: vec![],
        };
        let (image, input) = build_input(
            std::slice::from_ref(&child),
            vec![],
            vec![],
            Some(&selected),
            DaInput {
                rows: &[],
                roots: Some(&[]),
            },
            LOG_INV_RATE,
        )
        .unwrap();
        let recursor = recursor(&image).unwrap();
        let parent = prove_node(
            &image,
            &recursor,
            input.clone(),
            &[&child],
            LOG_INV_RATE,
            &mut AggregateStats::default(),
        )
        .unwrap();
        parent.verify().unwrap();
        // Recompute the execution public input after each forgery. The native
        // circuit, not a host precheck, must bind even omitted child metadata.
        for change in [
            (|i: &mut guest::Input| i.children[0].statement.sphincs[0].message[0] ^= 1) as fn(&mut guest::Input),
            |i| i.children[0].statement.da_roots.push([42; 32]),
            |i| i.children[0].statement.xmss[0].epoch += 1,
            |i| i.children[0].key[0] ^= 1,
            |i| i.children[0].height += 1,
        ] {
            let mut forged = input.clone();
            change(&mut forged);
            assert!(
                prove_node(
                    &image,
                    &recursor,
                    forged,
                    &[&child],
                    LOG_INV_RATE,
                    &mut AggregateStats::default()
                )
                .is_err()
            );
        }
        // Keep the guest metadata valid while replacing the actual native proof.
        let mut forged_child = child.clone();
        forged_child.proof.proof.stream.clear();
        assert!(
            prove_node(
                &image,
                &recursor,
                input.clone(),
                &[&forged_child],
                LOG_INV_RATE,
                &mut AggregateStats::default()
            )
            .is_err()
        );
        // Removing or duplicating a verifier input cannot match the guest list.
        for children in [vec![], vec![&child, &child]] {
            assert!(
                prove_node(
                    &image,
                    &recursor,
                    input.clone(),
                    &children,
                    LOG_INV_RATE,
                    &mut AggregateStats::default()
                )
                .is_err()
            );
        }
    }

    #[test]
    fn da_guest_checks_commitment_and_codewords() {
        let rows = da_rows(3, 101);
        let (image, input) = build_input(
            &[],
            vec![],
            vec![],
            None,
            DaInput {
                rows: &rows,
                roots: None,
            },
            LOG_INV_RATE,
        )
        .unwrap();
        execute_input(&image, &input).unwrap();
        let mut forged = input.clone();
        forged.da.as_mut().unwrap().membership_digest[0] ^= 1;
        assert!(execute_input(&image, &forged).is_err());
        // Recommit corrupted data, so only Reed-Solomon membership can reject.
        for position in [0, BLOB_SYMBOLS, 3 * lean_da::CODEWORD_SYMBOLS - 1] {
            let mut words = lean_da::encode_rows(&rows);
            words[position] ^= 1;
            let root = lean_da::commit_codewords(words.clone()).0.root;
            let mut forged = input.clone();
            forged.statement.da_roots = vec![root];
            forged.da = Some(guest::DirectDa {
                root,
                membership_digest: lean_da::vector_digest(&lean_da::membership_vector(&root)),
                codewords_le: words.into_iter().flat_map(u64::to_le_bytes).collect(),
            });
            assert!(execute_input(&image, &forged).is_err());
        }
        // Truncation cannot silently change a three-row commitment to two rows.
        let mut forged = input.clone();
        forged
            .da
            .as_mut()
            .unwrap()
            .codewords_le
            .truncate(2 * lean_da::CODEWORD_SYMBOLS * 8);
        assert!(execute_input(&image, &forged).is_err());
    }

    #[test]
    fn wire_rejects_wrong_claims_and_noncanonical_encodings() {
        let proof = prove_leaf(&get_signers(1));
        let claims = SignatureClaims {
            xmss: proof.xmss_signers.clone(),
            sphincs: vec![],
        };
        let compact = proof.to_bytes_without_pubkeys();
        EthereumProof::from_bytes_without_pubkeys(&compact, claims.clone())
            .unwrap()
            .verify()
            .unwrap();
        let mut wrong = claims;
        wrong.xmss[0].message[0] ^= 1;
        assert!(
            EthereumProof::from_bytes_without_pubkeys(&compact, wrong)
                .unwrap()
                .verify()
                .is_err()
        );
        let encoded = proof.to_bytes();
        assert_eq!(EthereumProof::from_bytes(&encoded).unwrap().to_bytes(), encoded);
        for cut in [0, 7, encoded.len() - 1] {
            assert!(EthereumProof::from_bytes(&encoded[..cut]).is_err());
        }
        let mut trailing = encoded;
        trailing.push(0);
        assert!(EthereumProof::from_bytes(&trailing).is_err());
        let malformed: WireFull = (WIRE_FULL, vec![0xff; 32], proof.proof.to_bytes());
        assert!(EthereumProof::from_bytes(&wire().serialize(&malformed).unwrap()).is_err());
        let legacy: WireFull = (
            *b"RVAGG001",
            proof.statement().to_bytes().unwrap(),
            proof.proof.to_bytes(),
        );
        assert!(EthereumProof::from_bytes(&wire().serialize(&legacy).unwrap()).is_err());
        let mut height = proof.clone();
        height.proof.height += 1;
        assert!(height.verify().is_err());
        let mut extra = proof.proof.to_bytes();
        extra.push(0);
        let malformed: WireFull = (WIRE_FULL, proof.statement().to_bytes().unwrap(), extra);
        assert!(EthereumProof::from_bytes(&wire().serialize(&malformed).unwrap()).is_err());
    }

    #[test]
    fn every_raw_signature_is_checked_before_deduplication() {
        let raw = at_epoch(&get_signers(1), XMSS_EPOCH_A);
        let mut duplicate = raw[0].clone();
        duplicate.3.wots_signature.chain_tips[0][0] ^= 1;
        let mut inputs = raw;
        inputs.push(duplicate);
        assert_eq!(
            aggregate(&[], inputs, vec![], &[], None, LOG_INV_RATE).unwrap_err(),
            AggregationError::MalformedRawSignature
        );
        let mut raw = get_sphincs_signers(1);
        let mut duplicate = raw[0].clone();
        duplicate.2.ots[0][0][0] ^= 1;
        raw.push(duplicate);
        assert_eq!(
            aggregate(&[], vec![], raw, &[], None, LOG_INV_RATE).unwrap_err(),
            AggregationError::MalformedRawSignature
        );
    }

    #[test]
    #[ignore = "Native DA proving is deferred; direct RV64IM execution exceeds proof capacity"]
    fn da_blob_proof() {
        for n_rows in [1, 6, 14, 32] {
            crate::benchmark::run_aggregation(0, 0, n_rows, LOG_INV_RATE, primitives::bench::Plan::default());
        }
    }
}
