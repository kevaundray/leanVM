#![no_std]
//! Canonical claims and RV64IM execution-side aggregation checks.
//!
//! Child claims are deferred: this guest binds their exact ordered metadata, but
//! does not authenticate child proofs. Its execution proof must be verified by
//! native recursion together with the child proofs bound into the public input.

extern crate alloc;

use alloc::vec::Vec;
use leanvm_guest::{Hasher, deferred};

pub const MAX_EPOCHS: usize = 1024;
/// Exclusive cap, including duplicate and unpublished contributions.
pub const MAX_KEYS: usize = 65536;
pub const MAX_DA_ROOTS: usize = 16;
/// External aggregation fan-in; each native recursion node has at most two children.
pub const MAX_RECURSIONS: usize = 16;
/// Internal nodes publish every input root before the final public selection.
/// Binary folding must retain up to sixteen external children's sixteen roots
/// each, plus one direct DA root, even when the final statement selects fewer.
pub const MAX_STATEMENT_DA_ROOTS: usize = MAX_DA_ROOTS * MAX_RECURSIONS + 1;
pub const MAX_INPUT_BYTES: usize = 1 << 30;
pub const XMSS_SIGNATURE_BYTES: usize = 1208;
pub const SPHINCS_SIGNATURE_BYTES: usize = 4924;
const MAX_DA_BYTES: usize = 1024 * 32768 * 8;
const DA_ROW_BYTES: usize = 32768 * 8;
const DOMAIN: &[u8] = b"leanVM/RV64IM/aggregation/statement/v1\0";
const INPUT_MAGIC: &[u8; 8] = b"RVAGG002";

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Statement {
    pub xmss: Vec<XmssGroup>,
    pub sphincs: Vec<SphincsClaim>,
    pub da_roots: Vec<[u8; 32]>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct XmssGroup {
    pub epoch: u32,
    pub message: [u8; 32],
    pub keys: Vec<[u8; 32]>,
}

/// Ordering is lexicographic on the entire (key, message) pair.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SphincsClaim {
    pub key: [u8; 32],
    pub message: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Child {
    pub statement: Statement,
    pub key: [u8; 32],
    pub height: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawXmss {
    pub epoch: u32,
    pub message: [u8; 32],
    pub key: [u8; 32],
    pub signature: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawSphincs {
    pub message: [u8; 32],
    pub key: [u8; 32],
    pub signature: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DirectDa {
    pub root: [u8; 32],
    pub membership_digest: [u8; 32],
    /// Complete encoded rows, each 32768 little-endian u64 symbols.
    pub codewords_le: Vec<u8>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Input {
    pub statement: Statement,
    pub children: Vec<Child>,
    pub xmss: Vec<RawXmss>,
    pub sphincs: Vec<RawSphincs>,
    pub da: Option<DirectDa>,
}

#[derive(Debug)]
pub enum Error {
    Truncated,
    TrailingBytes,
    InvalidEncoding,
    TooLarge,
    Allocation,
    EmptyStatement,
    NonCanonicalStatement,
    ConflictingMessages,
    NotCovered,
    PublicInputMismatch,
    Claims(leanvm_guest_claims::Error),
}

impl From<leanvm_guest_claims::Error> for Error {
    fn from(error: leanvm_guest_claims::Error) -> Self {
        Self::Claims(error)
    }
}
impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Claims(error) => write!(f, "claim verification: {error}"),
            other => write!(f, "{other:?}"),
        }
    }
}
impl core::error::Error for Error {}

fn bounded_add(total: &mut usize, count: usize) -> Result<(), Error> {
    *total = total.checked_add(count).ok_or(Error::TooLarge)?;
    if *total >= MAX_KEYS {
        return Err(Error::TooLarge);
    }
    Ok(())
}

fn reserve<T>(values: &mut Vec<T>, additional: usize) -> Result<(), Error> {
    values.try_reserve_exact(additional).map_err(|_| Error::Allocation)
}

impl Statement {
    pub fn validate(&self) -> Result<(), Error> {
        if self.xmss.len() > MAX_EPOCHS || self.da_roots.len() > MAX_STATEMENT_DA_ROOTS {
            return Err(Error::TooLarge);
        }
        let mut count = 0;
        bounded_add(&mut count, self.sphincs.len())?;
        bounded_add(&mut count, self.da_roots.len())?;
        for group in &self.xmss {
            bounded_add(&mut count, group.keys.len())?;
            if group.keys.is_empty() || group.keys.windows(2).any(|pair| pair[0] >= pair[1]) {
                return Err(Error::NonCanonicalStatement);
            }
        }
        if self.xmss.windows(2).any(|pair| pair[0].epoch >= pair[1].epoch)
            || self.sphincs.windows(2).any(|pair| pair[0] >= pair[1])
            || self.da_roots.windows(2).any(|pair| pair[0] >= pair[1])
        {
            return Err(Error::NonCanonicalStatement);
        }
        if count == 0 {
            return Err(Error::EmptyStatement);
        }
        Ok(())
    }

    pub fn to_bytes(&self) -> Result<Vec<u8>, Error> {
        self.validate()?;
        let mut encoder = Encoder::new();
        encode_statement(&mut encoder, self)?;
        Ok(encoder.bytes)
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        let mut decoder = Decoder::new(bytes)?;
        let statement = decoder.statement()?;
        statement.validate()?;
        decoder.finish()?;
        Ok(statement)
    }

    /// Hash the canonical statement encoding without allocating a second buffer.
    pub fn digest(&self) -> Result<[u8; 32], Error> {
        self.validate()?;
        self.digest_canonical()
    }

    fn digest_canonical(&self) -> Result<[u8; 32], Error> {
        let mut hasher = Hasher::new();
        hasher.update(DOMAIN);
        encode_statement(&mut hasher, self)?;
        Ok(hasher.finalize())
    }

    fn count(&self) -> usize {
        self.xmss.iter().map(|group| group.keys.len()).sum::<usize>() + self.sphincs.len() + self.da_roots.len()
    }
}

/// Bind the statement and exact ordered child metadata for native recursion.
///
/// This digest is an execution public input, not evidence of child proof validity.
pub fn public_input(statement: &Statement, children: &[Child]) -> Result<[u8; 32], Error> {
    if children.len() > deferred::MAX_CHILDREN {
        return Err(Error::TooLarge);
    }
    for child in children {
        child.statement.validate()?;
    }
    statement.validate()?;
    public_input_canonical(statement, children)
}

fn public_input_canonical(statement: &Statement, children: &[Child]) -> Result<[u8; 32], Error> {
    let mut claims = [deferred::Claim::default(); deferred::MAX_CHILDREN];
    for (claim, child) in claims.iter_mut().zip(children) {
        *claim = deferred::Claim {
            statement: child.statement.digest_canonical()?,
            key: child.key,
            height: child.height,
        };
    }
    Ok(deferred::binding(
        statement.digest_canonical()?,
        &claims[..children.len()],
    ))
}

trait Sink {
    fn bytes(&mut self, bytes: &[u8]) -> Result<(), Error>;
    fn count(&mut self, count: usize) -> Result<(), Error> {
        self.bytes(&u32::try_from(count).map_err(|_| Error::TooLarge)?.to_le_bytes())
    }
}
impl Sink for Hasher {
    fn bytes(&mut self, bytes: &[u8]) -> Result<(), Error> {
        self.update(bytes);
        Ok(())
    }
}
struct Encoder {
    bytes: Vec<u8>,
}
impl Encoder {
    fn new() -> Self {
        Self { bytes: Vec::new() }
    }
    fn blob(&mut self, bytes: &[u8]) -> Result<(), Error> {
        self.count(bytes.len())?;
        self.bytes(bytes)
    }
}
impl Sink for Encoder {
    fn bytes(&mut self, bytes: &[u8]) -> Result<(), Error> {
        if bytes.len() > MAX_INPUT_BYTES - self.bytes.len() {
            return Err(Error::TooLarge);
        }
        self.bytes.try_reserve(bytes.len()).map_err(|_| Error::Allocation)?;
        self.bytes.extend_from_slice(bytes);
        Ok(())
    }
}
fn encode_statement(sink: &mut impl Sink, statement: &Statement) -> Result<(), Error> {
    sink.count(statement.xmss.len())?;
    for group in &statement.xmss {
        sink.bytes(&group.epoch.to_le_bytes())?;
        sink.bytes(&group.message)?;
        sink.count(group.keys.len())?;
        sink.bytes(group.keys.as_flattened())?;
    }
    sink.count(statement.sphincs.len())?;
    for claim in &statement.sphincs {
        sink.bytes(&claim.key)?;
        sink.bytes(&claim.message)?;
    }
    sink.count(statement.da_roots.len())?;
    sink.bytes(statement.da_roots.as_flattened())?;
    Ok(())
}

struct Decoder<'a> {
    bytes: &'a [u8],
}
impl<'a> Decoder<'a> {
    fn new(bytes: &'a [u8]) -> Result<Self, Error> {
        if bytes.len() > MAX_INPUT_BYTES {
            return Err(Error::TooLarge);
        }
        Ok(Self { bytes })
    }
    fn take(&mut self, count: usize) -> Result<&'a [u8], Error> {
        let (value, rest) = self.bytes.split_at_checked(count).ok_or(Error::Truncated)?;
        self.bytes = rest;
        Ok(value)
    }
    fn array<const N: usize>(&mut self) -> Result<[u8; N], Error> {
        let mut out = [0; N];
        out.copy_from_slice(self.take(N)?);
        Ok(out)
    }
    fn u32(&mut self) -> Result<u32, Error> {
        Ok(u32::from_le_bytes(self.array()?))
    }
    /// Check both the protocol cap and a minimum wire size before any allocation.
    fn count(&mut self, max: usize, element_min: usize) -> Result<usize, Error> {
        let count = self.u32()? as usize;
        if count > max {
            return Err(Error::TooLarge);
        }
        if count > self.bytes.len() / element_min {
            return Err(Error::Truncated);
        }
        Ok(count)
    }
    fn blob(&mut self, max: usize) -> Result<Vec<u8>, Error> {
        let count = self.count(max, 1)?;
        let source = self.take(count)?;
        let mut value = Vec::new();
        reserve(&mut value, count)?;
        value.extend_from_slice(source);
        Ok(value)
    }
    fn signature(&mut self, length: usize) -> Result<Vec<u8>, Error> {
        let signature = self.blob(length)?;
        if signature.len() != length {
            return Err(Error::InvalidEncoding);
        }
        Ok(signature)
    }
    fn statement(&mut self) -> Result<Statement, Error> {
        let count = self.count(MAX_EPOCHS, 72)?;
        let mut statement = Statement::default();
        reserve(&mut statement.xmss, count)?;
        let mut total = 0;
        for _ in 0..count {
            let epoch = self.u32()?;
            let message = self.array()?;
            let keys_len = self.count(MAX_KEYS - 1, 32)?;
            bounded_add(&mut total, keys_len)?;
            let mut keys = Vec::new();
            reserve(&mut keys, keys_len)?;
            keys.extend_from_slice(self.take(keys_len * 32)?.as_chunks::<32>().0);
            statement.xmss.push(XmssGroup { epoch, message, keys });
        }
        let count = self.count(MAX_KEYS - 1, 64)?;
        bounded_add(&mut total, count)?;
        reserve(&mut statement.sphincs, count)?;
        for _ in 0..count {
            statement.sphincs.push(SphincsClaim {
                key: self.array()?,
                message: self.array()?,
            });
        }
        let count = self.count(MAX_STATEMENT_DA_ROOTS, 32)?;
        bounded_add(&mut total, count)?;
        reserve(&mut statement.da_roots, count)?;
        statement
            .da_roots
            .extend_from_slice(self.take(count * 32)?.as_chunks::<32>().0);
        Ok(statement)
    }
    fn finish(self) -> Result<(), Error> {
        if self.bytes.is_empty() {
            Ok(())
        } else {
            Err(Error::TrailingBytes)
        }
    }
}

impl Input {
    /// Encode only the payload. All lengths inside it are little-endian u32.
    pub fn to_bytes(&self) -> Result<Vec<u8>, Error> {
        self.validate_shape()?;
        let mut encoder = Encoder::new();
        encoder.bytes(INPUT_MAGIC)?;
        encode_statement(&mut encoder, &self.statement)?;
        encoder.count(self.children.len())?;
        for child in &self.children {
            encode_statement(&mut encoder, &child.statement)?;
            encoder.bytes(&child.key)?;
            encoder.bytes(&child.height.to_le_bytes())?;
        }
        encoder.count(self.xmss.len())?;
        for raw in &self.xmss {
            encoder.bytes(&raw.epoch.to_le_bytes())?;
            encoder.bytes(&raw.message)?;
            encoder.bytes(&raw.key)?;
            encoder.blob(&raw.signature)?;
        }
        encoder.count(self.sphincs.len())?;
        for raw in &self.sphincs {
            encoder.bytes(&raw.message)?;
            encoder.bytes(&raw.key)?;
            encoder.blob(&raw.signature)?;
        }
        encoder.count(usize::from(self.da.is_some()))?;
        if let Some(da) = &self.da {
            encoder.bytes(&da.root)?;
            encoder.bytes(&da.membership_digest)?;
            encoder.blob(&da.codewords_le)?;
        }
        Ok(encoder.bytes)
    }

    /// Complete guest witness stream: u64 payload length followed by the payload.
    pub fn to_witness(&self) -> Result<Vec<u8>, Error> {
        let mut payload = self.to_bytes()?;
        let length = (payload.len() as u64).to_le_bytes();
        reserve(&mut payload, 8)?;
        let old_len = payload.len();
        payload.resize(old_len + 8, 0);
        payload.copy_within(..old_len, 8);
        payload[..8].copy_from_slice(&length);
        Ok(payload)
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        let mut decoder = Decoder::new(bytes)?;
        if decoder.take(INPUT_MAGIC.len())? != INPUT_MAGIC {
            return Err(Error::InvalidEncoding);
        }
        let statement = decoder.statement()?;
        let mut input = Self {
            statement,
            ..Self::default()
        };
        let children_len = decoder.count(deferred::MAX_CHILDREN, 80)?;
        reserve(&mut input.children, children_len)?;
        let mut total = 0;
        for _ in 0..children_len {
            let statement = decoder.statement()?;
            bounded_add(&mut total, statement.count())?;
            let key = decoder.array()?;
            let height = decoder.u32()?;
            input.children.push(Child { statement, key, height });
        }
        let count = decoder.count(MAX_KEYS - 1, 72 + XMSS_SIGNATURE_BYTES)?;
        bounded_add(&mut total, count)?;
        reserve(&mut input.xmss, count)?;
        for _ in 0..count {
            input.xmss.push(RawXmss {
                epoch: decoder.u32()?,
                message: decoder.array()?,
                key: decoder.array()?,
                signature: decoder.signature(XMSS_SIGNATURE_BYTES)?,
            });
        }
        let count = decoder.count(MAX_KEYS - 1, 68 + SPHINCS_SIGNATURE_BYTES)?;
        bounded_add(&mut total, count)?;
        reserve(&mut input.sphincs, count)?;
        for _ in 0..count {
            input.sphincs.push(RawSphincs {
                message: decoder.array()?,
                key: decoder.array()?,
                signature: decoder.signature(SPHINCS_SIGNATURE_BYTES)?,
            });
        }
        match decoder.u32()? {
            0 => {}
            1 => {
                bounded_add(&mut total, 1)?;
                input.da = Some(DirectDa {
                    root: decoder.array()?,
                    membership_digest: decoder.array()?,
                    codewords_le: decoder.blob(MAX_DA_BYTES)?,
                });
            }
            _ => return Err(Error::InvalidEncoding),
        }
        decoder.finish()?;
        input.validate_shape()?;
        Ok(input)
    }

    fn validate_shape(&self) -> Result<usize, Error> {
        self.statement.validate()?;
        if self.children.len() > deferred::MAX_CHILDREN {
            return Err(Error::TooLarge);
        }
        let mut total = 0;
        bounded_add(&mut total, self.xmss.len())?;
        bounded_add(&mut total, self.sphincs.len())?;
        bounded_add(&mut total, usize::from(self.da.is_some()))?;
        for child in &self.children {
            child.statement.validate()?;
            bounded_add(&mut total, child.statement.count())?;
        }
        if self.xmss.iter().any(|raw| raw.signature.len() != XMSS_SIGNATURE_BYTES)
            || self
                .sphincs
                .iter()
                .any(|raw| raw.signature.len() != SPHINCS_SIGNATURE_BYTES)
        {
            return Err(Error::InvalidEncoding);
        }
        if let Some(da) = &self.da
            && (da.codewords_le.is_empty()
                || da.codewords_le.len() > MAX_DA_BYTES
                || da.codewords_le.len() % DA_ROW_BYTES != 0)
        {
            return Err(Error::InvalidEncoding);
        }
        Ok(total)
    }
}

struct XmssSupport<'a> {
    epoch: u32,
    message: &'a [u8; 32],
    keys: &'a [[u8; 32]],
}

/// Raw verified contributions and bound child claims deferred to native recursion.
#[derive(Default)]
struct Coverage<'a> {
    xmss: Vec<XmssSupport<'a>>,
    sphincs: Vec<(&'a [u8; 32], &'a [u8; 32])>,
    roots: Vec<&'a [u8; 32]>,
}
impl<'a> Coverage<'a> {
    fn statement(&mut self, statement: &'a Statement) -> Result<(), Error> {
        reserve(&mut self.xmss, statement.xmss.len())?;
        self.xmss.extend(statement.xmss.iter().map(|group| XmssSupport {
            epoch: group.epoch,
            message: &group.message,
            keys: &group.keys,
        }));
        reserve(&mut self.sphincs, statement.sphincs.len())?;
        self.sphincs
            .extend(statement.sphincs.iter().map(|claim| (&claim.key, &claim.message)));
        reserve(&mut self.roots, statement.da_roots.len())?;
        self.roots.extend(statement.da_roots.iter());
        Ok(())
    }

    fn check(mut self, declared: &Statement) -> Result<(), Error> {
        self.xmss.sort_unstable_by_key(|support| support.epoch);
        let mut epochs = 0;
        let mut previous: Option<(u32, &[u8; 32])> = None;
        for support in &self.xmss {
            let (epoch, message) = (support.epoch, support.message);
            match previous {
                Some((last_epoch, last_message)) if last_epoch == epoch => {
                    if message != last_message {
                        return Err(Error::ConflictingMessages);
                    }
                }
                _ => {
                    epochs += 1;
                    if epochs > MAX_EPOCHS {
                        return Err(Error::TooLarge);
                    }
                    previous = Some((epoch, message));
                }
            }
        }
        self.sphincs.sort_unstable();
        self.roots.sort_unstable();
        self.roots.dedup();
        for group in &declared.xmss {
            let start = self.xmss.partition_point(|support| support.epoch < group.epoch);
            let end = start + self.xmss[start..].partition_point(|support| support.epoch == group.epoch);
            let available = &mut self.xmss[start..end];
            if available
                .first()
                .is_none_or(|support| support.message != &group.message)
            {
                return Err(Error::NotCovered);
            }
            for key in &group.keys {
                if !available.iter_mut().any(|support| {
                    while let Some((candidate, rest)) = support.keys.split_first() {
                        match candidate.cmp(key) {
                            core::cmp::Ordering::Less => support.keys = rest,
                            core::cmp::Ordering::Equal => {
                                support.keys = rest;
                                return true;
                            }
                            core::cmp::Ordering::Greater => return false,
                        }
                    }
                    false
                }) {
                    return Err(Error::NotCovered);
                }
            }
        }
        let mut available = self.sphincs.into_iter();
        for claim in &declared.sphincs {
            loop {
                let Some(candidate) = available.next() else {
                    return Err(Error::NotCovered);
                };
                match candidate.cmp(&(&claim.key, &claim.message)) {
                    core::cmp::Ordering::Less => {}
                    core::cmp::Ordering::Equal => break,
                    core::cmp::Ordering::Greater => return Err(Error::NotCovered),
                }
            }
        }
        if declared
            .da_roots
            .iter()
            .any(|root| self.roots.binary_search(&root).is_err())
        {
            return Err(Error::NotCovered);
        }
        Ok(())
    }
}

/// Check raw claims, coverage and all deferred metadata, including unpublished claims.
///
/// The caller supplies the public input bound by the RV64IM proof instance.
/// Success alone does not authenticate child claims: native recursion must verify
/// that execution proof and every child proof under the keys and heights bound here.
pub fn verify_input(input: &Input, public: [u8; 32]) -> Result<(), Error> {
    input.validate_shape()?;
    verify_canonical_input(input, public)
}

fn verify_canonical_input(input: &Input, public: [u8; 32]) -> Result<(), Error> {
    if public_input_canonical(&input.statement, &input.children)? != public {
        return Err(Error::PublicInputMismatch);
    }
    let mut coverage = Coverage::default();
    for child in &input.children {
        coverage.statement(&child.statement)?;
    }
    reserve(&mut coverage.xmss, input.xmss.len())?;
    for raw in &input.xmss {
        leanvm_guest_claims::xmss::verify(&raw.key, &raw.message, &raw.signature, raw.epoch)?;
        coverage.xmss.push(XmssSupport {
            epoch: raw.epoch,
            message: &raw.message,
            keys: core::slice::from_ref(&raw.key),
        });
    }
    reserve(&mut coverage.sphincs, input.sphincs.len())?;
    for raw in &input.sphincs {
        leanvm_guest_claims::sphincs::verify(&raw.key, &raw.message, &raw.signature)?;
        coverage.sphincs.push((&raw.key, &raw.message));
    }
    if let Some(da) = &input.da {
        leanvm_guest_claims::da::verify_bytes(&da.codewords_le, &da.root, &da.membership_digest)?;
        reserve(&mut coverage.roots, 1)?;
        coverage.roots.push(&da.root);
    }
    coverage.check(&input.statement)
}

/// Read the framed witness and enforce execution-side checks for native recursion.
pub fn run_guest() -> Result<(), Error> {
    let mut length = [0; 8];
    leanvm_guest::read_witness_exact(&mut length);
    let length = u64::from_le_bytes(length);
    if length > MAX_INPUT_BYTES as u64 {
        return Err(Error::TooLarge);
    }
    let bytes = leanvm_guest::read_witness_vec(length as usize).map_err(|_| Error::Allocation)?;
    let input = Input::from_bytes(&bytes)?;
    drop(bytes);
    verify_canonical_input(&input, leanvm_guest::public_input())
}

#[cfg(test)]
mod tests;
