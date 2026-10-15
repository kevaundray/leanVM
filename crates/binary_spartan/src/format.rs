//! Strict parsers (and the matching encoders) for the two files a Clean export writes, both little-endian.
//!
//! Block R1CS (`circuit.r1cs`), `CLB1` for a block without links and `CLB2` for one with:
//!
//! ```text
//! magic "CLB1", u32 version = 1
//! u32 n_signals (signal 0 = constant one), u32 n_public (signals 1..=n_public), u32 n_constraints
//! per constraint, for A, B, C: u32 n_terms, then n_terms x u32 signal (strictly increasing)
//!
//! magic "CLB2", u32 version = 1
//! u32 n_signals, u32 n_public, u32 n_constraints, u32 n_link (at least 1)
//! n_link x (u32 in_signal, u32 out_signal)
//! the constraints as in CLB1
//! ```
//!
//! Link `j` asks `z_{i+1}[in_j] = z_i[out_j]` of consecutive instances. Both signals are private and distinct, and a
//! signal is the `in` of at most one link and the `out` of at most one.
//!
//! Batch witness (`witness.bin`):
//!
//! ```text
//! magic "CLW2", u32 version = 1
//! u32 n_signals, u32 n_instances
//! per instance: ceil(n_signals / 8) bytes, signal j at byte j/8 bit j%8; signal 0 = 1; spare bits zero
//! ```
//!
//! Anything else is rejected, so an accepted file has exactly one encoding and its BLAKE2s is a digest of the circuit.

use std::fmt;

const R1CS_MAGIC: &[u8; 4] = b"CLB1";
const LINKED_R1CS_MAGIC: &[u8; 4] = b"CLB2";
const WITNESS_MAGIC: &[u8; 4] = b"CLW2";
const VERSION: u32 = 1;
/// Upper bound on signals and constraints: a block is padded to at most `2^MAX_LOG` rows and columns.
pub const MAX_LOG: usize = 26;

/// Why a file was rejected.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FormatError {
    BadMagic,
    BadVersion(u32),
    Truncated,
    TrailingBytes,
    /// `n_signals` is zero, `n_public >= n_signals`, or a count exceeds `2^MAX_LOG`.
    BadHeader,
    /// A term names a signal `>= n_signals`.
    SignalOutOfRange {
        constraint: usize,
        signal: u32,
    },
    /// A term list is not strictly increasing.
    NotIncreasing {
        constraint: usize,
    },
    /// A link names a public or out-of-range signal, the same signal twice, or a signal another link already uses on
    /// the same side.
    BadLink {
        link: usize,
    },
    /// Zero instances, or a batch too large to address.
    BadInstanceCount,
    /// Signal 0 of an instance is not 1.
    ConstantNotOne {
        instance: usize,
    },
    /// An instance sets a bit past `n_signals`.
    SpareBitsSet {
        instance: usize,
    },
}

impl fmt::Display for FormatError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

impl std::error::Error for FormatError {}

/// One constraint `(Σ_A z)·(Σ_B z) = Σ_C z`, each side a strictly increasing signal list.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Constraint {
    pub a: Vec<u32>,
    pub b: Vec<u32>,
    pub c: Vec<u32>,
}

/// A parsed block R1CS.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct R1csFile {
    pub n_signals: usize,
    pub n_public: usize,
    pub constraints: Vec<Constraint>,
    /// `(in, out)` signal pairs; empty for a `CLB1` block.
    pub links: Vec<(u32, u32)>,
}

/// A parsed batch witness: `n_instances` rows of `bytes_per_instance()` bytes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WitnessFile {
    pub n_signals: usize,
    pub n_instances: usize,
    pub data: Vec<u8>,
}

struct Reader<'a> {
    bytes: &'a [u8],
}

impl<'a> Reader<'a> {
    fn take(&mut self, n: usize) -> Result<&'a [u8], FormatError> {
        if self.bytes.len() < n {
            return Err(FormatError::Truncated);
        }
        let (head, tail) = self.bytes.split_at(n);
        self.bytes = tail;
        Ok(head)
    }

    fn u32(&mut self) -> Result<u32, FormatError> {
        Ok(u32::from_le_bytes(self.take(4)?.try_into().expect("4 bytes")))
    }

    /// The magic, which must be one of `magics`, then the version. Returns the magic's index.
    fn header(&mut self, magics: &[&[u8; 4]]) -> Result<usize, FormatError> {
        let magic = self.take(4)?;
        let index = magics
            .iter()
            .position(|m| m.as_slice() == magic)
            .ok_or(FormatError::BadMagic)?;
        match self.u32()? {
            VERSION => Ok(index),
            v => Err(FormatError::BadVersion(v)),
        }
    }

    fn finish(&self) -> Result<(), FormatError> {
        if self.bytes.is_empty() {
            Ok(())
        } else {
            Err(FormatError::TrailingBytes)
        }
    }
}

fn check_count(n: u32) -> Result<usize, FormatError> {
    let n = n as usize;
    if n > 1 << MAX_LOG {
        return Err(FormatError::BadHeader);
    }
    Ok(n)
}

/// The first link that is not well formed: both signals private and distinct, no signal twice on one side.
pub fn check_links(n_signals: usize, n_public: usize, links: &[(u32, u32)]) -> Result<(), FormatError> {
    let mut used = vec![0u8; n_signals];
    for (link, &(input, output)) in links.iter().enumerate() {
        let private = |s: u32| (s as usize) > n_public && (s as usize) < n_signals;
        if !private(input) || !private(output) || input == output || used[input as usize] & 1 != 0 {
            return Err(FormatError::BadLink { link });
        }
        used[input as usize] |= 1;
        if used[output as usize] & 2 != 0 {
            return Err(FormatError::BadLink { link });
        }
        used[output as usize] |= 2;
    }
    Ok(())
}

impl R1csFile {
    pub fn parse(bytes: &[u8]) -> Result<Self, FormatError> {
        let mut r = Reader { bytes };
        let linked = r.header(&[R1CS_MAGIC, LINKED_R1CS_MAGIC])? == 1;
        let n_signals = check_count(r.u32()?)?;
        let n_public = r.u32()? as usize;
        let n_constraints = check_count(r.u32()?)?;
        let n_link = if linked { check_count(r.u32()?)? } else { 0 };
        if n_signals == 0 || n_public >= n_signals || (linked && n_link == 0) {
            return Err(FormatError::BadHeader);
        }
        // Every link takes 8 bytes, which bounds the allocation by the input.
        let mut links = Vec::with_capacity(n_link.min(r.bytes.len() / 8));
        for _ in 0..n_link {
            links.push((r.u32()?, r.u32()?));
        }
        check_links(n_signals, n_public, &links)?;
        // Every constraint takes at least 12 bytes, which bounds the allocation by the input.
        let mut constraints = Vec::with_capacity(n_constraints.min(r.bytes.len() / 12));
        for index in 0..n_constraints {
            let mut side = || -> Result<Vec<u32>, FormatError> {
                let n_terms = r.u32()? as usize;
                let raw = r.take(n_terms.checked_mul(4).ok_or(FormatError::Truncated)?)?;
                let terms: Vec<u32> = raw.as_chunks::<4>().0.iter().map(|b| u32::from_le_bytes(*b)).collect();
                if let Some(&signal) = terms.iter().find(|&&s| s as usize >= n_signals) {
                    return Err(FormatError::SignalOutOfRange {
                        constraint: index,
                        signal,
                    });
                }
                if terms.windows(2).any(|w| w[0] >= w[1]) {
                    return Err(FormatError::NotIncreasing { constraint: index });
                }
                Ok(terms)
            };
            let a = side()?;
            let b = side()?;
            let c = side()?;
            constraints.push(Constraint { a, b, c });
        }
        r.finish()?;
        Ok(Self {
            n_signals,
            n_public,
            constraints,
            links,
        })
    }

    /// The canonical encoding, which [`Self::parse`] inverts: `CLB1` without links, `CLB2` with.
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::new();
        let linked = !self.links.is_empty();
        out.extend_from_slice(if linked { LINKED_R1CS_MAGIC } else { R1CS_MAGIC });
        let mut header = vec![VERSION as usize, self.n_signals, self.n_public, self.constraints.len()];
        if linked {
            header.push(self.links.len());
        }
        for x in header {
            out.extend_from_slice(&u32::try_from(x).expect("count fits u32").to_le_bytes());
        }
        for &(input, output) in &self.links {
            out.extend_from_slice(&input.to_le_bytes());
            out.extend_from_slice(&output.to_le_bytes());
        }
        for constraint in &self.constraints {
            for side in [&constraint.a, &constraint.b, &constraint.c] {
                out.extend_from_slice(&u32::try_from(side.len()).expect("count fits u32").to_le_bytes());
                for &s in side.iter() {
                    out.extend_from_slice(&s.to_le_bytes());
                }
            }
        }
        out
    }
}

impl WitnessFile {
    pub fn bytes_per_instance(&self) -> usize {
        self.n_signals.div_ceil(8)
    }

    /// Instance `i`'s signal bytes.
    pub fn instance(&self, i: usize) -> &[u8] {
        let w = self.bytes_per_instance();
        &self.data[i * w..(i + 1) * w]
    }

    pub fn parse(bytes: &[u8]) -> Result<Self, FormatError> {
        let mut r = Reader { bytes };
        r.header(&[WITNESS_MAGIC])?;
        let n_signals = check_count(r.u32()?)?;
        if n_signals == 0 {
            return Err(FormatError::BadHeader);
        }
        let n_instances = r.u32()? as usize;
        if n_instances == 0 || n_instances > 1 << MAX_LOG {
            return Err(FormatError::BadInstanceCount);
        }
        let width = n_signals.div_ceil(8);
        let len = width.checked_mul(n_instances).ok_or(FormatError::BadInstanceCount)?;
        let data = r.take(len)?.to_vec();
        r.finish()?;
        let spare_mask = if n_signals.is_multiple_of(8) {
            0
        } else {
            0xFFu8 << (n_signals % 8)
        };
        for (instance, row) in data.chunks_exact(width).enumerate() {
            if row[0] & 1 != 1 {
                return Err(FormatError::ConstantNotOne { instance });
            }
            if row[width - 1] & spare_mask != 0 {
                return Err(FormatError::SpareBitsSet { instance });
            }
        }
        Ok(Self {
            n_signals,
            n_instances,
            data,
        })
    }

    /// The canonical encoding, which [`Self::parse`] inverts.
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(16 + self.data.len());
        out.extend_from_slice(WITNESS_MAGIC);
        for x in [VERSION as usize, self.n_signals, self.n_instances] {
            out.extend_from_slice(&u32::try_from(x).expect("count fits u32").to_le_bytes());
        }
        out.extend_from_slice(&self.data);
        out
    }
}
