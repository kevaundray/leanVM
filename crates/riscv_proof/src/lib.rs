#![no_std]

extern crate alloc;
#[cfg(any(feature = "host", test))]
extern crate std;

use alloc::vec::Vec;
use leanvm_guest::Field;

pub mod circuit;
pub mod cpu_tables;
#[cfg(feature = "host")]
pub mod host;
pub mod instruction;
pub mod layout;
pub mod memory;
pub mod packed;
pub mod packed_reduction;
pub mod program;
pub mod schema;
mod verify;

pub mod portable {
    pub mod algebra;
    pub mod flock;
    pub mod gkr;
    pub mod pcs;
    pub mod ring;
    pub mod transcript;
}

pub use program::ProgramInfo;
pub use verify::verify;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    InvalidProgram,
    InvalidShape,
    InvalidExecution,
    InvalidProof,
    Encoding,
    Unsupported,
    Capacity {
        cycles: u64,
        required_log: u32,
        max_log: u32,
    },
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl core::error::Error for Error {}
impl From<portable::transcript::Error> for Error {
    fn from(_: portable::transcript::Error) -> Self {
        Self::InvalidProof
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Opening {
    pub leaf: Vec<u64>,
    pub siblings: Vec<[u8; 32]>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof {
    pub stream: Vec<Field>,
    pub merkle: Vec<Opening>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifySummary {
    pub cycles: u64,
    pub memory_events: u64,
    pub committed_words: u64,
    pub log_inv_rate: u8,
}

impl Proof {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(b"RV64PRF1");
        out.extend_from_slice(&(self.stream.len() as u64).to_le_bytes());
        for field in &self.stream {
            out.extend_from_slice(&field.to_le_bytes());
        }
        out.extend_from_slice(&(self.merkle.len() as u64).to_le_bytes());
        for opening in &self.merkle {
            out.extend_from_slice(&(opening.leaf.len() as u64).to_le_bytes());
            for word in &opening.leaf {
                out.extend_from_slice(&word.to_le_bytes());
            }
            out.extend_from_slice(&(opening.siblings.len() as u64).to_le_bytes());
            for sibling in &opening.siblings {
                out.extend_from_slice(sibling);
            }
        }
        out
    }

    pub fn from_bytes(mut bytes: &[u8]) -> Result<Self, Error> {
        fn take<'a>(bytes: &mut &'a [u8], n: usize) -> Result<&'a [u8], Error> {
            let (part, rest) = bytes.split_at_checked(n).ok_or(Error::Encoding)?;
            *bytes = rest;
            Ok(part)
        }
        fn length(bytes: &mut &[u8], item_size: usize) -> Result<usize, Error> {
            let n = u64::from_le_bytes(take(bytes, 8)?.try_into().unwrap());
            let n = usize::try_from(n).map_err(|_| Error::Encoding)?;
            if n > portable::transcript::MAX_ELEMENTS || n > bytes.len() / item_size {
                return Err(Error::Encoding);
            }
            Ok(n)
        }
        if take(&mut bytes, 8)? != b"RV64PRF1" {
            return Err(Error::Encoding);
        }
        let n = length(&mut bytes, 24)?;
        let mut stream = Vec::new();
        stream.try_reserve_exact(n).map_err(|_| Error::Encoding)?;
        for _ in 0..n {
            stream.push(Field::from_le_bytes(take(&mut bytes, 24)?.try_into().unwrap()));
        }
        let n = length(&mut bytes, 16)?;
        let mut merkle = Vec::new();
        merkle.try_reserve_exact(n).map_err(|_| Error::Encoding)?;
        for _ in 0..n {
            let n = length(&mut bytes, 8)?;
            if n > 64 {
                return Err(Error::Encoding);
            }
            let mut leaf = Vec::new();
            leaf.try_reserve_exact(n).map_err(|_| Error::Encoding)?;
            for _ in 0..n {
                leaf.push(u64::from_le_bytes(take(&mut bytes, 8)?.try_into().unwrap()));
            }
            let n = length(&mut bytes, 32)?;
            if n > 32 {
                return Err(Error::Encoding);
            }
            let mut siblings = Vec::new();
            siblings.try_reserve_exact(n).map_err(|_| Error::Encoding)?;
            for _ in 0..n {
                siblings.push(take(&mut bytes, 32)?.try_into().unwrap());
            }
            merkle.push(Opening { leaf, siblings });
        }
        if !bytes.is_empty() {
            return Err(Error::Encoding);
        }
        Ok(Self { stream, merkle })
    }
}
