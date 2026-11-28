//! The Lean data of the aggregation guest, written from leanVM's own sources. A child of the
//! `aggregation` crate's root (the overlay's appended line), so `super::*` is everything it
//! defines, private items included.

use super::*;
// The crate's modules (`build.rs` widens their items).
use super::{
    cells::*, child::*, claim_pool::*, coverage::*, deferred::*, error::*, guest::*, hints::*, node::*,
    placeholders::*, proof::*, statement::*,
};
use std::collections::BTreeMap;
use verifier::E;

pub mod config;
pub mod bytecode;
#[cfg(test)]
mod guest_diff;
pub mod manifest;
pub mod node_vectors;

/// A generated file: its path relative to `lean_vm/` and its text.
pub struct File {
    pub path: String,
    pub text: String,
}

/// The compiled guest at its self-consistent size: the artefact the Lean back end wrote (`guests/lean_ethereum.compiled`).
pub fn guest() -> &'static isa::CompiledProgram {
    unified_guest()
}

/// The deployed placeholders, at the guest's log size.
pub fn placeholders() -> BTreeMap<String, String> {
    placeholder_map(guest().prog.len().trailing_zeros() as usize)
}

/// Every file this crate writes.
pub fn all_files() -> Vec<File> {
    let mut files = bytecode::files(guest());
    files.extend(config::files(guest().prog.len().trailing_zeros() as usize));
    files.push(manifest::file());
    files.push(node_vectors::file());
    files
}
