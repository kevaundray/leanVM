//! The compiler's test programs (`formal/lean_vm/tests/LeanVMTests/Programs/Basic.lean`) as the Lean back end
//! compiled them: `tests/compiled/<name>.txt`, and beside it `tests/compiled/<name>.inputs`, the public input the
//! program publishes and the witness streams its hints read, both written by `lake exe guest-backend export
//! programs`. Every program is proven and verified on them.
//!
//! An inputs file is a line `public A B`, then one line `witness NAME W…` per entry of a stream, in the order the
//! program's hints pop them; each word the decimal integer its two 64-bit limbs spell, the low limb first.
//!
//! `formal/lean_vm/scripts/export-rust.sh` includes this file for [`parse_inputs`].

use std::fs;

use isa::Program;
use lean_vm_core::cpu::{prove, verify};
use primitives::field::F128;

/// Named prover streams, each a list of entries.
pub(crate) type Streams = Vec<(String, Vec<Vec<F128>>)>;

/// A word from the decimal integer of its limbs.
fn word(s: &str) -> F128 {
    let v: u128 = s.parse().unwrap_or_else(|e| panic!("bad word `{s}`: {e}"));
    F128::new(v as u64, (v >> 64) as u64)
}

/// The public input and the streams of an inputs file.
pub(crate) fn parse_inputs(text: &str) -> ([F128; 2], Streams) {
    let mut public = [F128::ZERO; 2];
    let mut streams: Streams = Vec::new();
    for line in text.lines() {
        let mut parts = line.split_whitespace();
        match parts.next() {
            Some("public") => {
                let words: Vec<F128> = parts.map(word).collect();
                public = words.try_into().unwrap_or_else(|w: Vec<F128>| panic!("`public` needs two words, got {}", w.len()));
            }
            Some("witness") => {
                let name = parts.next().expect("`witness` needs a stream name").to_string();
                let entry = parts.map(word).collect();
                match streams.iter_mut().find(|(stream, _)| *stream == name) {
                    Some((_, entries)) => entries.push(entry),
                    None => streams.push((name, vec![entry])),
                }
            }
            Some(other) => panic!("unknown inputs line `{other}`"),
            None => {}
        }
    }
    (public, streams)
}

/// The test program `name` as the Lean back end compiled it, its witness streams and its public input.
pub(crate) fn lean_compiled(name: &str) -> (Program, Streams, [F128; 2]) {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/compiled");
    let read = |ext: &str| {
        fs::read_to_string(format!("{dir}/{name}.{ext}")).unwrap_or_else(|e| {
            panic!("{name}.{ext}: {e}: run `lake exe guest-backend export programs`")
        })
    };
    let program = Program::__from_text(&read("txt")).unwrap_or_else(|e| panic!("{name}: {e}"));
    let (public, streams) = parse_inputs(&read("inputs"));
    (program, streams, public)
}

/// Every test program proves and verifies on the inputs it declares.
#[test]
fn every_test_program_proves() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/compiled");
    let mut names: Vec<String> = fs::read_dir(dir)
        .expect("tests/compiled")
        .map(|e| e.expect("dir entry").path())
        .filter(|p| p.extension().is_some_and(|x| x == "inputs"))
        .map(|p| p.file_stem().unwrap().to_string_lossy().into_owned())
        .collect();
    names.sort();
    assert_eq!(names.len(), 18, "the eighteen test programs");
    for name in names {
        let (program, streams, want) = lean_compiled(&name);
        let (proof, _) = prove(&program, &streams, want, lean_vm_core::pcs::TEST_LOG_INV_RATE).unwrap();
        verify(&program, &want, &proof).unwrap_or_else(|e| panic!("{name}: verify: {e:?}"));
        println!("{name}: ok");
    }
}
