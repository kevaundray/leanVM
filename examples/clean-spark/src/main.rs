mod import;
mod proving;

use anyhow::{bail, Context, Result};
use std::path::PathBuf;

fn main() -> Result<()> {
    let mut paths = Vec::new();
    let mut self_check = false;
    for arg in std::env::args_os().skip(1) {
        if arg == "--self-check" {
            self_check = true;
        } else if arg == "--help" || arg == "-h" {
            println!("Usage: clean-spark <r1cs.json> <witness.json> [--self-check]");
            return Ok(());
        } else if arg.to_string_lossy().starts_with('-') {
            bail!("unknown option: {}", arg.to_string_lossy());
        } else {
            paths.push(PathBuf::from(arg));
        }
    }
    if paths.len() != 2 {
        bail!("Usage: clean-spark <r1cs.json> <witness.json> [--self-check]");
    }
    let circuit = import::load(&paths[0], &paths[1]).context("loading Clean R1CS and witness")?;
    proving::run(circuit, self_check)
}
