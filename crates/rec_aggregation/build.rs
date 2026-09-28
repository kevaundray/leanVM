use std::{env, path::PathBuf, process::Command};

fn main() {
    let root = PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").unwrap()).join("../..");
    let out = PathBuf::from(env::var_os("OUT_DIR").unwrap());
    for path in [
        "Cargo.toml",
        "Cargo.lock",
        "scripts/build-guests.sh",
        "crates/guest",
        "crates/guest_claims",
        "crates/riscv_proof",
        "crates/aggregation_guest",
    ] {
        println!("cargo:rerun-if-changed={}", root.join(path).display());
    }
    let target = root.join("target/guest");
    let status = Command::new("sh")
        .arg(root.join("scripts/build-guests.sh"))
        .arg(&target)
        .status()
        .expect("launch native guest build");
    assert!(
        status.success(),
        "RV64IM guest build failed; install nightly and rust-src with rustup"
    );
    let examples = target.join("riscv64im-unknown-none-elf/release/examples");
    for guest in ["aggregate", "fibonacci", "hash_chain", "memory_contracts"] {
        std::fs::copy(examples.join(guest), out.join(format!("{guest}.elf")))
            .expect("copy the compiled RV64IM guest image");
    }
}
