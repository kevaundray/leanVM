#!/bin/sh
set -eu
root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
target_dir=${1:-"$root/target/guest"}
cd "$root"
unset RUSTFLAGS RUSTC RUSTDOC RUSTC_WRAPPER RUSTC_WORKSPACE_WRAPPER
CARGO_ENCODED_RUSTFLAGS=$(printf '%s\037%s\037%s\037%s\037%s\037%s\037%s\037%s' '-C' 'panic=abort' '-C' 'target-feature=+unaligned-scalar-mem' '-C' "link-arg=-T$root/crates/guest/link.x" '-C' 'link-arg=--no-relax')
export CARGO_ENCODED_RUSTFLAGS
cargo +nightly build --release --target riscv64im-unknown-none-elf --target-dir "$target_dir" -Z build-std=core,alloc -Z build-std-features=compiler-builtins-mem -p leanvm_guest --examples --features runtime
cargo +nightly build --release --target riscv64im-unknown-none-elf --target-dir "$target_dir" -Z build-std=core,alloc -Z build-std-features=compiler-builtins-mem -p leanvm_aggregation_guest --example aggregate --features runtime
