#!/usr/bin/env bash
# The no_std leanVM verifier of src/ compiled by rustc to x86-64 and AArch64 assembly, exporting `leanvm_verify` (the
# context of NativeVm/Input.lean) that `run/check.sh` links as VM.S, byte for byte the same on every machine and in
# every checkout.
#
# Usage, from anywhere:
#   rustc/vm/build.sh            # full asm/*.s and SHA256SUMS
#   rustc/vm/build.sh --check    # rebuilds twice and checks hashes and committed assembly
#
# Needs rustup with the toolchain of `../rust-toolchain.toml` and the targets `x86_64-unknown-none` and
# `aarch64-unknown-none-softfloat` (`rustup target add`): no_std targets without SIMD or floating-point registers.
#
# The flags are `../build.sh`'s: plain rustc, the crate's metadata its name, every source path relative to the
# repository, the sysroot and the output directory remapped, nothing incremental, the baseline CPU, one codegen unit,
# `panic=abort`, and `-C lto=fat` on a static library so that the assembly is one module holding exactly what the
# export reaches (the assembly is written after LTO only when the link is emitted too). `run/check.sh` assembles the
# full output; ingestion selects the reachable code and data. rustc's own object is not emitted, as rustc 1.99.1's object and
# assembly code generation differ under fat LTO. On x86-64, `-align-all-functions=4` is passed: rustc's LLVM 23 otherwise
# starts each function with `.prefalign` (an LLVM 23 extension), which the harness's assembler (clang 21, GNU as) rejects.
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
root=$(cd "$here/../../../.." && pwd)

RUSTUP_TOOLCHAIN=$(sed -n 's/^channel = "\(.*\)"$/\1/p' "$here/../rust-toolchain.toml")
export RUSTUP_TOOLCHAIN
unset RUSTC_BOOTSTRAP RUSTC_WRAPPER RUSTFLAGS

crate=formal/native/rustc/vm

# build SRC ASM: writes the complete assembly from the crate at SRC to ASM.
build() {
  local src=$1 asm=$2
  mkdir -p "$asm"
  local deps sysroot target arch flags
  deps=$(mktemp -d)
  sysroot=$(rustc --print sysroot)
  for target in x86_64-unknown-none aarch64-unknown-none-softfloat; do
    arch=${target%%-*}
    flags=(
      --edition 2024 --target "$target"
      -C opt-level=3 -C codegen-units=1 -C panic=abort -C debuginfo=0 -C debug-assertions=no -C overflow-checks=no
      --remap-path-prefix="$src/=" --remap-path-prefix="$sysroot=/sysroot" --remap-path-prefix="$deps/=" --remap-path-prefix="$asm/="
    )
    case $arch in
      x86_64) flags+=(-C target-cpu=x86-64 -C llvm-args=-align-all-functions=4) ;;
      aarch64) flags+=(-C target-cpu=generic) ;;
    esac
    (
      cd "$src"
      rustc "${flags[@]}" --crate-type staticlib --crate-name native_vm -C metadata=native_vm -C lto=fat \
        --emit "link=$deps/libnative_vm-$arch.a,asm=$asm/vm-$arch.s" "$crate/src/lib.rs"
    )
  done
  rm -rf "$deps"
  (
    cd "$asm/.."
    sha256sum asm/vm-aarch64.s asm/vm-x86_64.s
  ) >"$asm/../SHA256SUMS"
}

case ${1:-} in
  "")
    build "$root" "$here/asm"
    cat "$here/SHA256SUMS"
    ;;
  --check)
    scratch=$(mktemp -d)
    trap 'rm -rf "$scratch"' EXIT
    status=0
    # Two checkouts at different depths, each with its own output directory.
    for tree in "$scratch/a" "$scratch/b/deeper/tree"; do
      mkdir -p "$tree/$crate"
      cp -R "$root/$crate/src" "$tree/$crate/"
      build "$tree" "$tree.artifacts/asm"
      if diff "$here/SHA256SUMS" "$tree.artifacts/SHA256SUMS"; then
        echo "$tree: identical to SHA256SUMS"
      else
        echo "$tree: DIFFERS from SHA256SUMS" >&2
        status=1
      fi
      if ! diff -r "$here/asm" "$tree.artifacts/asm"; then
        echo "$tree: DIFFERS from committed assembly" >&2
        status=1
      fi
    done
    exit $status
    ;;
  *)
    echo "usage: $0 [--check]" >&2
    exit 2
    ;;
esac
