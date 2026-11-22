#!/usr/bin/env bash
# The deployed `lean_xmss::verify` and `lean_sphincs::verify` compiled by rustc to x86-64 and AArch64 assembly, behind
# the entry points `xmss_verify` (`xmss.rs`) and `sphincs_verify` (`sphincs.rs`) in one `signatures.rs` crate.
# Shared functions have one body per architecture. `run/check.sh` links the output, byte for byte the same in every checkout.
#
# Usage, from anywhere:
#   rustc/build.sh            # full asm/*.s and SHA256SUMS
#   rustc/build.sh --check    # rebuilds twice and checks hashes and committed assembly
#
# Needs rustup with the toolchain of `rust-toolchain.toml` and its two targets (`rustup target add`).
#
# Plain rustc, not cargo: cargo derives each crate's `-C metadata` (which every symbol name hashes) from the
# dependency's absolute path when it lies outside the workspace, as the deployed crates do here, and it would apply the
# repository's `.cargo/config.toml` (`target-cpu=native`). Here every crate's metadata is its name, every source path is
# relative to the repository, the sysroot and the output directory are remapped, nothing is incremental, and the
# target CPU is the baseline. The targets are musl's, the libc of the harness these objects are linked into.
# `-C lto=fat` on the static library with one codegen unit makes the assembly one module holding exactly what the
# export reaches. The no_std entry crate aborts on panic; `-C panic=abort` leaves out unwinding tables.
# `runtime.rs` supplies the required global allocator, trapping if the allocation-free verifier ever allocates.
#
# No SIMD or floating-point registers: `-neon` on AArch64, `-sse,-sse2` on x86-64, for every crate alike, so that the
# code a verification runs uses general-purpose registers only, which Kraken models. rustc warns that the target's ABI
# wants those features: no floating-point value crosses any function boundary here, so the ABI is not affected. The
# entry crate defines `memcpy` and `memset` itself (`mem.rs`), so the assembly holds every instruction a
# verification runs. The raw assembly is the artifact (`run/check.sh` assembles it): rustc's own object is not emitted, as
# rustc 1.99.1's object and assembly code generation differ under fat LTO.
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
root=$(cd "$here/../../.." && pwd)

RUSTUP_TOOLCHAIN=$(sed -n 's/^channel = "\(.*\)"$/\1/p' "$here/rust-toolchain.toml")
export RUSTUP_TOOLCHAIN
unset RUSTC_BOOTSTRAP RUSTC_WRAPPER RUSTFLAGS

# What the build reads, relative to the repository: the deployed crates' sources and the entry points.
sources=(crates/keccak256/src crates/lean_xmss/src crates/lean_sphincs/src formal/native/rustc/xmss.rs formal/native/rustc/sphincs.rs formal/native/rustc/mem.rs formal/native/rustc/runtime.rs formal/native/rustc/signatures.rs)

# build SRC ASM: writes the complete assembly from the tree at SRC to ASM.
build() {
  local src=$1 asm=$2
  mkdir -p "$asm"
  local deps
  deps=$(mktemp -d)
  local sysroot
  sysroot=$(rustc --print sysroot)
  local target arch cpu
  for target in x86_64-unknown-linux-musl aarch64-unknown-linux-musl; do
    arch=${target%%-*}
    local arch_flags=()
    case $arch in
      # rustc's LLVM 23 otherwise starts each function with `.prefalign` (an LLVM 23 extension: alignment by the
      # function's size), which the harness's assembler (clang 21, GNU as) rejects; this gives `.p2align 4` instead.
      x86_64) cpu=x86-64 arch_flags=(-C llvm-args=-align-all-functions=4 -C target-feature=-sse,-sse2) ;;
      aarch64) cpu=generic arch_flags=(-C target-feature=-neon) ;;
    esac
    local flags=(
      --edition 2024 --target "$target" -C target-cpu="$cpu"
      -C opt-level=3 -C codegen-units=1 -C panic=abort -C debuginfo=0 -C debug-assertions=no -C overflow-checks=no
      --remap-path-prefix="$src/=" --remap-path-prefix="$sysroot=/sysroot" --remap-path-prefix="$deps/=" --remap-path-prefix="$asm/="
      -L dependency="$deps/$target" --out-dir "$deps/$target" "${arch_flags[@]}"
    )
    mkdir -p "$deps/$target"
    (
      cd "$src"
      rustc "${flags[@]}" --crate-type rlib --crate-name keccak256 -C metadata=keccak256 crates/keccak256/src/lib.rs
      for crate in lean_xmss lean_sphincs; do
        rustc "${flags[@]}" --crate-type rlib --crate-name "$crate" -C metadata="$crate" \
          --extern keccak256="$deps/$target/libkeccak256.rlib" "crates/$crate/src/lib.rs"
      done
      rustc "${flags[@]}" --crate-type staticlib --crate-name signatures -C metadata=signatures -C lto=fat \
        --extern "lean_xmss=$deps/$target/liblean_xmss.rlib" \
        --extern "lean_sphincs=$deps/$target/liblean_sphincs.rlib" \
        --emit "link=$deps/$target/libsignatures.a,asm=$asm/signatures-$arch.s" \
        formal/native/rustc/signatures.rs
    )
  done
  rm -rf "$deps"
  (
    cd "$asm/.."
    sha256sum asm/signatures-{aarch64,x86_64}.s
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
      for path in "${sources[@]}"; do
        mkdir -p "$(dirname "$tree/$path")"
        cp -R "$root/$path" "$tree/$path"
      done
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
