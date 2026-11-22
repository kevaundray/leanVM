#!/usr/bin/env bash
# The deployed `lean_xmss::verify` and `lean_sphincs::verify` compiled by rustc to x86-64 and AArch64 assembly, behind
# the entry points `xmss_verify` (`xmss.rs`) and `sphincs_verify` (`sphincs.rs`) that `run/check.sh` links, byte for
# byte the same on every machine and in every checkout.
#
# Usage, from anywhere:
#   rustc/build.sh            # full out/*.s, committed trimmed asm/*.s, and SHA256SUMS of both
#   rustc/build.sh --check    # rebuilds twice and checks both hashes and committed trimmed assembly
#
# Needs rustup with the toolchain of `rust-toolchain.toml` and its two targets (`rustup target add`).
#
# Plain rustc, not cargo: cargo derives each crate's `-C metadata` (which every symbol name hashes) from the
# dependency's absolute path when it lies outside the workspace, as the deployed crates do here, and it would apply the
# repository's `.cargo/config.toml` (`target-cpu=native`). Here every crate's metadata is its name, every source path is
# relative to the repository, the sysroot and the output directory are remapped, nothing is incremental, and the
# target CPU is the baseline. The targets are musl's, the libc of the harness these objects are linked into.
# `-C lto=fat` on the static library with one codegen unit makes the assembly one module holding exactly what the
# export reaches, std's panic and allocation paths included, and `-C panic=abort` leaves out the unwinding tables.
#
# No SIMD or floating-point registers: `-neon` on AArch64, `-sse,-sse2` on x86-64, for every crate alike, so that the
# code a verification runs uses general-purpose registers only, which Kraken models. rustc warns that the target's ABI
# wants those features: no floating-point value crosses any function boundary here, so the ABI is not affected. The
# entry crates define `memcpy` and `memset` themselves (`mem.rs`), so the assembly holds every instruction a
# verification runs. The raw assembly is the artifact (`run/check.sh` assembles it): rustc's own object is not emitted, as
# rustc 1.99.1's object and assembly code generation differ under fat LTO.
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
root=$(cd "$here/../../.." && pwd)

RUSTUP_TOOLCHAIN=$(sed -n 's/^channel = "\(.*\)"$/\1/p' "$here/rust-toolchain.toml")
export RUSTUP_TOOLCHAIN
unset RUSTC_BOOTSTRAP RUSTC_WRAPPER RUSTFLAGS

# What the build reads, relative to the repository: the deployed crates' sources and the entry points.
sources=(crates/keccak256/src crates/lean_xmss/src crates/lean_sphincs/src formal/native/rustc/xmss.rs formal/native/rustc/sphincs.rs formal/native/rustc/mem.rs)

# build SRC OUT ASM: compiles the tree at SRC and trims the full output into ASM.
build() {
  local src=$1 out=$2 asm=$3
  mkdir -p "$out" "$asm"
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
      --remap-path-prefix="$src/=" --remap-path-prefix="$sysroot=/sysroot" --remap-path-prefix="$deps/=" --remap-path-prefix="$out/="
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
      for scheme in xmss sphincs; do
        rustc "${flags[@]}" --crate-type staticlib --crate-name "$scheme" -C metadata="$scheme" -C lto=fat \
          --extern "lean_$scheme=$deps/$target/liblean_$scheme.rlib" \
          --emit "link=$deps/$target/lib$scheme.a,asm=$out/$scheme-$arch.s" \
          "formal/native/rustc/$scheme.rs"
      done
    )
    for scheme in xmss sphincs; do
      python3 -I "$here/trim.py" "$out/$scheme-$arch.s" "$asm/$scheme-$arch.s" "${scheme}_verify"
    done
  done
  rm -rf "$deps"
  (
    cd "$out/.."
    sha256sum out/xmss-{aarch64,x86_64}.s out/sphincs-{aarch64,x86_64}.s
    cd "$asm/.."
    sha256sum asm/xmss-{aarch64,x86_64}.s asm/sphincs-{aarch64,x86_64}.s
  ) >"$out/SHA256SUMS"
}

case ${1:-} in
  "")
    build "$root" "$here/out" "$here/asm"
    cp "$here/out/SHA256SUMS" "$here/SHA256SUMS"
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
      build "$tree" "$tree.artifacts/out" "$tree.artifacts/asm"
      if diff "$here/SHA256SUMS" "$tree.artifacts/out/SHA256SUMS"; then
        echo "$tree: identical to SHA256SUMS"
      else
        echo "$tree: DIFFERS from SHA256SUMS" >&2
        status=1
      fi
      if ! diff -r "$here/asm" "$tree.artifacts/asm"; then
        echo "$tree: DIFFERS from committed trimmed assembly" >&2
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
