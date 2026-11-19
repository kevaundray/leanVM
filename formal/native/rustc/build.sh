#!/usr/bin/env bash
# The deployed `lean_xmss::verify` and `lean_sphincs::verify` compiled by rustc to x86-64 and AArch64 assembly, behind
# the entry points `xmss_verify` (`xmss.rs`) and `sphincs_verify` (`sphincs.rs`) that `run/check.sh` links, byte for
# byte the same on every machine and in every checkout.
#
# Usage, from anywhere:
#   rustc/build.sh            # out/{xmss,sphincs}-{x86_64,aarch64}.{s,o}, and SHA256SUMS of them
#   rustc/build.sh --check    # builds twice, in two fresh directories, and fails unless both match SHA256SUMS
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
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
root=$(cd "$here/../../.." && pwd)

RUSTUP_TOOLCHAIN=$(sed -n 's/^channel = "\(.*\)"$/\1/p' "$here/rust-toolchain.toml")
export RUSTUP_TOOLCHAIN
unset RUSTC_BOOTSTRAP RUSTC_WRAPPER

# What the build reads, relative to the repository: the deployed crates' sources and the entry points.
sources=(crates/keccak256/src crates/lean_xmss/src crates/lean_sphincs/src formal/native/rustc/xmss.rs formal/native/rustc/sphincs.rs)

# build SRC OUT: compiles the tree at SRC (laid out as the repository) into OUT.
build() {
  local src=$1 out=$2
  mkdir -p "$out"
  local deps
  deps=$(mktemp -d)
  local sysroot
  sysroot=$(rustc --print sysroot)
  local target arch cpu
  for target in x86_64-unknown-linux-musl aarch64-unknown-linux-musl; do
    arch=${target%%-*}
    local arch_flags=()
    case $arch in
      # LLVM 23 marks a function's preferred alignment with `.prefalign`, which no released assembler (clang 21) knows;
      # a fixed 16-byte alignment gives `.p2align 4` instead.
      x86_64) cpu=x86-64 arch_flags=(-C llvm-args=-align-all-functions=4) ;;
      aarch64) cpu=generic ;;
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
          --emit "link=$deps/$target/lib$scheme.a,asm=$out/$scheme-$arch.s,obj=$out/$scheme-$arch.o" \
          "formal/native/rustc/$scheme.rs"
      done
    )
  done
  rm -rf "$deps"
  (cd "$out" && sha256sum xmss-*.s xmss-*.o sphincs-*.s sphincs-*.o >SHA256SUMS)
}

case ${1:-} in
  "")
    build "$root" "$here/out"
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
      build "$tree" "$tree.out"
      if diff "$here/SHA256SUMS" "$tree.out/SHA256SUMS"; then
        echo "$tree: identical to SHA256SUMS"
      else
        echo "$tree: DIFFERS from SHA256SUMS" >&2
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
