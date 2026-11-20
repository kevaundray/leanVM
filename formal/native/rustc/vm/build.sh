#!/usr/bin/env bash
# The no_std leanVM verifier of src/ compiled by rustc to x86-64 and AArch64 assembly, exporting `leanvm_verify` (the
# context of NativeVm/Input.lean) that `run/check.sh` links as VM.S, byte for byte the same on every machine and in
# every checkout.
#
# Usage, from anywhere:
#   rustc/vm/build.sh            # out/vm-{x86_64,aarch64}.s and out/vm-x86_64.post.s, and SHA256SUMS of them
#   rustc/vm/build.sh --check    # builds twice, in two fresh directories, and fails unless both match SHA256SUMS
#
# Needs rustup with the toolchain of `../rust-toolchain.toml` and the targets `x86_64-unknown-none` and
# `aarch64-unknown-none-softfloat` (`rustup target add`): no_std targets without SIMD or floating-point registers.
#
# The flags are `../build.sh`'s: plain rustc, the crate's metadata its name, every source path relative to the
# repository, the sysroot and the output directory remapped, nothing incremental, the baseline CPU, one codegen unit,
# `panic=abort`, and `-C lto=fat` on a static library so that the assembly is one module holding exactly what the
# export reaches (the assembly is written after LTO only when the link is emitted too). The assembly is the artifact
# (`run/check.sh` assembles it, the proofs ingest it): rustc's own object is not emitted, as rustc 1.99.1's object and
# assembly code generation differ under fat LTO. On x86-64 the small code model
# (the target's default is the kernel's, which a user-space harness cannot link) and `-align-all-functions=4`
# (rustc's LLVM writes `.prefalign` otherwise, which clang's assembler rejects).
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
root=$(cd "$here/../../../.." && pwd)

RUSTUP_TOOLCHAIN=$(sed -n 's/^channel = "\(.*\)"$/\1/p' "$here/../rust-toolchain.toml")
export RUSTUP_TOOLCHAIN
unset RUSTC_BOOTSTRAP RUSTC_WRAPPER RUSTFLAGS

crate=formal/native/rustc/vm

# build SRC OUT: compiles the crate of the tree at SRC (laid out as the repository) into OUT.
build() {
  local src=$1 out=$2
  mkdir -p "$out"
  local deps sysroot target arch flags
  deps=$(mktemp -d)
  sysroot=$(rustc --print sysroot)
  for target in x86_64-unknown-none aarch64-unknown-none-softfloat; do
    arch=${target%%-*}
    flags=(
      --edition 2024 --target "$target"
      -C opt-level=3 -C codegen-units=1 -C panic=abort -C debuginfo=0 -C debug-assertions=no -C overflow-checks=no
      --remap-path-prefix="$src/=" --remap-path-prefix="$sysroot=/sysroot" --remap-path-prefix="$deps/=" --remap-path-prefix="$out/="
    )
    case $arch in
      x86_64) flags+=(-C target-cpu=x86-64 -C llvm-args=-align-all-functions=4) ;;
      aarch64) flags+=(-C target-cpu=generic) ;;
    esac
    (
      cd "$src"
      rustc "${flags[@]}" --crate-type staticlib --crate-name native_vm -C metadata=native_vm -C lto=fat \
        --emit "link=$deps/libnative_vm-$arch.a,asm=$out/vm-$arch.s" "$crate/src/lib.rs"
      # The x86-64 code that is assembled, run and proved is the post-passed one (`../x86-postpass.py`), every
      # instruction one Kraken reads.
      if [[ $arch == x86_64 ]]; then
        python3 formal/native/rustc/x86-postpass.py "$out/vm-$arch.s" "$out/vm-$arch.post.s"
      fi
    )
  done
  rm -rf "$deps"
  (cd "$out" && sha256sum vm-*.s >SHA256SUMS)
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
      mkdir -p "$tree/$crate"
      cp -R "$root/$crate/src" "$tree/$crate/"
      cp "$root/formal/native/rustc/x86-postpass.py" "$tree/formal/native/rustc/"
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
