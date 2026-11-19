#!/usr/bin/env bash
# rustc's assembly for the signature verifiers as Lean modules of formal/native (IngestCore.lean says what is
# generated): AArch64 (rustc/out/{xmss,sphincs}-aarch64.s) as NativeRustcArm/Code.lean and everything under
# NativeRustcArm/Code/ but Infix.lean (the lemmas the generated proofs use), x86-64
# (rustc/out/{xmss,sphincs}-x86_64.post.s) as NativeRustcX64/Code.lean and NativeRustcX64/Code/. rustc/build.sh
# builds rustc/out when it is missing.
#
# Usage, from anywhere:
#   rustc/ingest/ingest.sh           # regenerates the modules
#   rustc/ingest/ingest.sh --check   # regenerates them in a temporary directory, fails if they differ
#
# The ingestion is a Lake project of its own (this directory) on Kraken's toolchain, whose parsers formal/native's
# Lean does not build.
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
native=$(cd "$here/../.." && pwd)
out=$native/rustc/out

case ${1:-} in
  "" | --check) ;;
  *) echo "usage: $0 [--check]" >&2; exit 2 ;;
esac

for f in xmss-aarch64.s sphincs-aarch64.s xmss-x86_64.post.s sphincs-x86_64.post.s; do
  [ -f "$out/$f" ] || { "$native/rustc/build.sh" >&2; break; }
done

(cd "$here" && lake build -q ingest-arm ingest-x64 >&2)
gen=$(mktemp -d)
trap 'rm -rf "$gen"' EXIT
(cd "$here" && lake env .lake/build/bin/ingest-arm "$gen" \
  xmss="$out/xmss-aarch64.s" sphincs="$out/sphincs-aarch64.s")
(cd "$here" && lake env .lake/build/bin/ingest-x64 "$gen" \
  xmss="$out/xmss-x86_64.post.s" sphincs="$out/sphincs-x86_64.post.s")

status=0
for lib in NativeRustcArm NativeRustcX64; do
  code=$native/$lib/Code
  if [ "${1:-}" = --check ]; then
    diff -r -x Infix.lean "$gen/$lib/Code" "$code" || status=1
    diff "$gen/$lib/Code.lean" "$native/$lib/Code.lean" || status=1
  else
    mkdir -p "$code"
    find "$code" -mindepth 1 -maxdepth 1 ! -name Infix.lean -exec rm -rf {} +
    cp -R "$gen/$lib/Code/." "$code/"
    cp "$gen/$lib/Code.lean" "$native/$lib/Code.lean"
  fi
done
if [ "${1:-}" = --check ]; then
  if [ $status = 0 ]; then echo "generated modules up to date"; else echo "generated modules DIFFER" >&2; fi
  exit $status
fi
echo "regenerated $(find "$gen" -name '*.lean' | wc -l) modules under NativeRustcArm/Code and NativeRustcX64/Code"
