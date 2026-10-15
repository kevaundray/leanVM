#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"

if (( $# > 1 )); then
    echo "usage: bash run-xmss.sh [signers per group, default 2,3]" >&2
    exit 2
fi
groups="${1:-2,3}"
out=artifacts/xmss
mkdir -p "$out"

cargo +1.97 build --release -p binary-spartan-cli
cli=../../target/release/binary-spartan
"$cli" gen-xmss --groups "$groups" --out "$out/honest"
"$cli" gen-xmss --groups "$groups" --out "$out/tampered" --tamper

(
    cd clean
    lake build clean_export
    lake exe clean_export xmss-r1cs "../$out/circuit.r1cs"
    lake exe clean_export xmss-witness "../$out/honest/inputs.json" "../$out/honest/witness.bin"
    lake exe clean_export xmss-witness "../$out/tampered/inputs.json" "../$out/tampered/witness.bin"
)

for mode in "" --spark; do
    "$cli" prove "$out/circuit.r1cs" "$out/honest/witness.bin" --signers "$out/honest/signers.json" \
        $mode --self-check --repeat 3
done
if "$cli" prove "$out/circuit.r1cs" "$out/tampered/witness.bin" --signers "$out/tampered/signers.json"; then
    echo "run-xmss.sh: the tampered witness was accepted" >&2
    exit 1
fi
echo "run-xmss.sh: the tampered witness was rejected"
