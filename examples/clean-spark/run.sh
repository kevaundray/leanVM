#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"

if (( $# > 1 )); then
    echo "usage: bash run.sh [x]" >&2
    exit 2
fi
if [[ ! -x node_modules/.bin/snarkjs ]]; then
    echo "Install witness tooling first: npm ci --ignore-scripts" >&2
    exit 1
fi

mkdir -p artifacts
node --input-type=module - "${1:-3}" <<'JS'
import { writeFileSync } from 'node:fs';
const x = process.argv[2];
const prime = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;
if (!/^(0|[1-9][0-9]*)$/.test(x) || BigInt(x) >= prime) {
    throw new Error('x must be a canonical decimal BN254 scalar');
}
writeFileSync('artifacts/input.json', JSON.stringify({ x }) + '\n');
console.log(`Circuit: x=${x}, expected y=${(BigInt(x) ** 2n + BigInt(x) + 5n) % prime}`);
JS

(
    cd clean
    lake build clean_export
    lake exe clean_export ../artifacts
)
node_modules/.bin/snarkjs wtns calculate artifacts/circuit.wasm artifacts/input.json artifacts/witness.wtns
node_modules/.bin/snarkjs wtns check artifacts/circuit.r1cs artifacts/witness.wtns
node_modules/.bin/snarkjs wtns export json artifacts/witness.wtns artifacts/witness.json
cargo run --release --locked -- artifacts/circuit.json artifacts/witness.json --self-check
