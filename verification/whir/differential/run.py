#!/usr/bin/env python3
"""Run both implementations, compare live vectors, and require both opening smokes."""

import os
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
PACKAGE = HERE.parent
SCOPE = ["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=16G", "-p", "MemorySwapMax=0"]
ENV = dict(os.environ, CARGO_TARGET_DIR="/tmp/whir-lean-target", CARGO_BUILD_JOBS="2", LEANVM_NUM_THREADS="1")


def run(command, cwd=PACKAGE):
    result = subprocess.run(SCOPE + command, cwd=cwd, env=ENV, text=True, stdout=subprocess.PIPE, check=True)
    return result.stdout


def records(text):
    result = {}
    for line in text.splitlines():
        key, sep, value = line.partition("=")
        if not sep or key in result:
            raise RuntimeError(f"Malformed or duplicate output: {line!r}")
        result[key] = value
    return result


def main():
    run(["lake", "build", "whirModel"])
    rust = records(run(["cargo", "+1.97", "run", "--release", "--locked", "--manifest-path", str(HERE / "Cargo.toml")]))
    executable = str(PACKAGE / ".lake" / "build" / "bin" / "whirModel")
    lean = records(run([executable]))
    lean_smoke = lean.pop("lean_smoke")
    rust_smoke = rust.pop("rust_smoke")
    query_cases = []
    for key in list(rust):
        if key.startswith("query_input_"):
            _, _, depth, count = key.split("_")
            values = rust.pop(key)
            expected = rust.pop(f"query_output_{depth}_{count}")
            limbs = values.split(",") if values else []
            actual = records(run([executable, "query", depth, count, *limbs]))
            if actual != {"queries": expected}:
                raise AssertionError(f"Query mismatch at depth={depth}, count={count}: {actual} != {expected}")
            query_cases.append((int(depth), int(count)))
    if lean.keys() != rust.keys():
        raise AssertionError(f"Different vector keys: Lean={lean.keys()}, Rust={rust.keys()}")
    for key in lean:
        if lean[key] != rust[key]:
            raise AssertionError(f"Differential mismatch in {key}:\nLean {lean[key]}\nRust {rust[key]}")
    if not lean_smoke.startswith("honest,") or not rust_smoke.startswith("honest,"):
        raise AssertionError("Missing successful opening smokes")
    print(f"PASS: {len(lean)} live arithmetic/encoding/folding/weight vectors; {len(query_cases)} production query batches {query_cases}")
    print("Lean ideal replay: " + lean_smoke)
    print("Rust production opening: " + rust_smoke)
    print("Boundary: no Lean refinement of bit arithmetic to Field, hash/FS/PoW, or cryptographic soundness is claimed.")


if __name__ == "__main__":
    main()
