#!/usr/bin/env python3
"""Package one real benchmark and reject an APK with a missing or wrong spec."""

import argparse
import json
from pathlib import Path
import shutil
import subprocess
import zipfile

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("function", choices=("shielded_prove",))
args = parser.parse_args()
name = f"leanvm_mobile_bench::{args.function}"
subprocess.run(
    [
        "mobench",
        "run",
        "--target",
        "android",
        "--crate-path",
        ".",
        "--function",
        name,
        "--release",
        "--iterations",
        "3",
        "--warmup",
        "1",
        "--output",
        f"target/package-check-{args.function}.json",
    ],
    check=True,
)
subprocess.run(
    [
        "mobench",
        "verify",
        "--target",
        "android",
        "--project-root",
        ".",
        "--crate-path",
        ".",
        "--check-artifacts",
        "--spec-path",
        "target/mobile-spec/android/bench_spec.json",
    ],
    check=True,
)
app = Path("android/app/build/outputs/apk/release/app-release-unsigned.apk")
test = Path("android/app/build/outputs/apk/androidTest/release/app-release-androidTest.apk")
for apk in (app, test):
    with zipfile.ZipFile(apk) as archive:
        spec = json.loads(archive.read("assets/bench_spec.json"))
        if (spec["function"], spec["iterations"], spec["warmup"]) != (name, 3, 1):
            raise ValueError(f"{apk}: benchmark specification differs from the requested workload")
        if apk == app:
            archive.getinfo("lib/arm64-v8a/libleanvm_mobile_bench.so")
output = Path("target/mobile-bench-packages") / args.function
output.mkdir(parents=True, exist_ok=True)
shutil.copyfile(app, output / "app.apk")
shutil.copyfile(test, output / "test.apk")
print(f"Packaged and checked {name}: ARM64 app and instrumentation APKs with the requested embedded specification")
