#!/usr/bin/env python3
"""Run trusted mobile benchmarks without publishing provider logs or signed URLs."""

import base64
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from urllib.parse import quote


DEVICE = "Google Pixel 7-13.0"
FUNCTIONS = (
    "leanvm_mobile_bench::shielded_prove",
    "leanvm_mobile_bench::shielded_aggregate",
)
MOBENCH_REV = "217cfd4f78db1284276a1a1da44e3bf473729f5c"
URL = re.compile(r"[A-Za-z][A-Za-z0-9+.-]*://[^\s<>\"'`]+")
PRIVATE_KEY = re.compile(r"url|uri|token|password|credential|authorization|access.?key|username", re.IGNORECASE)


def redactor():
    credentials = [os.environ.get(name, "") for name in ("BROWSERSTACK_USERNAME", "BROWSERSTACK_ACCESS_KEY")]
    values = [value for value in credentials if value]
    if all(credentials):
        values.append(":".join(credentials))
    secrets = set()
    for value in values:
        secrets.update((value, quote(value, safe=""), base64.b64encode(value.encode()).decode()))

    def text(value):
        for secret in sorted(secrets, key=len, reverse=True):
            value = value.replace(secret, "[redacted]")
        return URL.sub("[URL removed]", value)

    def clean(value):
        if isinstance(value, dict):
            return {text(key): clean(item) for key, item in value.items() if not PRIVATE_KEY.search(key)}
        if isinstance(value, list):
            return [clean(item) for item in value]
        if isinstance(value, str):
            return text(value)
        return value

    return text, clean


def export_reports(source, destination, clean, text):
    raw = []
    for path in sorted(source.rglob("summary.json")):
        report = json.loads(path.read_text())
        relative = path.relative_to(source)
        output = destination / relative
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(clean(report), indent=2) + "\n")
        if "benchmark_results" in report:
            raw.append({"source": str(relative), "benchmark_results": clean(report["benchmark_results"])})
        for name in ("summary.md", "results.csv"):
            sibling = path.with_name(name)
            if sibling.is_file():
                output.with_name(name).write_text(text(sibling.read_text()))
    (destination / "raw-results.json").write_text(json.dumps(raw, indent=2) + "\n")


def export_diagnostics(private, destination, text):
    excerpts = []
    for name in ("command.log", "command.stdout"):
        path = private / name
        with path.open("rb") as source:
            source.seek(max(0, path.stat().st_size - 16384))
            excerpts.extend(source.read().decode(errors="replace").splitlines()[-20:])
    (destination / "diagnostics.txt").write_text(text("\n".join(excerpts)) + "\n")


def main():
    os.umask(0o077)
    destination = Path("target/mobile-bench-results")
    destination.mkdir(parents=True, exist_ok=False)
    text, clean = redactor()
    metadata = {
        "source_sha": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
        "source_repository": os.environ.get("GITHUB_REPOSITORY"),
        "trigger_ref": os.environ.get("GITHUB_REF"),
        "event": os.environ.get("GITHUB_EVENT_NAME"),
        "workflow_run_id": os.environ.get("GITHUB_RUN_ID"),
        "workflow_run_attempt": os.environ.get("GITHUB_RUN_ATTEMPT"),
        "rustc": subprocess.check_output(["rustc", "--version"], text=True).strip(),
        "mobench_revision": MOBENCH_REV,
        "cargo_ndk_version": "4.1.2",
        "android_ndk_version": "26.1.10909125",
        "android_sdk": 34,
        "android_build_tools": "34.0.0",
        "target": "aarch64-linux-android",
        "profile": "release",
        "rustflags": os.environ.get("RUSTFLAGS"),
        "threads": 1,
        "candidate_device": DEVICE,
        "device_validated": False,
        "functions": list(FUNCTIONS),
        "spends_per_leaf": 1,
        "aggregation_leaves": 2,
        "warmup": 1,
        "iterations": 3,
        "soc": None,
        "thermal_data": None,
        "status": "not_started",
    }
    exit_code = 1
    try:
        if not all(os.environ.get(name) for name in ("BROWSERSTACK_USERNAME", "BROWSERSTACK_ACCESS_KEY")):
            metadata["status"] = "missing_credentials"
            print("BrowserStack credentials are missing. App Automate access and both repository secrets are required.")
            return 1
        with tempfile.TemporaryDirectory(prefix="mobile-bench-private-") as private:
            private = Path(private)
            reports = private / "reports"
            commands = (
                ("device_catalog", ["mobench", "devices", "--platform", "android", "--json"]),
                ("device_validation", ["mobench", "devices", "--platform", "android", "--validate", DEVICE]),
                (
                    "benchmark_run",
                    [
                        "mobench",
                        "ci",
                        "run",
                        "--target",
                        "android",
                        "--crate-path",
                        ".",
                        "--functions",
                        ",".join(FUNCTIONS),
                        "--devices",
                        DEVICE,
                        "--release",
                        "--iterations",
                        "3",
                        "--warmup",
                        "1",
                        "--fetch",
                        "--plots",
                        "off",
                        "--android-benchmark-timeout-secs",
                        "1200",
                        "--fetch-timeout-secs",
                        "1500",
                        "--output-dir",
                        str(reports),
                        "--fetch-output-dir",
                        str(private / "browserstack"),
                    ],
                ),
            )
            for stage, command in commands:
                metadata["status"] = stage
                with (private / "command.log").open("wb") as log, (private / "command.stdout").open("wb") as stdout:
                    try:
                        result = subprocess.run(command, stdout=stdout, stderr=log, timeout=3600, check=False)
                    except subprocess.TimeoutExpired:
                        metadata["status"] = stage + "_timeout"
                        print(f"Mobile benchmark {stage} timed out.")
                        log.flush()
                        stdout.flush()
                        export_diagnostics(private, destination, text)
                        break
                metadata[stage + "_exit_code"] = result.returncode
                if result.returncode:
                    metadata["status"] = stage + "_failed"
                    export_diagnostics(private, destination, text)
                    print(f"Mobile benchmark {stage} failed (exit {result.returncode}); see sanitized diagnostics.txt.")
                    if stage == "device_validation":
                        print("Check App Automate entitlement, credentials, and the candidate device in BrowserStack.")
                    break
                if stage == "device_catalog":
                    output = (private / "command.stdout").read_text()
                    catalog = json.loads(output[output.index("[") :])
                    matches = [
                        device
                        for device in catalog
                        if device.get("device") == "Google Pixel 7" and device.get("os_version") == "13.0" and device.get("os") == "android"
                    ]
                    metadata["catalog_matches"] = [
                        {key: device.get(key) for key in ("device", "os", "os_version", "available")} for device in matches
                    ]
                    if not matches or all(device.get("available") is False for device in matches):
                        metadata["status"] = "candidate_device_unavailable"
                        print("The candidate Pixel 7 / Android 13.0 is not available in the authenticated device catalog.")
                        break
                if stage == "device_validation":
                    metadata["device_validated"] = True
            else:
                summary = json.loads((reports / "summary.json").read_text())["summary"]
                devices = [device["device"] for device in summary["device_summaries"]]
                measured = {benchmark["function"]: benchmark for device in summary["device_summaries"] for benchmark in device["benchmarks"]}
                if (
                    devices != [DEVICE]
                    or set(measured) != set(FUNCTIONS)
                    or any(measured[function].get("samples") != 3 or measured[function].get("failure") for function in FUNCTIONS)
                ):
                    metadata["status"] = "incomplete_results"
                    print("BrowserStack did not return three successful samples for both benchmarks on the requested model and OS.")
                else:
                    metadata["status"] = "complete"
                    exit_code = 0
            export_reports(reports, destination, clean, text)
    except (OSError, ValueError, KeyError, TypeError):
        metadata["status"] = "execution_or_report_error"
        exit_code = 1
        print("Mobile benchmark execution or report export failed. No raw provider diagnostics are published.")
    finally:
        (destination / "metadata.json").write_text(json.dumps(clean(metadata), indent=2) + "\n")
    if exit_code == 0:
        print("Both shielded benchmarks completed; sanitized reports are in target/mobile-bench-results.")
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
