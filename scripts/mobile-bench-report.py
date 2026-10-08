#!/usr/bin/env python3
"""Render verified mobile results in Actions and update the matching current-head PR comment."""

import argparse
import json
import math
import os
from pathlib import Path
import re
import statistics
import subprocess


MARKER = "<!-- leanvm-mobile-bench -->"
FUNCTION = "leanvm_mobile_bench::shielded_prove"
DEVICES = {
    "android": ("Google Pixel 7", "13.0", "Android"),
    "ios": ("iPhone 14", "16", "iOS"),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def positive(value):
    return type(value) is int and value > 0


def render(directory, repository, head, run_id):
    require(re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository), "invalid repository")
    require(re.fullmatch(r"[0-9a-f]{40}", head), "invalid commit")
    require(run_id.isdecimal() and int(run_id) > 0, "invalid run ID")
    metadata = json.loads((directory / "metadata.json").read_text())
    require(metadata["source_repository"] == repository, "source repository mismatch")
    require(metadata["source_sha"] == head, "source commit mismatch")
    require(metadata["workflow_run_id"] == run_id, "workflow run mismatch")
    platform = metadata["platform"]
    require(platform in DEVICES, "unexpected platform")
    model, version, os_name = DEVICES[platform]
    link = f"https://github.com/{repository}/actions/runs/{run_id}"
    prefix = f"### Mobile benchmarks: {model} / {os_name} {version}\n\n[Actions run and full artifacts]({link}) · Source `{head}`.\n\n"
    if metadata["status"] != "complete":
        return prefix + "The device benchmark did not complete successfully. No performance result is published.\n", False, platform
    require(metadata["device_validated"] is True, "device was not validated")
    require(metadata["candidate_device"] == f"{model}-{version}", "unexpected device")
    require(metadata["functions"] == [FUNCTION], "unexpected workload")
    require(metadata["spends_per_leaf"] == 2 and metadata["warmup"] == 1 and metadata["iterations"] == 3, "unexpected workload shape")
    require(metadata["verified_proofs"] == 4, "not all proofs verified")
    threads = metadata["threads"]
    require(positive(threads) and threads == metadata["available_parallelism"], "invalid thread count")
    raw = json.loads((directory / "raw-results.json").read_text())
    require(len(raw) == 1, "expected one report")
    devices = raw[0]["benchmark_results"]
    require(len(devices) == 1, "unexpected measured device")
    measured_device = next(iter(devices))
    require(measured_device in (model, f"{model}-{version}") and len(devices[measured_device]) == 1, "unexpected measured device")
    result = devices[measured_device][0]
    require(result["function"] == FUNCTION, "unexpected measured function")
    require(result["spec"] == {"name": FUNCTION, "warmup": 1, "iterations": 3}, "unexpected measured specification")
    metrics = result["custom_metrics"]["run_u64"]
    for key in ("threads", "available_parallelism", "spends_per_leaf", "verified_proofs"):
        require(type(metrics[key]) is int and metrics[key] == metadata[key], f"{key} mismatch")
    samples = result["samples_ns"]
    require(len(samples) == 3 and all(positive(value) and math.isfinite(value) for value in samples), "invalid samples")
    require([sample["duration_ns"] for sample in result["samples"]] == samples, "sample records disagree")
    median = statistics.median(samples) / 1e9
    body = prefix + "\n".join(
        [
            "| Benchmark | Device / OS | Threads | Median | Sample range | Verified proofs |",
            "|---|---|---:|---:|---:|---:|",
            f"| Shielded, 2 spends | {model} / {os_name} {version} | {threads} | {median:.3f} s | {min(samples) / 1e9:.3f} to {max(samples) / 1e9:.3f} s | 4 / 4 |",
            "",
            "Samples: " + ", ".join(f"{value / 1e9:.9f} s" for value in samples) + ".",
            "",
        ]
    )
    return body, True, platform


def gh(endpoint, method="GET", payload=None):
    command = ["gh", "api", endpoint, "--method", method]
    if payload is not None:
        command += ["--input", "-"]
    output = subprocess.check_output(command, input=None if payload is None else json.dumps(payload), text=True)
    return json.loads(output) if output.strip() else None


def pages(endpoint):
    page = 1
    while True:
        rows = gh(f"{endpoint}{'&' if '?' in endpoint else '?'}per_page=100&page={page}")
        yield from rows
        if len(rows) < 100:
            break
        page += 1


def post(repository, source_repository, head, body):
    # The artifact cannot select a PR. GitHub supplies candidates, and each current head is checked again before writing.
    owner = source_repository.split("/")[0]
    prs = [pr for pr in pages(f"repos/{repository}/pulls?state=open") if pr["head"]["sha"] == head]
    for pr in prs:
        number = pr["number"]
        current = gh(f"repos/{repository}/pulls/{number}")
        if current["head"]["sha"] != head or current["head"]["repo"]["full_name"] != source_repository:
            continue
        comments = list(pages(f"repos/{repository}/issues/{number}/comments"))
        mine = [c for c in comments if c["user"]["login"] in ("github-actions[bot]", owner) and c["body"].startswith(MARKER)]
        # Recheck after fetching comments so an updated PR does not receive a stale measurement.
        if gh(f"repos/{repository}/pulls/{number}")["head"]["sha"] != head:
            continue
        payload = {"body": MARKER + "\n" + body}
        if mine:
            gh(f"repos/{repository}/issues/comments/{mine[0]['id']}", "PATCH", payload)
        else:
            gh(f"repos/{repository}/issues/{number}/comments", "POST", payload)
        print(f"Published mobile results on {repository}#{number}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path, nargs="+")
    parser.add_argument("--repository", required=True)
    parser.add_argument("--head", required=True)
    parser.add_argument("--run-id", required=True)
    parser.add_argument("--comment-repository")
    args = parser.parse_args()
    reports = [render(directory, args.repository, args.head, args.run_id) for directory in args.directory]
    require(len({platform for _, _, platform in reports}) == len(reports), "duplicate platform reports")
    for directory, (section, _, _) in zip(args.directory, reports):
        (directory / "ci-summary.md").write_text(section)
    body = "\n".join(section for section, _, _ in reports)
    complete = any(success for _, success, _ in reports)
    if summary := os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(summary, "a") as output:
            output.write(body)
    print(body)
    if args.comment_repository and complete:
        require(re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", args.comment_repository), "invalid comment repository")
        post(args.comment_repository, args.repository, args.head, body)


if __name__ == "__main__":
    main()
