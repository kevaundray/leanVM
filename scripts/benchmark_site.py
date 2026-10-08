#!/usr/bin/env python3
"""Collect inert benchmark JSON from explicitly selected GitHub Actions sources."""

import argparse
import hashlib
import io
import json
import math
import re
import statistics
import subprocess
import sys
import zipfile
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MAX_JSON = 4 * 1024 * 1024
MAX_ARCHIVE = 32 * 1024 * 1024
PROGRAMS = {
    "fibonacci-asm-2000000": ("Fibonacci", "2,000,000 steps modulo 2^64", "bins/leanvm/src/workload.rs"),
    "hash-50000": ("BLAKE2s guest", "Hash 50,000 bytes through the precompile", "programs/hash/guest/src/main.rs"),
    "leanxmss-100": ("leanXMSS", "Verify 100 signatures", "programs/leanxmss/guest/src/main.rs"),
    "leansphincs-26": ("leanSPHINCS", "Verify 26 signatures", "programs/leansphincs/guest/src/main.rs"),
    "falcon-7": ("Falcon-512", "Verify 7 signatures", "programs/falcon/guest/src/main.rs"),
    "stateproof-5": ("L1 state proofs", "Verify 5 account and storage reads", "programs/stateproof/guest/src/main.rs"),
    "shielded-258": ("Shielded transfers", "258 spends, 516 input notes", "programs/shielded/guest/src/main.rs"),
}
SHA = re.compile(r"[0-9a-f]{40}")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def warn(message):
    print(f"benchmark-site: {message}", file=sys.stderr)


def api(path, binary=False):
    result = subprocess.run(["gh", "api", path], capture_output=True, timeout=120, check=True)
    require(len(result.stdout) <= MAX_ARCHIVE, "API response too large")
    return result.stdout if binary else json.loads(result.stdout)


def archive_json(data, name):
    # Never extract archives or execute downloaded files, including PR artifacts.
    require(len(data) <= MAX_ARCHIVE, "archive too large")
    with zipfile.ZipFile(io.BytesIO(data)) as archive:
        matches = [entry for entry in archive.infolist() if entry.filename == name]
        require(len(matches) == 1, f"expected one {name}")
        require(matches[0].file_size <= MAX_JSON, f"{name} too large")
        return json.loads(archive.read(matches[0]))


def artifact_bytes(repo, artifact):
    require(not artifact["expired"], "artifact expired")
    require(artifact["size_in_bytes"] <= MAX_ARCHIVE, "artifact too large")
    return api(f"repos/{repo}/actions/artifacts/{artifact['id']}/zip", binary=True)


def artifacts(repo, run_id):
    return api(f"repos/{repo}/actions/runs/{run_id}/artifacts?per_page=100")["artifacts"]


def positive(value):
    require(type(value) in (int, float) and math.isfinite(value) and value > 0, "invalid timing")
    return value


def instant(value):
    require(isinstance(value, str), "missing timestamp")
    parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
    require(parsed.tzinfo is not None, "timestamp must include timezone")
    return parsed


def workload(name):
    threads = re.search(r"-(\d+)thread(?:-|$)", name)
    count = int(threads[1]) if threads else None
    clean = re.sub(r"-\d+thread", "", name)
    if clean in PROGRAMS:
        title, description, path = PROGRAMS[clean]
        return title, description, path, "program", count
    tree = re.fullmatch(r"aggregate-leanxmss-100-(2|4)to1-(first|node)", clean)
    if tree:
        arity, level = tree.groups()
        description = (f"{arity} to 1, first-level node over {arity} copies of a 100-signature leaf proof"
                       if level == "first" else
                       f"{arity} to 1, higher node over {arity} tree proofs; 100-signature leaves")
        return "leanXMSS aggregation", description, "crates/leanvm_core/src/rec/tree/mod.rs", "aggregation", count
    return None


def expected_benchmarks():
    names = set(PROGRAMS)
    names.update(f"leanxmss-100-{n}thread" for n in (1, 4, 8))
    names.update(f"aggregate-leanxmss-100-{arity}to1{suffix}"
                 for arity in (2, 4) for suffix in ("", "-1thread", "-4thread", "-8thread"))
    return names


def machine_id(machine):
    fields = {key: machine[key] for key in ("name", "arch", "os", "cpu", "logical_cpus", "memory_bytes")}
    return hashlib.sha256(json.dumps(fields, sort_keys=True).encode()).hexdigest()[:16]


def row(name, description, path, category, count, samples, machine, source, verification=None):
    require(samples and len(samples) <= 100, "invalid sample count")
    samples = [positive(sample) for sample in samples]
    machine = dict(machine, id=machine_id(machine))
    identity = [name, description, category, machine["id"], count, source["kind"]]
    return {
        "id": hashlib.sha256(json.dumps(identity).encode()).hexdigest()[:24],
        "program": {"name": name, "source_url": f"https://github.com/{source['repository']}/blob/{source['commit']}/{path}"},
        "workload": description,
        "category": category,
        "machine": machine,
        "threads": {"count": count, "label": f"{count} thread{'s' if count != 1 else ''}" if count else "Default (not recorded)"},
        "median_seconds": statistics.median(samples),
        "min_seconds": min(samples),
        "max_seconds": max(samples),
        "samples_seconds": samples,
        "source": source,
        "verification": verification,
    }


def log_machines(data):
    """Read each job's own CPU log, not another job's nominal runner specification."""
    machines = {}
    with zipfile.ZipFile(io.BytesIO(data)) as archive:
        for entry in archive.infolist():
            match = re.fullmatch(r"(.+) \((x86-64|arm64)\)/\d+_CPU.txt", entry.filename)
            if not match or entry.file_size > MAX_JSON:
                continue
            text = archive.read(entry).decode("utf-8-sig")
            cpu = re.search(r"Z Model name:\s+([^\r\n]+)", text)
            count = re.search(r"Z CPU\(s\):\s+(\d+)", text)
            os = re.search(r"Z (Linux [^\r\n]+)", text)
            machines[(match[1], match[2])] = {
                "cpu": cpu[1].strip() if cpu else None,
                "logical_cpus": int(count[1]) if count else None,
                "os": os[1] if os else None,
            }
    return machines


def desktop_rows(document, benchmark, run, config, hardware):
    repo, branch = config["repository"], config["branch"]
    require(SHA.fullmatch(document["base"]), "invalid base revision")
    prs = [pr for pr in run["pull_requests"] if pr["number"] == document["pr"] and pr["base"]["ref"] == branch]
    require(run["event"] == "pull_request" and len(prs) == 1, "not a selected baseline PR run")
    arch = document["testbed"]
    require(arch in ("x86-64", "arm64"), "unknown testbed")
    cpu = document["cpu"]
    require(isinstance(cpu, str) and 0 < len(cpu) <= 200, "missing CPU model")
    if hardware.get("cpu"):
        require(cpu == hardware["cpu"], "CPU log and artifact disagree")
    machine = {"name": cpu, "arch": arch, "os": hardware.get("os"), "cpu": cpu,
               "logical_cpus": hardware.get("logical_cpus"), "memory_bytes": None}
    expected = {benchmark + "-first", benchmark + "-node"} if benchmark.startswith("aggregate-") else {benchmark}
    rounds = [sample for sample in document["runs"] if sample["side"] == "base"]
    require(len(rounds) == config["rounds"], "incomplete baseline rounds")
    require({sample["round"] for sample in rounds} == set(range(1, config["rounds"] + 1)), "duplicate/missing rounds")
    for sample in rounds:
        require(set(sample["results"]) == expected, "unexpected workload or incomplete aggregation")
    source = {"repository": repo, "branch": branch, "commit": document["base"],
              "run_url": run["html_url"], "measured_at": run["created_at"],
              "kind": "branch", "label": f"{branch} baseline (PR #{document['pr']} base)",
              "timestamp_basis": "workflow start; individual sample timestamps not recorded"}
    results = []
    for name in sorted(expected):
        definition = workload(name)
        require(definition is not None, "unsupported workload")
        samples = []
        for sample in sorted(rounds, key=lambda item: item["round"]):
            metric = sample["results"][name]["latency"]
            # Each A/B round must represent one measurement, not a mean of several.
            require(metric["value"] == metric["lower_value"] == metric["upper_value"], "round is not a single sample")
            samples.append(positive(metric["value"]) / 1e9)
        title, description, path, category, count = definition
        results.append(row(title, description, path, category, count, samples, machine, source))
    return results


def mobile_rows(metadata, raw, run, selected):
    require(metadata["status"] == "complete" and metadata["device_validated"] is True, "incomplete mobile run")
    require(metadata["source_sha"] == selected["commit"] == run["head_sha"], "mobile revision mismatch")
    require(metadata["source_repository"] == selected["repository"], "mobile repository mismatch")
    require(str(metadata["workflow_run_id"]) == str(run["id"]), "mobile run mismatch")
    require(metadata["trigger_ref"] == f"refs/heads/{selected['branch']}", "mobile branch mismatch")
    definitions = {
        "leanvm_mobile_bench::shielded_prove": (
            "Shielded transfers", "2 spends, 4 input notes; standalone proof, leaf log inverse rate 2",
            "programs/shielded/guest/src/main.rs", "program",
            {"spends_per_leaf": 2, "leaf_log_inv_rate": 2}),
        "leanvm_mobile_bench::shielded_aggregate": (
            "Shielded aggregation",
            "2 to 1; two independently proven 2-spend leaves, 4 spends and 8 input notes total; leaf setup excluded; leaf rate 2, tree rate 1",
            "bench-mobile/src/lib.rs", "aggregation",
            {"spends_per_leaf": 2, "leaf_log_inv_rate": 2, "aggregation_leaves": 2,
             "aggregation_log_inv_rate": 1, "verified_leaves": 2}),
    }
    expected = metadata["functions"]
    require(expected and len(set(expected)) == len(expected) and set(expected) <= definitions.keys(), "unsupported mobile functions")
    per_function = metadata.get("benchmarks")
    if per_function is not None:
        require(set(per_function) == set(expected), "incomplete per-function metadata")
    else:
        require(expected == ["leanvm_mobile_bench::shielded_prove"], "missing per-function metadata")
    device = metadata["requested_device"]
    device_version = f"{device}-{metadata['requested_os_version']}"
    measured = {}
    for report in raw:
        require(len(report["benchmark_results"]) == 1, "ambiguous mobile device")
        observed_device, functions = next(iter(report["benchmark_results"].items()))
        require(observed_device in (device, device_version) and functions, "mobile device mismatch")
        if per_function is not None:
            summary = report["summary"]
            require(summary["target"] == metadata["requested_os"] and summary["devices"] == [device_version], "mobile platform mismatch")
            require(summary["warmup"] == metadata["warmup"] and summary["iterations"] == metadata["iterations"], "mobile summary specification mismatch")
            names = [result["function"] for result in functions]
            require(summary["function"] == (names[0] if len(names) == 1 else "multiple"), "mobile summary function mismatch")
            devices = summary["device_summaries"]
            require(len(devices) == 1 and devices[0]["device"] in (device, device_version), "mobile summary device mismatch")
            summaries = devices[0]["benchmarks"]
            require(len(summaries) == len(names) and {item["function"] for item in summaries} == set(names), "incomplete mobile summary")
            require(all(item["samples"] == metadata["iterations"] and not item.get("failure") for item in summaries), "failed mobile summary")
        for result in functions:
            function = result["function"]
            require(function in expected and function not in measured, "unexpected or duplicate mobile function")
            require(not result.get("failure"), "failed mobile benchmark")
            measured[function] = result
    require(set(measured) == set(expected), "missing mobile function")
    machine = {"name": device, "arch": "aarch64", "os": f"{metadata['requested_os']} {metadata['requested_os_version']}",
               "cpu": metadata.get("soc"), "logical_cpus": None, "memory_bytes": None}
    rows = []
    for function in expected:
        result = measured[function]
        title, description, path, category, required = definitions[function]
        metrics = result["custom_metrics"]["run_u64"]
        recorded = per_function[function] if per_function is not None else metadata
        for key, value in required.items():
            require(type(metrics[key]) is int and metrics[key] == value, f"mobile {key} mismatch")
            if key in recorded:
                require(recorded[key] == value, f"mobile recorded {key} mismatch")
        if per_function is not None:
            require(all(type(value) is int and metrics.get(key) == value for key, value in recorded.items()), "mobile metrics mismatch")
            require(set(required) | {"threads", "available_parallelism", "verified_proofs"} <= recorded.keys(), "missing mobile metrics")
            require([sample["duration_ns"] for sample in result["samples"]] == result["samples_ns"], "mobile sample records disagree")
        count = recorded["threads"]
        require(type(count) is int and 0 < count <= 1024 and metrics["threads"] == count, "mobile thread mismatch")
        if "available_parallelism" in recorded:
            require(recorded["available_parallelism"] == count == metrics["available_parallelism"], "mobile parallelism mismatch")
        samples = result["samples_ns"]
        require(len(samples) == metadata["iterations"] == result["spec"]["iterations"], "incomplete mobile samples")
        require(result["spec"]["warmup"] == metadata["warmup"], "mobile warmup mismatch")
        total = metadata["warmup"] + len(samples)
        require(recorded["verified_proofs"] == metrics["verified_proofs"] == total, "mobile proofs not all verified")
        samples = [positive(sample) / 1e9 for sample in samples]
        timestamp = datetime.fromtimestamp(result["resources"]["timestamp_ms"] / 1000, timezone.utc).isoformat().replace("+00:00", "Z")
        source = {"repository": selected["repository"], "branch": selected["branch"], "commit": selected["commit"],
                  "run_url": run["html_url"], "measured_at": timestamp, "kind": "pull_request", "label": selected["label"]}
        rows.append(row(title, description, path, category, count, samples, machine, source,
                        {"verified_proofs": total, "total_proofs": total}))
    return rows


def validate(snapshot):
    require(snapshot["schema_version"] == 1, "unsupported schema")
    instant(snapshot["generated_at"])
    require(isinstance(snapshot["results"], list) and len(snapshot["results"]) <= 10000, "invalid results")
    seen = set()
    for result in snapshot["results"]:
        require(result["id"] not in seen, "duplicate result")
        seen.add(result["id"])
        require(result["category"] in ("program", "aggregation"), "unsupported category")
        require(result["program"]["source_url"].startswith("https://github.com/"), "invalid source link")
        require(SHA.fullmatch(result["source"]["commit"]), "invalid revision")
        instant(result["source"]["measured_at"])
        samples = result["samples_seconds"]
        require(samples and len(samples) <= 100, "invalid samples")
        for sample in samples:
            positive(sample)
        require(result["median_seconds"] == statistics.median(samples), "median mismatch")
        require(result["min_seconds"] == min(samples) and result["max_seconds"] == max(samples), "range mismatch")
        count = result["threads"]["count"]
        require(count is None or type(count) is int and 0 < count <= 1024, "invalid threads")
    return snapshot


def merge(previous, candidates):
    results = {result["id"]: result for result in previous["results"]}
    for candidate in candidates:
        old = results.get(candidate["id"])
        if old is None or instant(candidate["source"]["measured_at"]) > instant(old["source"]["measured_at"]):
            results[candidate["id"]] = candidate
    ordered = sorted(results.values(), key=lambda item: (item["program"]["name"], item["workload"], item["machine"]["id"], item["threads"]["count"] or 0))
    if ordered == previous["results"]:
        return previous
    return validate({"schema_version": 1, "generated_at": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"), "results": ordered})


def restore(repo, branch):
    default_branch = api(f"repos/{repo}")["default_branch"]
    runs = api(f"repos/{repo}/actions/workflows/benchmark-site.yml/runs?status=success&per_page=10")["workflow_runs"]
    for run in runs:
        trusted = (run["event"] in ("push", "workflow_dispatch") and run["head_branch"] == branch
                   or run["event"] == "schedule" and run["head_branch"] == default_branch)
        if not trusted:
            continue
        for artifact in artifacts(repo, run["id"]):
            if artifact["name"] == "benchmark-data" and not artifact["expired"]:
                return validate(archive_json(artifact_bytes(repo, artifact), "latest.json"))["results"]
    return []


def collect_desktop(config):
    repo, branch = config["repository"], config["branch"]
    runs = api(f"repos/{repo}/actions/workflows/{config['workflow']}/runs?status=success&event=pull_request&per_page={config['recent_runs']}")["workflow_runs"]
    accepted = set()
    revisions = {}
    candidates = []
    expected = expected_benchmarks()
    for run in runs:
        if run["conclusion"] != "success" or run["path"] != f".github/workflows/{config['workflow']}":
            continue
        if not any(pr["base"]["ref"] == branch for pr in run["pull_requests"]):
            continue
        run_artifacts = artifacts(repo, run["id"])
        try:
            hardware = log_machines(api(f"repos/{repo}/actions/runs/{run['id']}/logs", binary=True))
        except (ValueError, KeyError, subprocess.SubprocessError, zipfile.BadZipFile) as error:
            warn(f"run {run['id']}: hardware logs unavailable ({error}); retaining existing results")
            continue
        for artifact in run_artifacts:
            match = re.fullmatch(r"ab-(x86-64|arm64)-(.+)", artifact["name"])
            if not match or match[2] not in expected:
                continue
            try:
                machine = hardware.get((match[2], match[1]))
                require(machine and machine["cpu"] and machine["logical_cpus"] and machine["os"], "missing hardware evidence")
                configuration = (match.groups(), json.dumps(machine, sort_keys=True))
                if configuration in accepted:
                    continue
                document = archive_json(artifact_bytes(repo, artifact), "ab.json")
                require(document["testbed"] == match[1], "artifact testbed mismatch")
                revision = document["base"]
                require(SHA.fullmatch(revision), "invalid base revision")
                if revision not in revisions:
                    comparison = api(f"repos/{repo}/compare/{revision}...{branch}")
                    revisions[revision] = comparison["status"] in ("ahead", "identical")
                require(revisions[revision], "base is not on the selected branch")
                candidates.extend(desktop_rows(document, match[2], run, config, machine))
                accepted.add(configuration)
            except (ValueError, KeyError, TypeError, subprocess.SubprocessError, zipfile.BadZipFile) as error:
                warn(f"{artifact['name']}: retaining prior data ({error})")
    print(f"Collected {len(candidates)} desktop rows from {len(accepted)} benchmark artifacts")
    return candidates


def collect_mobile(selected):
    repo = selected["repository"]
    run = api(f"repos/{repo}/actions/runs/{selected['run_id']}")
    require(run["conclusion"] == "success" and run["head_sha"] == selected["commit"], "unapproved mobile run")
    require(run["path"] == f".github/workflows/{selected['workflow']}" and run["head_branch"] == selected["branch"], "mobile workflow mismatch")
    candidates = []
    for artifact in artifacts(repo, run["id"]):
        if artifact["name"] not in ("mobile-bench-ios-results", "mobile-bench-android-results"):
            continue
        try:
            data = artifact_bytes(repo, artifact)
            candidates.extend(mobile_rows(archive_json(data, "metadata.json"), archive_json(data, "raw-results.json"), run, selected))
        except (ValueError, KeyError, TypeError, subprocess.SubprocessError, zipfile.BadZipFile) as error:
            warn(f"{artifact['name']}: retaining prior data ({error})")
    print(f"Collected {len(candidates)} mobile rows from approved run {run['id']}")
    return candidates


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "site/benchmarks/latest.json")
    parser.add_argument("--sources", type=Path, default=ROOT / "scripts/benchmark-sources.json")
    parser.add_argument("--check", action="store_true", help="validate the existing snapshot without network access")
    parser.add_argument("--restore-repository", help="restore prior published data before collecting")
    parser.add_argument("--restore-branch", default="riscv-exploration")
    args = parser.parse_args()
    snapshot = validate(json.loads(args.output.read_text())) if args.output.exists() else {
        "schema_version": 1, "generated_at": datetime.now(timezone.utc).isoformat(), "results": []}
    if args.check:
        require(snapshot["results"], "snapshot is empty")
        print(f"Valid snapshot: {len(snapshot['results'])} rows")
        return
    config = json.loads(args.sources.read_text())
    if args.restore_repository:
        try:
            snapshot = merge(snapshot, restore(args.restore_repository, args.restore_branch))
        except (ValueError, KeyError, TypeError, subprocess.SubprocessError, zipfile.BadZipFile) as error:
            warn(f"previous publication unavailable, keeping committed snapshot ({error})")
    collectors = [(collect_desktop, config["desktop"])] + [(collect_mobile, selected) for selected in config["mobile"]]
    for collect, selected in collectors:
        try:
            snapshot = merge(snapshot, collect(selected))
        except (ValueError, KeyError, TypeError, subprocess.SubprocessError, zipfile.BadZipFile) as error:
            warn(f"source unavailable, keeping prior valid data ({error})")
    require(snapshot["results"], "no valid results available")
    validate(snapshot)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.output.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(snapshot, indent=2, allow_nan=False) + "\n")
    temporary.replace(args.output)
    print(f"Published {len(snapshot['results'])} rows to {args.output}")


if __name__ == "__main__":
    main()
