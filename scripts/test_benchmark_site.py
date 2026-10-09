"""A snapshot is publishable only when every planned fresh measurement is valid."""

from copy import deepcopy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import benchmark_site as site


CREATED = "2026-01-02T00:00:00Z"
MEASURED = "2026-01-02T01:00:00Z"


def desktop_fixture(plan, testbed, benchmark):
    machine = {"name": f"Test {testbed}", "arch": testbed, "os": "Linux test", "cpu": f"Test {testbed}",
               "logical_cpus": 16, "memory_bytes": 64 * 1024 ** 3}
    machine["id"] = site.machine_id(machine)
    count = site.workload(site.expected_results(benchmark)[0])[4] or 16
    samples = []
    for number in range(1, plan["rounds"] + 1):
        value = (1, 9, 2)[(number - 1) % 3] * 1_000_000_000
        results = {name: {"latency": {"value": value, "lower_value": value, "upper_value": value},
                          "verify": {"value": 10, "lower_value": 5, "upper_value": 15},
                          "proof-size": {"value": 1024},
                          "peak-memory": {"value": (7, 3, 5)[(number - 1) % 3] * 1024 ** 2}}
                   for name in site.expected_results(benchmark)}
        samples.append({"round": number, "measured_at": MEASURED, "exit_code": 0, "threads": count, "results": results})
    return {"schema_version": 2, "snapshot": deepcopy(plan["snapshot"]), "plan_id": site.digest(plan),
            "testbed": testbed, "benchmark": benchmark, "machine": machine, "threads": count, "samples": samples}


def mobile_fixture(plan, platform):
    report = site.mobile_report
    model, version, _ = report.DEVICES[platform]
    metadata = {"source_repository": plan["snapshot"]["repository"], "source_sha": plan["snapshot"]["commit"],
                "workflow_run_id": str(plan["snapshot"]["run_id"]), "platform": platform, "status": "complete",
                "device_validated": True, "candidate_device": f"{model}-{version}", "functions": list(report.FUNCTIONS),
                "warmup": 1, "iterations": 3, "threads": 6, "available_parallelism": 6,
                "measured_at": MEASURED, "timestamp_basis": "collection_completed_at", "trigger_ref": "refs/heads/main"}
    entries = []
    for index, function in enumerate(report.FUNCTIONS, 1):
        metrics = dict(report.WORKLOADS[function], threads=6, available_parallelism=6)
        samples = [1_000_000_000, 9_000_000_000, 2_000_000_000]
        entries.append({"function": function, "spec": {"name": function, "warmup": 1, "iterations": 3},
                        "custom_metrics": {"run_u64": metrics}, "samples_ns": samples,
                        "samples": [{"duration_ns": value, "process_peak_memory_kb": peak * index}
                                    for value, peak in zip(samples, (2048, 1024, 3072))]})
    metadata["benchmarks"] = report.benchmark_metrics({entry["function"]: entry for entry in entries})
    raw = [{"summary": {"target": platform, "function": "multiple", "warmup": 1, "iterations": 3,
                        "devices": [metadata["candidate_device"]],
                        "device_summaries": [{"device": model, "benchmarks": [
                            {"function": entry["function"], "samples": 3} for entry in entries]}]},
            "benchmark_results": {model: entries}}]
    return metadata, raw


class SnapshotTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.artifacts = self.root / "artifacts"
        self.artifacts.mkdir()
        self.output = self.root / "latest.json"
        self.plan = site.make_plan("example/leanVM", "a" * 40, 123, 3)
        self.plan["created_at"] = CREATED
        for testbed in site.TESTBEDS:
            for benchmark in self.plan["desktop"]["benchmarks"]:
                directory = self.artifacts / f"snapshot-result-desktop-{testbed}-{benchmark}"
                directory.mkdir()
                self.save(directory / "result.json", desktop_fixture(self.plan, testbed, benchmark))
        for platform in ("ios", "android"):
            directory = self.artifacts / f"snapshot-result-mobile-{platform}"
            directory.mkdir()
            metadata, raw = mobile_fixture(self.plan, platform)
            self.save(directory / "metadata.json", metadata)
            self.save(directory / "raw-results.json", raw)
        self.desktop = self.artifacts / "snapshot-result-desktop-x86-64-leanxmss-100-4thread" / "result.json"
        self.mobile = self.artifacts / "snapshot-result-mobile-ios"

    def save(self, path, value):
        path.write_text(json.dumps(value))

    def publish(self):
        return site.publish(self.plan, self.artifacts, self.output)

    def assert_refused_without_mutation(self):
        self.output.write_bytes(b"previous published bytes\n")
        with self.assertRaises((ValueError, KeyError, TypeError, OSError)):
            self.publish()
        self.assertEqual(self.output.read_bytes(), b"previous published bytes\n")

    def test_complete_snapshot_has_global_provenance_and_independent_samples(self):
        snapshot = self.publish()
        self.assertEqual(snapshot["snapshot"], self.plan["snapshot"])
        self.assertEqual(snapshot["schema_version"], 3)
        self.assertEqual(len(snapshot["results"]), 56)
        for row in snapshot["results"]:
            self.assertEqual(row["samples_seconds"], [1, 9, 2])
            self.assertEqual((row["median_seconds"], row["min_seconds"], row["max_seconds"]), (2, 1, 9))
            self.assertNotIn("source", row)
            self.assertIn(f"/blob/{self.plan['snapshot']['commit']}/", row["program"]["source_url"])
            self.assertEqual(row["verification"]["verified_proofs"], row["verification"]["total_proofs"])
            expected_peak = (6 if row["category"] == "aggregation" else 3) if row["machine"]["arch"] == "aarch64" else 7
            self.assertEqual(row["peak_memory_bytes"], expected_peak * 1024 ** 2)
            self.assertTrue(row["peak_memory_method"].strip())
        self.assertEqual(site.load(self.output), snapshot)
        aggregate = [row for row in snapshot["results"] if row["program"]["name"] == "Shielded aggregation"]
        self.assertEqual(len(aggregate), 2)
        self.assertEqual(aggregate[0]["verification"]["parameters"]["verified_leaves"], 2)
        self.assertEqual(aggregate[0]["verification"]["parameters"]["aggregation_log_inv_rate"], 1)

    def test_aggregation_keeps_each_levels_round_maximum(self):
        benchmark = "aggregate-leanxmss-100-2to1"
        document = desktop_fixture(self.plan, "x86-64", benchmark)
        for sample, first, node in zip(document["samples"], (11, 4, 8), (13, 17, 12)):
            sample["results"][benchmark + "-first"]["peak-memory"]["value"] = first * 1024
            sample["results"][benchmark + "-node"]["peak-memory"]["value"] = node * 1024
        rows = site.desktop_rows(document, self.plan, "x86-64", benchmark)
        self.assertEqual([row["peak_memory_bytes"] for row in rows], [11 * 1024, 17 * 1024])

    def test_missing_or_invalid_desktop_memory_cannot_replace_snapshot(self):
        original = site.load(self.desktop)
        for value in (None, 0, -1, True, 1.5, "1024", float("nan"), float("inf"), 2 ** 53):
            with self.subTest(value=value):
                document = deepcopy(original)
                document["samples"][1]["results"][document["benchmark"]]["peak-memory"]["value"] = value
                self.save(self.desktop, document)
                self.assert_refused_without_mutation()
        document = deepcopy(original)
        del document["samples"][1]["results"][document["benchmark"]]["peak-memory"]
        self.save(self.desktop, document)
        self.assert_refused_without_mutation()

    def test_missing_or_invalid_mobile_memory_cannot_replace_snapshot(self):
        path = self.mobile / "raw-results.json"
        original = site.load(path)
        for value in (None, 0, -1, True, 1.5, "1024", float("nan"), float("inf"), 2 ** 43):
            with self.subTest(value=value):
                raw = deepcopy(original)
                entries = next(iter(raw[0]["benchmark_results"].values()))
                entries[1]["samples"][1]["process_peak_memory_kb"] = value
                self.save(path, raw)
                self.assert_refused_without_mutation()
        raw = deepcopy(original)
        entries = next(iter(raw[0]["benchmark_results"].values()))
        del entries[1]["samples"][1]["process_peak_memory_kb"]
        self.save(path, raw)
        self.assert_refused_without_mutation()

    def test_missing_desktop_case_or_device_does_not_publish(self):
        for directory in (self.desktop.parent, self.mobile):
            with self.subTest(artifact=directory.name):
                hidden = self.root / directory.name
                directory.rename(hidden)
                self.assert_refused_without_mutation()
                hidden.rename(directory)

    def test_missing_or_duplicate_round_and_averaged_latency_are_rejected(self):
        original = site.load(self.desktop)
        variants = []
        document = deepcopy(original)
        document["samples"].pop()
        variants.append(document)
        document = deepcopy(original)
        document["samples"][1] = deepcopy(document["samples"][0])
        variants.append(document)
        document = deepcopy(original)
        document["samples"][0]["results"][document["benchmark"]]["latency"]["upper_value"] += 1
        variants.append(document)
        for document in variants:
            with self.subTest(document=document):
                self.save(self.desktop, document)
                self.assert_refused_without_mutation()

    def test_stale_mixed_and_wrong_run_desktop_results_are_rejected(self):
        original = site.load(self.desktop)
        for field, value in (("commit", "b" * 40), ("repository", "wrong/repo"), ("run_id", 999)):
            with self.subTest(field=field):
                document = deepcopy(original)
                document["snapshot"][field] = value
                self.save(self.desktop, document)
                self.assert_refused_without_mutation()
        document = deepcopy(original)
        document["samples"][0]["measured_at"] = "2025-01-01T00:00:00Z"
        self.save(self.desktop, document)
        self.assert_refused_without_mutation()
        document = deepcopy(original)
        document["plan_id"] = "0" * 64
        self.save(self.desktop, document)
        self.assert_refused_without_mutation()

    def test_mobile_source_device_threads_and_verification_must_agree(self):
        path = self.mobile / "metadata.json"
        original = site.load(path)
        variants = [{field: value} for field, value in (
            ("source_sha", "b" * 40), ("source_repository", "wrong/repo"), ("workflow_run_id", "124"),
            ("platform", "android"), ("candidate_device", "wrong device"), ("threads", 1),
            ("device_validated", False), ("status", "incomplete"), ("measured_at", "2025-01-01T00:00:00Z"))]
        for mutation in variants:
            with self.subTest(mutation=mutation):
                self.save(path, dict(original, **mutation))
                self.assert_refused_without_mutation()
        self.save(path, original)
        raw_path = self.mobile / "raw-results.json"
        original_raw = site.load(raw_path)
        for key in ("verified_proofs", "verified_leaves", "aggregation_leaves", "leaf_log_inv_rate", "threads"):
            with self.subTest(metric=key):
                raw = deepcopy(original_raw)
                result = next(iter(raw[0]["benchmark_results"].values()))[1]
                result["custom_metrics"]["run_u64"][key] += 1
                self.save(raw_path, raw)
                self.assert_refused_without_mutation()

    def test_mobile_missing_function_sample_and_duplicate_function_are_rejected(self):
        path = self.mobile / "raw-results.json"
        original = site.load(path)
        for mutation in ("function", "sample", "duplicate"):
            with self.subTest(mutation=mutation):
                raw = deepcopy(original)
                entries = next(iter(raw[0]["benchmark_results"].values()))
                if mutation == "function":
                    entries.pop()
                elif mutation == "sample":
                    entries[0]["samples_ns"].pop()
                else:
                    entries.append(deepcopy(entries[0]))
                self.save(path, raw)
                self.assert_refused_without_mutation()

    def test_duplicate_or_unexpected_artifact_and_json_key_are_rejected(self):
        duplicate = self.artifacts / "snapshot-result-desktop-x86-64-leanxmss-100-4thread-copy"
        duplicate.mkdir()
        self.save(duplicate / "result.json", site.load(self.desktop))
        self.assert_refused_without_mutation()
        (duplicate / "result.json").unlink()
        duplicate.rmdir()
        self.desktop.write_text('{"schema_version":2,"schema_version":2}')
        self.assert_refused_without_mutation()

    def test_aggregation_requires_both_levels(self):
        path = self.artifacts / "snapshot-result-desktop-arm64-aggregate-leanxmss-100-2to1" / "result.json"
        document = site.load(path)
        document["samples"][0]["results"].pop("aggregate-leanxmss-100-2to1-node")
        self.save(path, document)
        self.assert_refused_without_mutation()

    def test_os_visible_ram_variation_preserves_platform_and_exact_observations(self):
        original = site.load(self.desktop)
        varied = deepcopy(original)
        varied["machine"]["memory_bytes"] -= 24 * 1024
        varied["machine"]["id"] = site.machine_id(varied["machine"])
        self.save(self.desktop, varied)
        snapshot = self.publish()
        rows = [row for row in snapshot["results"] if row["machine"]["arch"] == "x86-64"]
        self.assertEqual(len({row["machine"]["id"] for row in rows}), 1)
        self.assertEqual({row["machine"]["memory_bytes"] for row in rows},
                         {original["machine"]["memory_bytes"], varied["machine"]["memory_bytes"]})
        self.assertEqual(len(snapshot["results"]), 56)

    def test_changed_platform_or_default_allocation_cannot_replace_snapshot(self):
        path = self.artifacts / "snapshot-result-desktop-x86-64-hash-50000" / "result.json"
        original = site.load(path)
        for field, value in (("cpu", "Other CPU"), ("os", "Linux other"),
                             ("logical_cpus", 32), ("arch", "arm64")):
            with self.subTest(field=field):
                document = deepcopy(original)
                document["machine"][field] = value
                document["machine"]["id"] = site.machine_id(document["machine"])
                self.save(path, document)
                self.assert_refused_without_mutation()
        document = deepcopy(original)
        document["threads"] = 8
        for sample in document["samples"]:
            sample["threads"] = 8
        self.save(path, document)
        self.assert_refused_without_mutation()

    def test_inconsistent_machine_or_thread_metadata_is_rejected(self):
        original = site.load(self.desktop)
        for mutation in ("named", "sample", "machine", "verification"):
            with self.subTest(mutation=mutation):
                document = deepcopy(original)
                if mutation == "named":
                    document["threads"] = 8
                elif mutation == "sample":
                    document["samples"][0]["threads"] = 8
                elif mutation == "machine":
                    document["machine"]["cpu"] = "Other machine"
                    document["machine"]["id"] = site.machine_id(document["machine"])
                else:
                    document["samples"][0]["exit_code"] = 1
                self.save(self.desktop, document)
                self.assert_refused_without_mutation()

    def test_failed_atomic_replace_preserves_previous_snapshot(self):
        self.output.write_bytes(b"previous")
        with patch.object(site.os, "replace", side_effect=OSError("disk error")):
            with self.assertRaises(OSError):
                self.publish()
        self.assertEqual(self.output.read_bytes(), b"previous")
        self.assertEqual(list(self.root.glob(".latest.json.*")), [])

    def test_plan_cannot_be_overwritten_or_narrowed(self):
        path = self.root / "plan.json"
        site.atomic_write(path, self.plan, immutable=True)
        previous = path.read_bytes()
        with self.assertRaises(FileExistsError):
            site.atomic_write(path, dict(self.plan, rounds=1), immutable=True)
        self.assertEqual(path.read_bytes(), previous)
        for section, key in (("desktop", "benchmarks"), ("desktop", "testbeds"), ("mobile", "functions"), ("mobile", "platforms")):
            plan = deepcopy(self.plan)
            plan[section][key].pop()
            with self.assertRaises(ValueError):
                site.validate_plan(plan)

    def test_public_schema_rejects_bad_statistics_duplicates_and_row_sources(self):
        original = self.publish()
        for mutation in ("median", "range", "sample", "duplicate", "source", "revision", "verified"):
            with self.subTest(mutation=mutation):
                snapshot = deepcopy(original)
                row = snapshot["results"][0]
                if mutation == "median":
                    row["median_seconds"] = 999
                elif mutation == "range":
                    row["min_seconds"] = 0
                elif mutation == "sample":
                    row["samples_seconds"][0] = float("nan")
                elif mutation == "duplicate":
                    snapshot["results"].append(deepcopy(row))
                elif mutation == "source":
                    row["source"] = snapshot["snapshot"]
                elif mutation == "revision":
                    row["program"]["source_url"] = row["program"]["source_url"].replace("a" * 40, "b" * 40)
                else:
                    row["verification"]["verified_proofs"] = 1
                with self.assertRaises(ValueError):
                    site.validate(snapshot)

    def test_public_memory_requires_safe_integer_bytes_and_nonempty_method(self):
        original = self.publish()
        for field, values in (
            ("peak_memory_bytes", (None, 0, -1, True, 1.5, "1024", float("nan"), float("inf"), 2 ** 53)),
            ("peak_memory_method", (None, "", " \t\n", 123, "x" * 501)),
        ):
            for value in values:
                with self.subTest(field=field, value=value):
                    snapshot = deepcopy(original)
                    snapshot["results"][0][field] = value
                    with self.assertRaises(ValueError):
                        site.validate(snapshot)
            snapshot = deepcopy(original)
            del snapshot["results"][0][field]
            with self.assertRaises(ValueError):
                site.validate(snapshot)
        original["results"][0]["peak_memory_bytes"] = 2 ** 53 - 1
        self.assertEqual(site.validate(original), original)

    def test_only_honest_unpublished_bootstrap_is_allowed(self):
        empty = {"schema_version": 3, "generated_at": None, "snapshot": None, "results": []}
        self.assertEqual(site.validate(empty), empty)
        for mutation in ({"generated_at": CREATED}, {"snapshot": self.plan["snapshot"]}, {"schema_version": 2}):
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                site.validate(dict(empty, **mutation))


if __name__ == "__main__":
    unittest.main()
