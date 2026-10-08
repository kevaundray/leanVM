"""Behavioral checks for sample completeness, units, provenance and retention."""

import copy
import io
import unittest
import zipfile

import benchmark_site as site


class CollectionTests(unittest.TestCase):
    def setUp(self):
        self.config = {"repository": "leanEthereum/leanVM", "branch": "riscv-exploration", "rounds": 3}
        self.run = {"id": 123, "event": "pull_request", "created_at": "2026-01-02T00:00:00Z",
                    "html_url": "https://github.com/leanEthereum/leanVM/actions/runs/123",
                    "pull_requests": [{"number": 42, "base": {"ref": "riscv-exploration"}}]}
        self.document = {"pr": 42, "base": "a" * 40, "testbed": "x86-64", "cpu": "Test CPU", "runs": []}
        for number, value in enumerate((1e9, 9e9, 2e9), 1):
            self.document["runs"].append({"round": number, "side": "base", "results": {
                "leanxmss-100-4thread": {"latency": {"value": value, "lower_value": value, "upper_value": value}}}})
        self.hardware = {"cpu": "Test CPU", "logical_cpus": 32, "os": "Linux"}

    def desktop(self, document=None):
        return site.desktop_rows(document or self.document, "leanxmss-100-4thread", self.run, self.config, self.hardware)

    def test_individual_rounds_produce_seconds_and_explicit_threads(self):
        result = self.desktop()[0]
        self.assertEqual(result["samples_seconds"], [1, 9, 2])
        self.assertEqual(result["median_seconds"], 2)
        self.assertEqual(result["threads"]["count"], 4)
        self.assertEqual(result["source"]["commit"], "a" * 40)
        self.assertIsNone(site.workload("leanxmss-100")[4])
        self.assertIsNone(site.workload("pcs-throughput"))
        self.assertIsNone(site.workload("flock-hash-batch-262144"))
        self.assertIsNone(site.workload("kernels"))

    def test_partial_duplicate_and_averaged_rounds_are_not_published(self):
        partial = copy.deepcopy(self.document)
        partial["runs"].pop()
        duplicate = copy.deepcopy(self.document)
        duplicate["runs"][1]["round"] = 1
        averaged = copy.deepcopy(self.document)
        averaged["runs"][0]["results"]["leanxmss-100-4thread"]["latency"]["lower_value"] = 0.5e9
        nonfinite = copy.deepcopy(self.document)
        nonfinite["runs"][0]["results"]["leanxmss-100-4thread"]["latency"] = dict.fromkeys(("value", "lower_value", "upper_value"), float("inf"))
        for document in (partial, duplicate, averaged, nonfinite):
            with self.subTest(document=document), self.assertRaises(ValueError):
                self.desktop(document)

    def test_latest_is_per_configuration_and_unavailable_sources_preserve_data(self):
        result = self.desktop()[0]
        previous = site.validate({"schema_version": 1, "generated_at": "2026-01-03T00:00:00Z", "results": [result]})
        self.assertEqual(site.merge(previous, []), previous)
        older = copy.deepcopy(result)
        older["source"]["measured_at"] = "2026-01-01T00:00:00Z"
        self.assertEqual(site.merge(previous, [older]), previous)
        newer = copy.deepcopy(result)
        newer["source"]["measured_at"] = "2026-01-04T00:00:00Z"
        newer["source"]["commit"] = "b" * 40
        merged = site.merge(previous, [newer])
        self.assertEqual(merged["results"][0]["source"]["commit"], "b" * 40)
        self.assertEqual(len(merged["results"]), 1)

    def test_aggregation_levels_and_inputs_remain_distinct(self):
        first = site.workload("aggregate-leanxmss-100-2to1-4thread-first")
        higher = site.workload("aggregate-leanxmss-100-2to1-4thread-node")
        wider = site.workload("aggregate-leanxmss-100-4to1-4thread-first")
        self.assertEqual(first[3:], ("aggregation", 4))
        self.assertEqual(len({first[1], higher[1], wider[1]}), 3)

    def test_mobile_requires_verified_complete_samples_and_selected_revision(self):
        selected = {"repository": "owner/repo", "branch": "mobile", "commit": "a" * 40, "label": "Mobile PR"}
        run = dict(self.run, head_sha="a" * 40)
        metadata = {"status": "complete", "device_validated": True, "source_sha": "a" * 40,
                    "source_repository": "owner/repo", "workflow_run_id": "123", "trigger_ref": "refs/heads/mobile",
                    "spends_per_leaf": 2, "functions": ["leanvm_mobile_bench::shielded_prove"],
                    "requested_device": "Phone", "threads": 6, "iterations": 3, "warmup": 1,
                    "verified_proofs": 4, "requested_os": "android", "requested_os_version": "13"}
        raw = [{"benchmark_results": {"Phone": [{"function": "leanvm_mobile_bench::shielded_prove",
               "custom_metrics": {"run_u64": {"spends_per_leaf": 2, "leaf_log_inv_rate": 2, "threads": 6, "verified_proofs": 4}},
               "samples_ns": [1e9, 3e9, 2e9], "spec": {"warmup": 1, "iterations": 3},
               "resources": {"timestamp_ms": 1767312000000}}]}}]
        result = site.mobile_rows(metadata, raw, run, selected)[0]
        self.assertEqual(result["median_seconds"], 2)
        self.assertEqual(result["verification"], {"verified_proofs": 4, "total_proofs": 4})
        self.assertIsNone(result["machine"]["logical_cpus"])
        self.assertNotEqual(result["workload"], site.workload("shielded-258")[1])
        for field, value in (("verified_proofs", 3), ("source_sha", "b" * 40), ("iterations", 4)):
            with self.subTest(field=field), self.assertRaises(ValueError):
                site.mobile_rows(dict(metadata, **{field: value}), raw, run, selected)

    def test_archive_paths_are_never_extracted_or_accepted_as_root_json(self):
        buffer = io.BytesIO()
        with zipfile.ZipFile(buffer, "w") as archive:
            archive.writestr("../ab.json", "{}")
        with self.assertRaises(ValueError):
            site.archive_json(buffer.getvalue(), "ab.json")


if __name__ == "__main__":
    unittest.main()
