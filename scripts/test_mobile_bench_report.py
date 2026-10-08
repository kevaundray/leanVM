"""Mobile reporting must not publish invalid, incomplete or stale proof measurements."""

import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch


SPEC = importlib.util.spec_from_file_location("mobile_report", Path(__file__).with_name("mobile-bench-report.py"))
report = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(report)
HEAD = "a" * 40
REPO = "example/leanVM"


class MobileReportTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.directory = Path(self.temp.name)
        self.metadata = {
            "source_repository": REPO,
            "source_sha": HEAD,
            "workflow_run_id": "123",
            "status": "complete",
            "platform": "android",
            "device_validated": True,
            "candidate_device": "Google Pixel 7-13.0",
            "functions": [report.FUNCTION],
            "spends_per_leaf": 2,
            "warmup": 1,
            "iterations": 3,
            "verified_proofs": 4,
            "threads": 6,
            "available_parallelism": 6,
        }
        self.result = {
            "function": report.FUNCTION,
            "spec": {"name": report.FUNCTION, "warmup": 1, "iterations": 3},
            "custom_metrics": {"run_u64": {"threads": 6, "available_parallelism": 6, "spends_per_leaf": 2, "verified_proofs": 4}},
            "samples_ns": [1_000_000_000, 9_000_000_000, 2_000_000_000],
            "samples": [{"duration_ns": value} for value in (1_000_000_000, 9_000_000_000, 2_000_000_000)],
            # Never trust a separately supplied aggregate instead of the samples.
            "median_ns": 999,
        }

    def render(self, head=HEAD, device="Google Pixel 7"):
        (self.directory / "metadata.json").write_text(json.dumps(self.metadata))
        raw = [{"benchmark_results": {device: [self.result]}}]
        (self.directory / "raw-results.json").write_text(json.dumps(raw))
        return report.render(self.directory, REPO, head, "123")

    def test_median_and_range_come_from_samples(self):
        body, complete, _ = self.render()
        self.assertTrue(complete)
        self.assertIn("| 6 | 2.000 s | 1.000 to 9.000 s | 4 / 4 |", body)
        self.assertIn("not a paired base-versus-PR comparison", body)

    def test_incomplete_run_publishes_no_latency(self):
        self.metadata["status"] = "incomplete_results"
        body, complete, _ = self.render()
        self.assertFalse(complete)
        self.assertNotIn("2.000 s", body)
        self.assertIn("No performance result", body)

    def test_iphone_cannot_be_labelled_as_android(self):
        self.metadata["platform"] = "ios"
        self.metadata["candidate_device"] = "iPhone 14-16"
        with self.assertRaisesRegex(ValueError, "unexpected measured device"):
            self.render()

    def test_iphone_provider_name_variants_preserve_device_identity(self):
        self.metadata["platform"] = "ios"
        self.metadata["candidate_device"] = "iPhone 14-16"
        for device in ("iPhone 14", "iPhone 14-16"):
            with self.subTest(device=device):
                body, complete, platform = self.render(device=device)
                self.assertTrue(complete)
                self.assertEqual(platform, "ios")
                self.assertIn("| iPhone 14 / iOS 16 | 6 | 2.000 s |", body)
        with self.assertRaisesRegex(ValueError, "unexpected measured device"):
            self.render(device="iPhone 14-17")

    def test_wrong_source_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "source commit mismatch"):
            self.render("b" * 40)

    def test_unverified_proof_or_changed_thread_count_is_rejected(self):
        for key, value in (("verified_proofs", 3), ("threads", 8)):
            with self.subTest(key=key):
                old = self.result["custom_metrics"]["run_u64"][key]
                self.result["custom_metrics"]["run_u64"][key] = value
                with self.assertRaises(ValueError):
                    self.render()
                self.result["custom_metrics"]["run_u64"][key] = old

    def test_invalid_or_conflicting_samples_are_rejected(self):
        for samples in ([0, 1, 2], [True, 1, 2], [float("nan"), 1, 2], [1, 2], [1, 2, 3]):
            with self.subTest(samples=samples):
                self.result["samples_ns"] = samples
                with self.assertRaises(ValueError):
                    self.render()

    def test_pr_updated_during_publication_is_not_written(self):
        current = {"number": 7, "head": {"sha": HEAD, "repo": {"full_name": REPO}}}
        updated = {"head": {"sha": "b" * 40}}
        with patch.object(report, "pages", side_effect=[[current], []]), patch.object(report, "gh", side_effect=[current, updated]) as api:
            report.post(REPO, REPO, HEAD, "measured result")
        self.assertTrue(all(len(call.args) == 1 for call in api.call_args_list), "a stale result performed an API write")

    def test_failed_iphone_does_not_erase_android_results(self):
        self.render()
        ios = self.directory / "ios"
        ios.mkdir()
        metadata = self.metadata | {"platform": "ios", "candidate_device": "iPhone 14-16", "status": "benchmark_run_failed"}
        (ios / "metadata.json").write_text(json.dumps(metadata))
        argv = ["report", str(self.directory), str(ios), "--repository", REPO, "--head", HEAD, "--run-id", "123"]
        output = io.StringIO()
        with patch("sys.argv", argv), patch("sys.stdout", output), patch.dict("os.environ", {}, clear=True):
            report.main()
        self.assertIn("| Google Pixel 7 / Android 13.0 | 6 | 2.000 s |", output.getvalue())
        self.assertIn("### Mobile benchmarks: iPhone 14 / iOS 16", output.getvalue())
        self.assertIn("No performance result is published", output.getvalue())
        self.assertNotIn("| iPhone 14", output.getvalue())


if __name__ == "__main__":
    unittest.main()
