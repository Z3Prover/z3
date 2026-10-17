"""Tests for corpus selection, verdict accounting, resource bounds, and reports."""

import argparse
import contextlib
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

import run_checker_regressions as runner


class CheckerRegressionTests(unittest.TestCase):
    def test_verdict_requires_matching_exit_code_and_stdout(self):
        for code, text, expected in (
                (0, "ACCEPT\n", "ACCEPT"), (1, "REJECT", "REJECT"),
                (3, "PARTIAL 4", "PARTIAL"), (4, "SAT", "SAT"),
                (5, "UNKNOWN timeout", "UNKNOWN"), (2, "", "ERROR"),
                (-11, "", "CRASH"), (134, "", "CRASH"),
                (0, "SAT", "PROTOCOL_ERROR"), (0, "", "PROTOCOL_ERROR"),
                (1, "ACCEPT", "PROTOCOL_ERROR"), (3, "PARTIAL 0", "PROTOCOL_ERROR"),
                (5, "UNKNOWN", "PROTOCOL_ERROR"),
                (0, "ACCEPT\nSAT", "PROTOCOL_ERROR")):
            with self.subTest(code=code, text=text):
                self.assertEqual(runner.classify(code, text), expected)

    def test_selection_is_recursive_sorted_bounded_and_not_manifest_driven(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "nested").mkdir()
            for name in ("b.smt2", "a.smt2", "nested/c.smt2", "list.txt", "saved.proof"):
                (root / name).touch()
            paths, total = runner.discover(root, ".", 2)
            self.assertEqual(total, 3)
            self.assertEqual([path.name for path in paths], ["a.smt2", "b.smt2"])
            self.assertEqual(len(runner.discover(root, ".", 0)[0]), 3)
            with self.assertRaises(ValueError):
                runner.discover(root, "..", 0)
            with self.assertRaises(ValueError):
                runner.discover(root, "missing", 0)
            (root / "empty").mkdir()
            with self.assertRaises(ValueError):
                runner.discover(root, "empty", 0)

    def test_process_execution_preserves_logs_and_statistics(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            (output / "logs").mkdir()
            row = runner.run_case(
                [sys.executable, "-c",
                 "import sys; print('ACCEPT'); "
                 "print('solve_ms=1.250 marshal_ms=2.500 check_ms=0.500 "
                 "expressions=7 declarations=3 proof_nodes=9', file=sys.stderr)"],
                "test.smt2", output, 0, 10, 0)
            self.assertEqual(row["outcome"], "ACCEPT")
            self.assertGreater(row["wall_seconds"], 0)
            self.assertEqual(row["statistics"]["marshal_ms"], 2.5)
            self.assertEqual(row["statistics"]["proof_nodes"], 9)
            self.assertEqual((output / row["stdout"]).read_text().strip(), "ACCEPT")

    def test_whole_process_timeout_kills_the_checker(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            (output / "logs").mkdir()
            row = runner.run_case(
                [sys.executable, "-c", "import time; time.sleep(30)"],
                "slow.smt2", output, 0, 0.1, 0)
            self.assertEqual(row["outcome"], "TIMEOUT")
            self.assertIsNone(row["returncode"])
            self.assertLess(row["wall_seconds"], 10)

    @unittest.skipUnless(sys.platform == "linux", "Linux address-space limit")
    def test_linux_memory_limit_is_applied_to_the_checker_process(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            (output / "logs").mkdir()
            row = runner.run_case(
                [sys.executable, "-c",
                 "import resource; assert resource.getrlimit(resource.RLIMIT_AS) == (512*1024**2,)*2; "
                 "print('ACCEPT')"],
                "bounded.smt2", output, 0, 10, 512)
            self.assertEqual(row["outcome"], "ACCEPT")

    def test_report_never_counts_partial_sat_or_unknown_as_success(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            outcomes = ("ACCEPT", "PARTIAL", "REJECT", "SAT", "UNKNOWN", "TIMEOUT", "ERROR")
            rows = [{"path": f"{index}.smt2", "outcome": outcome, "wall_seconds": index + 1}
                    for index, outcome in enumerate(outcomes)]
            selection = {"paths": [row["path"] for row in rows] + ["interrupted.smt2"]}
            (output / "selection.json").write_text(json.dumps(selection))
            (output / "results.jsonl").write_text(
                "\n".join(json.dumps(row) for row in rows) + "\n")
            runner.report(output)
            summary = json.loads((output / "summary.json").read_text())
            self.assertEqual(summary["tested"], 7)
            self.assertEqual(summary["selected"], 8)
            self.assertEqual(summary["success_rate"], 1 / 7)
            self.assertEqual(summary["uncertified_rate"], 6 / 7)
            self.assertEqual(summary["counts"]["NOT_RUN"], 1)
            self.assertEqual(summary["median_seconds"], 4)
            self.assertEqual(summary["p95_seconds"], 7)
            self.assertIn("Pulse is not linked", (output / "report.md").read_text())
            self.assertIn("interrupted.smt2", (output / "results.csv").read_text())

    def test_report_survives_a_build_failure_with_no_results(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            (output / "build.json").write_text('{"exit_code":1,"wall_seconds":5}')
            with patch.dict("os.environ", {"BUILD_OUTCOME": "failure"}):
                runner.report(output)
            summary = json.loads((output / "summary.json").read_text())
            self.assertEqual(summary["build"]["exit_code"], 1)
            self.assertIsNone(summary["success_rate"])
            self.assertEqual(summary["tested"], 0)
            text = (output / "report.md").read_text()
            self.assertIn("**failure**", text)
            self.assertIn("no test success is claimed", text)

    def test_budget_exhaustion_records_all_unattempted_inputs(self):
        with tempfile.TemporaryDirectory() as directory:
            corpus = Path(directory) / "corpus"
            corpus.mkdir()
            for name in ("a.smt2", "b.smt2"):
                (corpus / name).touch()
            output = Path(directory) / "report"
            args = argparse.Namespace(
                corpus=corpus, corpus_path=".", max_cases=0, checker=Path("checker"),
                output=output, corpus_commit="test", memory_limit_mb=0,
                total_timeout_seconds=1, case_timeout_seconds=1, solver_timeout_ms=1)
            version = argparse.Namespace(stdout="test-version")
            with patch.object(runner.subprocess, "run", return_value=version), \
                    patch.object(runner.time, "perf_counter", side_effect=[0, 2, 3]), \
                    contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(runner.run_suite(args), 1)
            runner.report(output)
            summary = json.loads((output / "summary.json").read_text())
            self.assertEqual(summary["counts"]["NOT_RUN"], 2)
            self.assertEqual(summary["tested"], 0)

    def test_interrupted_final_record_is_reported_not_silently_lost(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            (output / "selection.json").write_text('{"paths":["a.smt2","b.smt2"]}')
            (output / "results.jsonl").write_text(
                '{"path":"a.smt2","outcome":"ACCEPT","wall_seconds":1}\n{"path":')
            runner.report(output)
            summary = json.loads((output / "summary.json").read_text())
            self.assertEqual(summary["counts"]["ACCEPT"], 1)
            self.assertEqual(summary["counts"]["NOT_RUN"], 1)
            self.assertEqual(len(summary["warnings"]), 1)
            self.assertIn("**Warning:**", (output / "report.md").read_text())
            (output / "results.jsonl").write_text("bad record\n")
            with self.assertRaises(json.JSONDecodeError):
                runner.report(output)

    def test_process_errors_fail_the_run_but_coverage_gaps_do_not(self):
        with tempfile.TemporaryDirectory() as directory:
            corpus = Path(directory) / "corpus"
            corpus.mkdir()
            (corpus / "input.smt2").touch()
            args = argparse.Namespace(
                corpus=corpus, corpus_path=".", max_cases=0, checker=Path("checker"),
                output=Path(directory) / "report", corpus_commit="test", memory_limit_mb=0,
                total_timeout_seconds=10, case_timeout_seconds=1, solver_timeout_ms=1)
            for outcome in runner.OUTCOMES[:-1]:
                with self.subTest(outcome=outcome), \
                        patch.object(runner.subprocess, "run",
                                     return_value=argparse.Namespace(stdout="test-version")), \
                        patch.object(runner, "run_case",
                                     return_value={"path": "input.smt2", "outcome": outcome}), \
                        contextlib.redirect_stdout(io.StringIO()):
                    self.assertEqual(runner.run_suite(args), int(outcome in runner.ERRORS))

    def test_resource_arguments_reject_invalid_or_unbounded_values(self):
        for value in ("0", "-1", "inf", "nan"):
            with self.subTest(value=value), self.assertRaises(argparse.ArgumentTypeError):
                runner.positive_float(value)
        for value in ("0", "-1", "4294967296"):
            with self.subTest(value=value), self.assertRaises(argparse.ArgumentTypeError):
                runner.solver_timeout(value)
        with self.assertRaises(argparse.ArgumentTypeError):
            runner.nonnegative_int("-1")


if __name__ == "__main__":
    unittest.main()
