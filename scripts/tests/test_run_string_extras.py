# Copyright (c) 2026 Microsoft Corporation
# SPDX-License-Identifier: MIT

import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import subprocess


SPEC = importlib.util.spec_from_file_location(
    "run_string_extras", Path(__file__).resolve().parents[1] / "run_string_extras.py")
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)


class TestStringExtras(unittest.TestCase):
    def test_errors_are_not_hidden_by_a_sat_answer_or_baseline(self):
        for stdout, stderr, code in [
                ('sat\n(error "parse error")\n', "", 0),
                ("sat\n", '(error "parse error")', 0),
                ("sat\n", "", 1)]:
            with self.subTest(stdout=stdout, stderr=stderr, code=code):
                self.assertEqual(runner.classify(stdout, stderr, code, "error-1"), ("error", True))
        self.assertEqual(runner.classify("sat\n", "", 0, "error-1"), ("sat", False))

    def test_answer_regressions_and_inconclusive_results_fail(self):
        for answer in ("unsat", "unknown", ""):
            with self.subTest(answer=answer):
                self.assertTrue(runner.classify(answer + "\n", "", 0, "sat")[1])
        self.assertEqual(runner.classify("sat\n(:time 0.1)\n", "", 0, "sat"), ("sat", False))

    def test_solver_timeout_does_not_fail_even_with_a_solved_baseline(self):
        for baseline in ("sat", "unsat", "error-1"):
            with self.subTest(baseline=baseline):
                self.assertEqual(runner.classify("timeout\n", "", 0, baseline), ("timeout", False))
        self.assertEqual(runner.classify('timeout\n(error "parse error")\n', "", 0, "sat"),
                         ("error", True))

    def test_model_validation_failures_override_answers_and_timeouts(self):
        for diagnostic in ('(error "an invalid model was generated")',
                           '(error "invalid model")', 'model validation failed'):
            for stdout, stderr in [("sat\n" + diagnostic, ""), ("timeout\n", diagnostic)]:
                with self.subTest(stdout=stdout, stderr=stderr):
                    self.assertEqual(runner.classify(stdout, stderr, 0, "error-1"),
                                     ("model-validation-failure", True))

    def test_corpus_rejects_modified_and_unlisted_inputs(self):
        with tempfile.TemporaryDirectory() as directory:
            corpus = Path(directory)
            data = b"(check-sat)\n"
            (corpus / "a.smt2").write_bytes(data)
            manifest = {"benchmarks": [{"file": "a.smt2", "sha256": hashlib.sha256(data).hexdigest()}]}
            (corpus / "manifest.json").write_text(json.dumps(manifest))
            self.assertEqual(runner.load_corpus(corpus), manifest)
            (corpus / "a.smt2").write_bytes(b"modified")
            with self.assertRaisesRegex(ValueError, "checksum"):
                runner.load_corpus(corpus)
            (corpus / "b.smt2").write_bytes(data)
            with self.assertRaisesRegex(ValueError, "exactly once"):
                runner.load_corpus(corpus)

    def test_empty_corpus_cannot_pass(self):
        with tempfile.TemporaryDirectory() as directory:
            corpus = Path(directory)
            (corpus / "manifest.json").write_text('{"benchmarks": []}')
            with self.assertRaisesRegex(ValueError, "exactly once"):
                runner.load_corpus(corpus)

    def test_external_timeout_preserves_partial_output(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            error = subprocess.TimeoutExpired("z3", 15, output=b"partial", stderr=b"diagnostic")
            entry = {"file": "failures/a.smt2", "baseline": "error-1"}
            with patch.object(runner.subprocess, "run", side_effect=error):
                result = runner.run_case(Path("z3"), output, entry, [], output)
            self.assertFalse(result["failed"])
            self.assertEqual(result["status"], "timeout")
            self.assertIn("partial", (output / "failures/a.log").read_text())

    def test_external_timeout_does_not_hide_model_validation_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            error = subprocess.TimeoutExpired(
                "z3", 15, output=b'sat\n(error "an invalid model was generated")')
            entry = {"file": "a.smt2", "baseline": "sat"}
            with patch.object(runner.subprocess, "run", side_effect=error):
                result = runner.run_case(Path("z3"), output, entry, [], output)
            self.assertTrue(result["failed"])
            self.assertEqual(result["status"], "model-validation-failure")

    def test_run_reports_model_validation_failures_but_not_timeouts_as_failures(self):
        corpus = Path(__file__).resolve().parents[2] / "benchmarks" / "string-extras"
        manifest = runner.load_corpus(corpus)
        manifest["benchmarks"] = manifest["benchmarks"][:2]
        for invalid_model in (False, True):
            with self.subTest(invalid_model=invalid_model), tempfile.TemporaryDirectory() as directory:
                output = Path(directory)
                step_summary = output / "step-summary.md"
                answers = [subprocess.CompletedProcess([], 0, "timeout\n", ""),
                           subprocess.CompletedProcess([], 0,
                               '(error "an invalid model was generated")\n' if invalid_model else "sat\n", "")]
                with patch("sys.argv", ["run_string_extras.py", "--binary", "z3",
                                        "--output", directory, "--jobs", "1"]), \
                        patch.object(runner, "load_corpus", return_value=manifest), \
                        patch.object(runner.subprocess, "check_output", return_value="Z3 test"), \
                        patch.object(runner.subprocess, "run", side_effect=answers) as run, \
                        patch.dict(runner.os.environ, {"GITHUB_STEP_SUMMARY": str(step_summary)}):
                    self.assertEqual(runner.main(), invalid_model)
                for call in run.call_args_list:
                    self.assertIn("model_validate=true", call.args[0])
                report = json.loads((output / "results.json").read_text())
                self.assertFalse(report["results"][0]["failed"])
                self.assertEqual(report["results"][1]["failed"], invalid_model)
                summary = (output / "summary.md").read_text()
                self.assertEqual(summary, step_summary.read_text())
                self.assertIn(f"**{int(invalid_model)} failures**", summary)
                self.assertIn(f"**{int(invalid_model)} model validation failures**", summary)
                self.assertIn("1 timeouts (not failures)", summary)
                if invalid_model:
                    self.assertIn("## Model validation failures", summary)
                    self.assertIn(manifest["benchmarks"][1]["source"], summary)


if __name__ == "__main__":
    unittest.main()
