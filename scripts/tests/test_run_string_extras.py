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
                ('sat\n(error "invalid model")\n', "", 0),
                ("sat\n", '(error "invalid model")', 0),
                ("sat\n", "", 1)]:
            with self.subTest(stdout=stdout, stderr=stderr, code=code):
                self.assertEqual(runner.classify(stdout, stderr, code, "error-1"), ("error", True))
        self.assertEqual(runner.classify("sat\n", "", 0, "error-1"), ("sat", False))

    def test_answer_regressions_and_inconclusive_results_fail(self):
        for answer in ("unsat", "unknown", "timeout", ""):
            with self.subTest(answer=answer):
                self.assertTrue(runner.classify(answer + "\n", "", 0, "sat")[1])
        self.assertEqual(runner.classify("sat\n(:time 0.1)\n", "", 0, "sat"), ("sat", False))

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
            self.assertTrue(result["failed"])
            self.assertEqual(result["status"], "timeout")
            self.assertIn("partial", (output / "failures/a.log").read_text())


if __name__ == "__main__":
    unittest.main()
