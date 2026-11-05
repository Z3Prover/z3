"""Tests for reproducible, oracle-selected QF_FF certificate inputs."""

from collections import Counter
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import prepare_checker_qfff as qfff
import run_checker_regressions as runner


SOURCE = """
def generate(rng, p):
    value = rng.randrange(p)
    salt = rng.randrange(1000000)
    atom = f'(= x (as ff{value} F))'
    if rng.randrange(3) == 0:
        return atom + f' ; {salt}\\n', lambda x, y: x == value
    return f'(and {atom} (not {atom})) ; {salt}\\n', lambda x, y: False

def problem(p, formula):
    return (f'(set-logic QF_FF)\\n(define-sort F () (_ FiniteField {p}))\\n'
            f'(declare-const x F)\\n(declare-const y F)\\n'
            f'(assert {formula})\\n(check-sat)\\n')
"""


class CheckerQfffTests(unittest.TestCase):
    def source(self, root, content=SOURCE):
        z3test = root / "z3test"
        source = z3test / qfff.GENERATOR
        source.parent.mkdir(parents=True)
        source.write_text(content, encoding="utf-8")
        return z3test

    def prepare(self, z3test, output, seed="run-123"):
        with patch.object(qfff.subprocess, "check_output", return_value="a" * 40 + "\n"), \
                contextlib.redirect_stdout(io.StringIO()):
            qfff.prepare(z3test, output, seed)
        return json.loads((output / "manifest.json").read_text())

    def test_exact_cohort_filters_sat_and_records_verifiable_provenance(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            z3test = self.source(root)
            output = root / "inputs"
            document = self.prepare(z3test, output)
            paths, count = runner.discover(output, ".", 0)
            self.assertEqual(count, 25)
            self.assertEqual(Counter(row["prime"] for row in document["cases"]),
                             {prime: 5 for prime in qfff.PRIMES})
            for path in paths:
                text = path.read_text()
                self.assertIn("(set-info :status unsat)", text)
                self.assertIn("(assert (and ", text)
            metadata = runner.verify_manifest(output, ".", output / "manifest.json", paths)
            self.assertEqual(set(metadata["logics"].values()), {"QF_FF"})
            source = document["generators"][0]
            self.assertEqual(source["sha256"], runner.file_sha256(z3test / qfff.GENERATOR))
            self.assertEqual(source["commit"], "a" * 40)
            paths[0].write_text("(assert false)\n")
            with self.assertRaisesRegex(ValueError, "Input SHA-256 mismatch"):
                runner.verify_manifest(output, ".", output / "manifest.json", paths)

    def test_seed_reproduces_inputs_and_rotates_a_new_run(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            z3test = self.source(root)
            first = self.prepare(z3test, root / "first")
            self.assertEqual(first, self.prepare(z3test, root / "same"))
            self.assertNotEqual(first["cases"],
                                self.prepare(z3test, root / "other", "run-456")["cases"])

    def test_insufficient_unsat_or_distinct_inputs_fail_without_a_manifest(self):
        for predicate, expected in (
                ("x == p - 1 and y == p - 1", "only 0"), ("False", "only 1")):
            with self.subTest(predicate=predicate), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                z3test = self.source(root,
                    f"def generate(rng, p): return '(assert false)', lambda x, y: {predicate}\n"
                    "def problem(p, formula): return formula\n")
                output = root / "inputs"
                with patch.object(qfff, "MAX_ATTEMPTS", 8), \
                        self.assertRaisesRegex(ValueError, expected):
                    self.prepare(z3test, output)
                self.assertFalse((output / "manifest.json").exists())


if __name__ == "__main__":
    unittest.main()
