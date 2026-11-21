"""End-to-end tests for the standalone sort-indexed checker."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from run_checker_regressions import read_diagnostics


CHECKER = os.environ.get("Z3_INDEPENDENT_CHECKER")


@unittest.skipUnless(CHECKER and Path(CHECKER).is_file(),
                     "set Z3_INDEPENDENT_CHECKER to the standalone executable")
class IndependentCheckerTests(unittest.TestCase):
    def run_checker(self, source, *args):
        return subprocess.run([CHECKER, *args], input=source, text=True,
                              capture_output=True, timeout=30)

    def test_refutation_and_statistics(self):
        result = self.run_checker(
            "(declare-const x Int)(assert (> x 0))(assert (< x 0))(check-sat)",
            "--stats")
        self.assertEqual((result.returncode, result.stdout.strip()), (0, "ACCEPT"))
        self.assertIn("semantics=sorted-core", result.stderr)

    def test_sat_is_not_certified(self):
        result = self.run_checker("(assert true)(check-sat)")
        self.assertEqual((result.returncode, result.stdout.strip()), (4, "SAT"))

    def test_pending_is_not_certified(self):
        result = self.run_checker(
            "(declare-const x Int)(assert (= (* x x) 2))(check-sat)",
            "--diagnostics")
        self.assertEqual((result.returncode, result.stdout.strip()), (3, "PARTIAL 1"))
        self.assertIn("diagnostic\tchecked\tpending=1\tfamilies=1", result.stderr)
        self.assertRegex(result.stderr, r"obligation\t[^\t]+\t1\t\d+\t[^\n]+")
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / "stderr"
            log.write_text(result.stderr, encoding="utf-8")
            self.assertEqual(read_diagnostics(log)["pending"], 1)

    def test_certified_diagnostics_do_not_change_verdict(self):
        source = "(declare-const x Int)(assert (> x 0))(assert (< x 0))(check-sat)"
        result = self.run_checker(source, "--diagnostics")
        self.assertEqual((result.returncode, result.stdout.strip()), (0, "ACCEPT"))
        self.assertIn("diagnostic\tchecked\tpending=0\tfamilies=0", result.stderr)

    def test_optional_duplicate_distinct_replay(self):
        source = "(declare-const x Int)(assert (distinct x x))(check-sat)"
        baseline = self.run_checker(source, "--diagnostics")
        self.assertEqual((baseline.returncode, baseline.stdout.strip()), (3, "PARTIAL 1"))
        enhanced = self.run_checker(source, "--distinct-replay", "--diagnostics", "--stats")
        self.assertEqual((enhanced.returncode, enhanced.stdout.strip()), (0, "ACCEPT"))
        self.assertIn("diagnostic\tchecked\tpending=0\tfamilies=0", enhanced.stderr)
        self.assertIn("semantics=sorted-distinct", enhanced.stderr)

    def test_optional_distinct_replay_remains_conservative(self):
        cases = [
            ("(declare-const x Int)(assert (= (* x x) 2))(check-sat)", 3, "PARTIAL 1"),
            ("(declare-const x Int)(declare-const y Int)"
             "(assert (distinct x y))(check-sat)", 4, "SAT"),
            ("(declare-datatypes ((Box 0)) (((mk-box))))"
             "(declare-const c (Array Int Box))"
             "(declare-fun q ((Array Int Box)) Bool)"
             "(assert (q c))(assert (not (q c)))(check-sat)",
             5, "UNKNOWN unsupported-root-fragment"),
        ]
        for source, code, verdict in cases:
            with self.subTest(verdict=verdict):
                result = self.run_checker(source, "--distinct-replay", "--diagnostics")
                self.assertEqual((result.returncode, result.stdout.strip()), (code, verdict))

    def test_optional_skolem_replay_preserves_other_verdicts(self):
        cases = [
            ("(assert false)(check-sat)", 0, "ACCEPT"),
            ("(declare-const x Int)(assert (= (* x x) 2))(check-sat)", 3, "PARTIAL 1"),
            ("(assert true)(check-sat)", 4, "SAT"),
            ("(declare-datatypes ((Box 0)) (((mk-box))))"
             "(declare-const c (Array Int Box))"
             "(declare-fun q ((Array Int Box)) Bool)"
             "(assert (q c))(assert (not (q c)))(check-sat)",
             5, "UNKNOWN unsupported-root-fragment"),
        ]
        for source, code, verdict in cases:
            with self.subTest(verdict=verdict):
                result = self.run_checker(source, "--skolem-replay", "--diagnostics", "--stats")
                self.assertEqual((result.returncode, result.stdout.strip()), (code, verdict))
                if code != 4:
                    self.assertIn("semantics=sorted-skolem", result.stderr)
                    baseline = self.run_checker(source, "--diagnostics")
                    diagnostic = "\n".join(
                        line for line in result.stderr.splitlines()
                        if not line.startswith("solve_ms=")) + "\n"
                    self.assertEqual(diagnostic, baseline.stderr)

    def test_distinct_and_skolem_modes_cannot_be_combined(self):
        result = self.run_checker("", "--distinct-replay", "--skolem-replay")
        self.assertEqual(result.returncode, 2)

    def test_optional_field_replay(self):
        source = ("(set-logic QF_FF)(define-sort F () (_ FiniteField 5))"
                  "(declare-const x F)(declare-const y F)"
                  "(assert (and (= (ff.add (ff.mul x x) (as ff-2 F)) (ff.mul (ff.mul x x) y))"
                  " (= y (ff.bitsum (ite (= x y) y (as ff-6 F))"
                  " (ff.bitsum (as ff1 F) x)))))(check-sat)")
        baseline = self.run_checker(source, "--diagnostics")
        self.assertEqual(baseline.returncode, 3, baseline.stdout + baseline.stderr)
        enhanced = self.run_checker(source, "--field-replay", "--diagnostics", "--stats")
        self.assertEqual((enhanced.returncode, enhanced.stdout.strip()), (0, "ACCEPT"))
        self.assertIn("diagnostic\tchecked\tpending=0\tfamilies=0", enhanced.stderr)
        self.assertIn("semantics=sorted-field", enhanced.stderr)
        interactive = self.run_checker(source, "--interactive", "--field-replay", "--diagnostics")
        self.assertEqual(interactive.returncode, 0, interactive.stdout + interactive.stderr)
        self.assertIn("; proof-check ACCEPT", interactive.stdout)
        self.assertIn("diagnostic\tchecked\tpending=0\tfamilies=0", interactive.stderr)

    def test_field_replay_preserves_other_verdicts(self):
        for source in ("(assert false)(check-sat)",
                       "(declare-const x Int)(assert (= (* x x) 2))(check-sat)",
                       "(assert true)(check-sat)",
                       "(declare-datatypes ((Box 0)) (((mk-box))))"
                       "(declare-const c (Array Int Box))"
                       "(declare-fun q ((Array Int Box)) Bool)"
                       "(assert (q c))(assert (not (q c)))(check-sat)"):
            with self.subTest(source=source):
                baseline = self.run_checker(source, "--diagnostics")
                enhanced = self.run_checker(source, "--field-replay", "--diagnostics")
                self.assertEqual((enhanced.returncode, enhanced.stdout, enhanced.stderr),
                                 (baseline.returncode, baseline.stdout, baseline.stderr))
        for other in ("--distinct-replay", "--skolem-replay"):
            self.assertEqual(self.run_checker("", "--field-replay", other).returncode, 2)

    def test_prime_evidence_cli(self):
        source = "(assert false)(check-sat)"
        for interactive in (False, True):
            mode = ("--interactive",) if interactive else ()
            baseline = self.run_checker(source, *mode, "--field-replay", "--diagnostics")
            for evidence in ("3:" + ",".join(["2"] * 16), "1:3"):
                with self.subTest(interactive=interactive, evidence=evidence):
                    result = self.run_checker(source, *mode, "--field-replay",
                                              "--prime-evidence", evidence, "--diagnostics")
                    stable = lambda text: [line for line in text.splitlines()
                                           if not line.startswith("; proof-stats ")]
                    self.assertEqual((result.returncode, stable(result.stdout), result.stderr),
                                     (baseline.returncode, stable(baseline.stdout), baseline.stderr))
        invalid = ("", "3", "3:2,", "3:-2", "-1:2", "3:0x2",
                   "3:" + ",".join(["2"] * 257), "3:268435457",
                   str(2**256 + 1) + ":2")
        for evidence in invalid:
            with self.subTest(evidence=evidence):
                result = self.run_checker(source, "--field-replay", "--prime-evidence", evidence)
                self.assertEqual(result.returncode, 2)
        self.assertEqual(self.run_checker(source, "--prime-evidence", "3:2").returncode, 2)
        self.assertEqual(self.run_checker(source, "--field-replay", "--prime-evidence", "3:2",
                                          "--prime-evidence", "3:2").returncode, 2)

    def test_array_replay_cli(self):
        source = ("(set-logic QF_AX)(declare-const a (Array Int Int))"
                  "(declare-const i Int)(declare-const v Int)"
                  "(assert (not (= (select (store a i v) i) v)))(check-sat)")
        result = self.run_checker(source, "--array-replay", "--diagnostics", "--stats")
        self.assertEqual((result.returncode, result.stdout.strip()), (0, "ACCEPT"))
        self.assertIn("semantics=sorted-array", result.stderr)
        interactive = self.run_checker(source, "--interactive", "--array-replay", "--diagnostics")
        self.assertEqual(interactive.returncode, 0, interactive.stdout + interactive.stderr)
        self.assertIn("; proof-check ACCEPT", interactive.stdout)
        for other in ("--distinct-replay", "--skolem-replay", "--field-replay",
                      "--definition-replay"):
            self.assertEqual(self.run_checker("", "--array-replay", other).returncode, 2)

    def test_definition_array_replay_cli(self):
        source = ("(set-logic QF_AX)(declare-const a (Array Int Int))"
                  "(declare-const i Int)(declare-const v Int)"
                  "(assert (not (= (select (store a i v) i) v)))(check-sat)")
        result = self.run_checker(source, "--definition-array-replay", "--diagnostics", "--stats")
        self.assertEqual((result.returncode, result.stdout.strip()), (0, "ACCEPT"))
        self.assertIn("semantics=sorted-definition-array", result.stderr)
        interactive = self.run_checker(source, "--interactive", "--definition-array-replay",
                                       "--diagnostics")
        self.assertEqual(interactive.returncode, 0, interactive.stdout + interactive.stderr)
        self.assertIn("; proof-check ACCEPT", interactive.stdout)
        for other in ("--distinct-replay", "--skolem-replay", "--field-replay",
                      "--array-replay", "--definition-replay"):
            self.assertEqual(
                self.run_checker("", "--definition-array-replay", other).returncode, 2)

    def test_array_replay_diagnostics_preserve_noncertified_verdicts(self):
        cases = [
            ("(declare-const x Int)(assert (= (* x x) 2))(check-sat)", 3, "PARTIAL 1"),
            ("(declare-datatypes ((Box 0)) (((mk-box))))"
             "(declare-const c (Array Int Box))"
             "(declare-fun q ((Array Int Box)) Bool)"
             "(assert (q c))(assert (not (q c)))(check-sat)",
             5, "UNKNOWN unsupported-root-fragment"),
        ]
        for source, code, verdict in cases:
            with self.subTest(verdict=verdict):
                baseline = self.run_checker(source, "--diagnostics")
                result = self.run_checker(source, "--array-replay", "--diagnostics")
                self.assertEqual((result.returncode, result.stdout.strip()), (code, verdict))
                self.assertEqual(result.stderr, baseline.stderr)
                interactive = self.run_checker(source, "--interactive", "--array-replay", "--diagnostics")
                self.assertEqual(interactive.returncode, code)
                self.assertIn("; proof-check " + verdict, interactive.stdout)
                self.assertEqual(interactive.stderr, baseline.stderr)

    def test_definition_replay_preserves_other_verdicts(self):
        for source in ("(assert false)(check-sat)",
                       "(declare-const x Int)(assert (= (* x x) 2))(check-sat)",
                       "(assert true)(check-sat)",
                       "(declare-datatypes ((Box 0)) (((mk-box))))"
                       "(declare-const c (Array Int Box))"
                       "(declare-fun q ((Array Int Box)) Bool)"
                       "(assert (q c))(assert (not (q c)))(check-sat)"):
            with self.subTest(source=source):
                baseline = self.run_checker(source, "--diagnostics")
                enhanced = self.run_checker(source, "--definition-replay", "--diagnostics")
                self.assertEqual((enhanced.returncode, enhanced.stdout, enhanced.stderr),
                                 (baseline.returncode, baseline.stdout, baseline.stderr))
        for other in ("--distinct-replay", "--skolem-replay", "--field-replay"):
            self.assertEqual(self.run_checker("", "--definition-replay", other).returncode, 2)

    def test_interactive_definition_replay(self):
        source = "(push)(assert false)(check-sat)(pop)(assert true)(check-sat)"
        result = self.run_checker(source, "--interactive", "--definition-replay", "--diagnostics")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("; proof-check ACCEPT", result.stdout)
        self.assertIn("semantics=sorted-definition", result.stdout)

    def test_interactive_preserves_scopes_and_checks_each_refutation(self):
        source = ("; quoted symbols can contain delimiters\n"
                  "(declare-const |x);| Int)"
                  "(push 1)(assert (> |x);| 0))(assert (< |x);| 0))(check-sat)(pop 1)"
                  "(check-sat)"
                  "(push 1)(assert (distinct |x);| |x);|))(check-sat)(pop 1)"
                  "(reset)(assert false)(check-sat)")
        result = self.run_checker(source, "--interactive", "--distinct-replay", "--diagnostics")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout.count("; proof-check ACCEPT"), 3)
        self.assertEqual(result.stdout.count("unsat\n"), 3)
        self.assertEqual(result.stdout.count("\nsat\n"), 1)
        self.assertEqual(result.stderr.count("diagnostic\tchecked\tpending=0"), 3)

    def test_interactive_reports_pending_and_incomplete_commands(self):
        pending = self.run_checker("(declare-const x Int)(assert (distinct x x))(check-sat)",
                                   "--interactive", "--diagnostics")
        self.assertEqual(pending.returncode, 3)
        self.assertIn("; proof-check PARTIAL 1", pending.stdout)
        self.assertIn("obligation\trewrite\t1\t", pending.stderr)
        malformed = self.run_checker("(assert true", "--interactive")
        self.assertEqual(malformed.returncode, 2)

    def test_interactive_skolem_diagnostics_preserve_base_results(self):
        source = ("(push)(assert false)(check-sat)(pop)"
                  "(declare-const x Int)(assert (= (* x x) 2))(check-sat)")
        baseline = self.run_checker(source, "--interactive", "--diagnostics")
        enhanced = self.run_checker(source, "--interactive", "--skolem-replay", "--diagnostics")
        self.assertEqual(enhanced.returncode, baseline.returncode)
        self.assertEqual(enhanced.stderr, baseline.stderr)
        self.assertIn("; proof-check ACCEPT", enhanced.stdout)
        self.assertIn("; proof-check PARTIAL 1", enhanced.stdout)

    def test_interactive_reports_nnf_root_counts(self):
        source = ("(declare-fun p (Int) Bool)"
                  "(assert (not (exists ((x Int)) (p x))))(assert (p 0))(check-sat)")
        result = self.run_checker(source, "--interactive", "--diagnostics")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertRegex(result.stdout,
                         r"proof-nnf nnf-pos-roots=\d+ nnf-pos-pending=0 "
                         r"nnf-neg-roots=[1-9]\d* nnf-neg-pending=0")

    def test_uncovered_is_not_certified(self):
        source = ("(declare-datatypes ((Box 0)) (((mk-box))))"
                  "(declare-const c (Array Int Box))"
                  "(declare-fun q ((Array Int Box)) Bool)"
                  "(assert (q c))(assert (not (q c)))(check-sat)")
        result = self.run_checker(source, "--diagnostics")
        self.assertEqual((result.returncode, result.stdout.strip()),
                         (5, "UNKNOWN unsupported-root-fragment"))
        self.assertIn("diagnostic\tchecked\tpending=0\tfamilies=0", result.stderr)

    def test_invalid_input_is_not_certified(self):
        result = self.run_checker("(assert unknown-name)(check-sat)")
        self.assertNotEqual(result.returncode, 0)
        self.assertNotEqual(result.stdout.strip(), "ACCEPT")

    def test_invalid_timeout_is_rejected(self):
        result = self.run_checker("", "--timeout-ms", "4294967296")
        self.assertEqual(result.returncode, 2)


if __name__ == "__main__":
    unittest.main()
