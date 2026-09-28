"""Tests for the proof regression matrix runner.

Classification tests use synthetic solver runs and need no z3. The end-to-end
test runs the real runner when Z3_EXE points at a z3 executable (or z3 is on
PATH) and is skipped otherwise.
"""
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import proof_matrix  # noqa: E402

_Z3 = os.environ.get("Z3_EXE") or shutil.which("z3")


def fake_run(stdout="", stderr="", code=0, timeout=False):
    return {"stdout": stdout, "stderr": stderr, "code": code, "time": 0.0, "timeout": timeout}


class TestClassification(unittest.TestCase):
    def classify(self, run, expected="unsat", checks=lambda record: "verified"):
        record = proof_matrix.base_record("b.smt2", "QF_LIA", "cell", expected)
        return proof_matrix.finish(record, run, checks)

    def test_unsat_with_passing_checks_is_verified(self):
        self.assertEqual(self.classify(fake_run("unsat\n"))["status"], "verified")

    def test_checks_decide_the_status_of_unsat_runs(self):
        for status in ("unverified-fallback", "checker-rejected", "no-checker", "no-proof"):
            self.assertEqual(self.classify(fake_run("unsat\n"), checks=lambda r, s=status: s)["status"], status)

    def test_sat_and_unknown_results_are_not_applicable_even_with_proof_errors(self):
        for stdout in ('sat\n(error "line 4: proof is not available")\n', "unknown\n"):
            record = self.classify(fake_run(stdout), expected=stdout.split("\n")[0])
            self.assertEqual(record["status"], "not-applicable")

    def test_disagreement_with_the_reference_result_is_reported(self):
        self.assertEqual(self.classify(fake_run("sat\n"), expected="unsat")["status"], "disagree")
        self.assertEqual(self.classify(fake_run("unsat\n"), expected="sat")["status"], "disagree")

    def test_missing_proof_after_unsat_is_no_proof_not_crash(self):
        record = self.classify(fake_run('unsat\n(error "line 4: proof construction is not enabled, use command '
                                        '(set-option :produce-proofs true)")\n'))
        self.assertEqual(record["status"], "no-proof")

    def test_crashes_and_timeouts(self):
        self.assertEqual(self.classify(fake_run("", "ASSERTION VIOLATION", code=1))["status"], "crash")
        self.assertEqual(self.classify(fake_run("unsat\n", "", code=139))["status"], "crash")
        self.assertEqual(self.classify(fake_run(timeout=True))["status"], "timeout")

    def test_unknown_reference_never_counts_as_disagreement(self):
        self.assertEqual(self.classify(fake_run("unsat\n"), expected=None)["status"], "verified")

    def test_strip_commands_removes_conflicting_options_and_queries(self):
        source = ("(set-option :produce-proofs true)(set-option :sat.smt true)(set-option :solver.proof.log \"x\")"
                  "(set-option :smt.arith.validate true)(assert p)(check-sat)(get-proof)(get-model)(exit)")
        self.assertEqual(proof_matrix.strip_commands(source), "(assert p)(check-sat)")

    def test_summary_lists_every_status_column(self):
        records = [
            {"logic": "QF_LIA", "cell": "smt-clause-log", "status": "verified"},
            {"logic": "QF_LIA", "cell": "smt-clause-log", "status": "unverified-fallback"},
            {"logic": "QF_LIA", "cell": "reference", "status": "reference"},
        ]
        summary = proof_matrix.summarize(records)
        header, row = summary.split("\n")
        self.assertEqual(header.split()[3:], ["total", "unverified-fallback", "verified"])
        self.assertIn("QF_LIA / smt-clause-log", row)
        self.assertEqual(row.split()[3:], ["2", "1", "1"])
        self.assertNotIn("reference", row)


class TestBenchmarkLists(unittest.TestCase):
    def test_list_lines_carry_known_failure_annotations(self):
        path, known = proof_matrix.parse_list_line("  dir/b.smt2  smt-clause-log=checker-rejected # note\n")
        self.assertEqual(str(path), "dir/b.smt2")
        self.assertEqual(known, {"smt-clause-log": "checker-rejected"})
        self.assertIsNone(proof_matrix.parse_list_line("# comment only"))
        self.assertIsNone(proof_matrix.parse_list_line("   "))

    def test_bad_annotations_are_rejected(self):
        for line in ("b.smt2 smt-clause-log", "b.smt2 no-such-cell=crash", "b.smt2 smt-clause-log=verified"):
            with self.assertRaises(ValueError):
                proof_matrix.parse_list_line(line)

    def test_relative_entries_resolve_next_to_the_list_then_against_the_root(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "root"
            (root / "corpus").mkdir(parents=True)
            (root / "corpus" / "far.smt2").write_text("(check-sat)")
            lists = Path(directory) / "lists"
            lists.mkdir()
            (lists / "near.smt2").write_text("(check-sat)")
            listing = lists / "canary.txt"
            listing.write_text("near.smt2\ncorpus/far.smt2 smt-clause-log=crash\n%s\n" % (root / "corpus" / "far.smt2"))
            entries = list(proof_matrix.collect_benchmarks([str(listing)], root=str(root)))
            self.assertEqual([p for p, _ in entries],
                             [lists / "near.smt2", root / "corpus" / "far.smt2", root / "corpus" / "far.smt2"])
            self.assertEqual([k for _, k in entries], [{}, {"smt-clause-log": "crash"}, {}])
            without_root = list(proof_matrix.collect_benchmarks([str(listing)]))
            self.assertEqual(without_root[1][0], lists / "corpus" / "far.smt2")

    def test_known_failures_do_not_fail_the_run_but_stale_annotations_are_reported(self):
        def record(cell, status):
            return dict(proof_matrix.base_record("b.smt2", "QF_LIA", cell, "unsat"), status=status)
        known = {"smt-clause-log": "checker-rejected"}
        reproduced = proof_matrix.annotate_known(record("smt-clause-log", "checker-rejected"), known)
        self.assertTrue(reproduced["known_failure"])
        stale = proof_matrix.annotate_known(record("smt-clause-log", "verified"), known)
        self.assertEqual(stale["stale_expectation"], "checker-rejected")
        self.assertNotIn("known_failure", stale)
        other_cell = proof_matrix.annotate_known(record("legacy-proof-object", "crash"), known)
        self.assertNotIn("known_failure", other_cell)
        self.assertEqual(proof_matrix.failures([reproduced, stale]), [])
        self.assertEqual(proof_matrix.failures([other_cell]), [other_cell])
        self.assertEqual(proof_matrix.failures([record("smt-clause-log", "unverified-fallback")]), [])


@unittest.skipUnless(_Z3, "set Z3_EXE or put z3 on PATH")
class TestEndToEnd(unittest.TestCase):
    def run_matrix(self, sources, cells):
        with tempfile.TemporaryDirectory() as directory:
            paths = []
            for index, source in enumerate(sources):
                path = Path(directory) / ("b%d.smt2" % index)
                path.write_text(source)
                paths.append(str(path))
            out = Path(directory) / "out.jsonl"
            proc = subprocess.run([sys.executable, proof_matrix.__file__, "--z3", _Z3, "--timeout", "30",
                                   "--cells", cells, "--out", str(out), *paths], capture_output=True, text=True)
            records = [json.loads(line) for line in out.read_text().splitlines()]
            return proc, records

    def test_linear_arithmetic_clause_log_is_verified_and_sat_is_not_applicable(self):
        unsat = ("(set-logic QF_LRA)(declare-const x Real)(declare-const y Real)"
                 "(assert (> x y))(assert (> y 0.0))(assert (< x 0.0))(check-sat)")
        sat = "(set-logic QF_LRA)(declare-const x Real)(assert (> x 0.0))(check-sat)"
        proc, records = self.run_matrix([unsat, sat], "smt-clause-log,legacy-proof-object,arith-validate")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        by_key = {(Path(r["benchmark"]).name, r["cell"]): r for r in records}
        self.assertEqual(by_key[("b0.smt2", "smt-clause-log")]["status"], "verified")
        self.assertIn("farkas", by_key[("b0.smt2", "smt-clause-log")]["hints"])
        self.assertEqual(by_key[("b0.smt2", "smt-clause-log")]["fallbacks"], 0)
        self.assertEqual(by_key[("b0.smt2", "legacy-proof-object")]["status"], "no-checker")
        self.assertIn("asserted", by_key[("b0.smt2", "legacy-proof-object")]["rules"])
        self.assertEqual(by_key[("b0.smt2", "arith-validate")]["status"], "verified")
        for cell in ("smt-clause-log", "legacy-proof-object", "arith-validate"):
            self.assertEqual(by_key[("b1.smt2", cell)]["status"], "not-applicable")

    def test_array_axiom_logging_replays_with_array_fallbacks(self):
        # Regression for Z3Prover/z3#10922: this input crashed under sat.smt=true with
        # solver.proof.log. It must log and replay; the array hints fall back to the SMT
        # checker until an array plugin exists, so the class is unverified-fallback, not
        # verified, and a change in either direction should be a deliberate update here.
        canary = Path(proof_matrix.__file__).resolve().parent / "proof_canaries" / "array_axiom_log.smt2"
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory) / "out.jsonl"
            proc = subprocess.run([sys.executable, proof_matrix.__file__, "--z3", _Z3, "--timeout", "30",
                                   "--cells", "smt-clause-log,smt-clause-log-nopp", "--out", str(out), str(canary)],
                                  capture_output=True, text=True)
            records = [json.loads(line) for line in out.read_text().splitlines()]
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        by_cell = {r["cell"]: r for r in records}
        self.assertEqual(by_cell["reference"]["expected"], "unsat")
        for cell in ("smt-clause-log", "smt-clause-log-nopp"):
            self.assertEqual(by_cell[cell]["status"], "unverified-fallback", by_cell[cell])
            self.assertIn("array", by_cell[cell]["hints"])
            self.assertIn("array", by_cell[cell]["hint_misses"])
            self.assertGreater(by_cell[cell]["fallbacks"], 0)

    def test_known_failure_annotations_in_lists_are_honored_end_to_end(self):
        source = ("(set-logic QF_LRA)(declare-const x Real)(declare-const y Real)"
                  "(assert (> x y))(assert (> y 0.0))(assert (< x 0.0))(check-sat)")
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "b.smt2"
            path.write_text(source)
            listing = Path(directory) / "list.txt"
            listing.write_text("b.smt2 smt-clause-log=checker-rejected\n")
            out = Path(directory) / "out.jsonl"
            proc = subprocess.run([sys.executable, proof_matrix.__file__, "--z3", _Z3, "--timeout", "30",
                                   "--cells", "smt-clause-log", "--out", str(out), str(listing)],
                                  capture_output=True, text=True)
            record = [json.loads(l) for l in out.read_text().splitlines() if '"smt-clause-log"' in l][0]
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertEqual(record["status"], "verified")
        self.assertEqual(record["stale_expectation"], "checker-rejected")
        self.assertIn("stale known-failure annotations", proc.stdout)

    def test_nonlinear_lemmas_are_reported_as_fallbacks_not_verified(self):
        source = ("(set-logic QF_NIA)(declare-const x Int)(declare-const y Int)(assert (> x 0))(assert (> y 0))"
                  "(assert (= (* x y) 7))(assert (not (= x 1)))(assert (not (= x 7)))(check-sat)")
        proc, records = self.run_matrix([source], "smt-clause-log")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        record = [r for r in records if r["cell"] == "smt-clause-log"][0]
        self.assertEqual(record["status"], "unverified-fallback")
        self.assertGreater(record["fallbacks"], 0)
        self.assertIn("nla", record["hint_misses"])

    def test_preprocessing_only_contradictions_have_no_clause_proof(self):
        source = ("(set-logic QF_UF)(declare-sort U 0)(declare-fun f (U) U)(declare-const a U)(declare-const b U)"
                  "(assert (= a b))(assert (not (= (f a) (f b))))(check-sat)")
        proc, records = self.run_matrix([source], "smt-clause-log,smt-clause-log-nopp")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        by_cell = {r["cell"]: r for r in records}
        self.assertEqual(by_cell["smt-clause-log"]["status"], "no-proof")
        self.assertIn(by_cell["smt-clause-log-nopp"]["status"], ("verified", "no-proof"))

    def test_propositional_legacy_proofs_are_lean_checked_when_requested(self):
        if not (Path(proof_matrix.__file__).resolve().parents[2] / "scripts" / "check_lean.sh").exists():
            self.skipTest("Lean checker script not present")
        source = "(declare-const p Bool)(declare-const q Bool)(assert (or p q))(assert (not p))(assert (not q))(check-sat)"
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "b.smt2"
            path.write_text(source)
            out = Path(directory) / "out.jsonl"
            proc = subprocess.run([sys.executable, proof_matrix.__file__, "--z3", _Z3, "--lean",
                                   "--cells", "legacy-proof-object", "--out", str(out), str(path)],
                                  capture_output=True, text=True)
            self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
            record = [json.loads(l) for l in out.read_text().splitlines() if '"legacy-proof-object"' in l][0]
            self.assertEqual(record["status"], "verified")
            self.assertEqual(record["checker"], "lean")


if __name__ == "__main__":
    unittest.main()
