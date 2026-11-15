"""Tests for incremental proof and NNF accounting."""

import argparse
import contextlib
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest

from run_independent_incremental import run, summarize_log
from run_checker_regressions import file_sha256


class IncrementalAccountingTests(unittest.TestCase):
    def summarize(self, text):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "stdout"
            path.write_text(text, encoding="utf-8")
            return summarize_log(path)

    def test_completed_and_interrupted_queries_are_separate(self):
        result = self.summarize(
            "sat\nunsat\n; proof-check PARTIAL 1\n"
            "; proof-nnf nnf-pos-roots=3 nnf-pos-pending=1 nnf-neg-roots=2 nnf-neg-pending=0\n"
            "unsat\n")
        self.assertEqual(result["solver_sat"], 1)
        self.assertEqual(result["solver_unsat"], 2)
        self.assertEqual(result["proof_partial"], 1)
        self.assertEqual(result["unsat_without_verdict"], 1)
        self.assertEqual(result["nnf_pos_roots"], 3)
        self.assertEqual(result["nnf_pos_pending"], 1)
        self.assertEqual(result["nnf_reported_proofs"], 1)

    def test_unmatched_and_impossible_nnf_counts_are_rejected(self):
        with self.assertRaises(ValueError):
            self.summarize("; proof-nnf nnf-pos-roots=0 nnf-pos-pending=0 nnf-neg-roots=0 nnf-neg-pending=0\n")
        with self.assertRaises(ValueError):
            self.summarize("unsat\n; proof-check PARTIAL 1\n"
                           "; proof-nnf nnf-pos-roots=0 nnf-pos-pending=1 nnf-neg-roots=0 nnf-neg-pending=0\n")

    def test_phase_totals_include_every_query_and_replay_semantics(self):
        result = self.summarize(
            "unsat\n; proof-check ACCEPT\n"
            "; proof-stats solve_ms=1.5 marshal_ms=2.5 check_ms=3.5 "
            "expressions=7 declarations=3 proof_nodes=9 semantics=sorted-datatype assertions=2 pending=0\n"
            "unsat\n; proof-check PARTIAL 1\n"
            "; proof-stats solve_ms=4.5 marshal_ms=5.5 check_ms=6.5 "
            "expressions=8 declarations=3 proof_nodes=10 semantics=sorted-definition\n")
        self.assertEqual(result["phase_reported_proofs"], 2)
        self.assertEqual(result["phase_solve_ms"], 6)
        self.assertEqual(result["phase_marshal_ms"], 8)
        self.assertEqual(result["phase_check_ms"], 10)

    def test_replay_arguments_and_binary_identity_are_recorded(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            corpus = root / "inputs"
            corpus.mkdir()
            (corpus / "case.smt2").write_text("(assert false)(check-sat)")
            checker = root / "checker.py"
            checker.write_text(
                "import sys\n"
                "assert sys.argv[1:] == ['--definition-replay', '--interactive', "
                "'--diagnostics', '--timeout-ms', '5']\n"
                "assert '(assert false)' in sys.stdin.read()\n"
                "print('unsat\\n; proof-check ACCEPT')\n")
            args = argparse.Namespace(
                corpus=corpus, corpus_commit="test", max_cases=0,
                checker=Path(sys.executable), checker_arg=[str(checker), "--definition-replay"],
                output=root / "results", solver_timeout_ms=5,
                case_timeout_seconds=10, total_timeout_seconds=30, memory_limit_mb=0)
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(run(args), 0)
            selection = json.loads((args.output / "selection.json").read_text())
            self.assertEqual(selection["checker_arguments"], args.checker_arg)
            self.assertEqual(selection["checker_sha256"], file_sha256(Path(sys.executable)))
            summary = json.loads((args.output / "summary.json").read_text())
            self.assertEqual(summary["sessions_completed"], 1)
            self.assertEqual(summary["proof_accept"], 1)


if __name__ == "__main__":
    unittest.main()
