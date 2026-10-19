import argparse
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

import qsat_benchmark as bench


class QsatBenchmarkTests(unittest.TestCase):
    def test_rewrite_only_actual_command(self):
        text = '''; (check-sat)
(set-info :source "quoted ""(check-sat)""; source")
(declare-const |(check-sat)| Bool)
(assert |(check-sat)|)
(check-sat)
(exit)
'''
        rewritten = bench.qsat_input(text)
        self.assertEqual(rewritten.count("(check-sat-using qsat)"), 1)
        self.assertIn('""(check-sat)""; source', rewritten)
        self.assertIn("(declare-const |(check-sat)| Bool)", rewritten)
        self.assertTrue(rewritten.endswith("(exit)\n"))

    def test_reject_incremental_and_malformed(self):
        for text in ("(check-sat)(check-sat)", "(push 1)(check-sat)",
                     "(check-sat-assuming ())", "(check-sat-using smt)",
                     "(reset)(check-sat)", "(assert true", ")", '(echo "bad)'):
            with self.subTest(text=text), self.assertRaises(ValueError):
                bench.qsat_input(text)

    def test_inline_command_comments(self):
        self.assertEqual(
            bench.qsat_input("(; before head\ncheck-sat ; after head\n)"),
            "(check-sat-using qsat)",
        )
        with self.assertRaises(ValueError):
            bench.qsat_input("(; comment\npush 1)(check-sat)")

    def test_candidate_parameters_do_not_change_baseline(self):
        args = argparse.Namespace(
            baseline=Path(sys.executable), candidate=Path(sys.executable),
            include_default=False, recursive_backjump=True, classic_mbp=True, mucyc=None,
        )
        baseline, candidate = bench.solvers(args)
        self.assertEqual(baseline["tactic"], "qsat")
        self.assertIn(":qsat_recursive_backjump true", candidate["tactic"])
        self.assertIn(":qsat_use_qel false", candidate["tactic"])

    def test_classification(self):
        for code, stdout, stderr, timeout, expected in (
            (0, "sat\n", "", False, "sat"),
            (0, "unsat,12\n", "", False, "unsat"),
            (0, "unknown\n", "", False, "unknown"),
            (0, "sat\n(error \"bad\")", "", False, "error"),
            (0, "sat\n", "(error \"bad\")", False, "error"),
            (1, "unsat\n", "", False, "error"),
            (-11, "", "", False, "crash"),
            (0, "sat\nunsat\n", "", False, "error"),
            (0, "", "", False, "error"),
            (-9, "sat\n", "", True, "timeout"),
        ):
            with self.subTest(expected=expected, stdout=stdout):
                self.assertEqual(bench.classify(code, stdout, stderr, timeout), expected)

    def test_mucyc_library_provenance(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "main.exe").write_bytes(b"executable")
            config = root / "config" / "solver"
            config.mkdir(parents=True)
            for name in ("mucyc_progress_ncr.json", "mucyc.json", "z3_smt.json"):
                (config / name).write_text("{}")
            (root / "lib").mkdir()
            library = root / "lib" / "libz3.so"
            library.write_bytes(b"original Z3 library")
            args = argparse.Namespace(baseline=None, candidate=None, mucyc=root)
            for solver in bench.solvers(args):
                self.assertEqual(solver["z3_library"], {
                    "path": str(library), "sha256": bench.sha256(library),
                })
            library.unlink()
            self.assertTrue(all("z3_library" not in solver for solver in bench.solvers(args)))

    def test_deterministic_stratified_selection(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for family in ("a", "b"):
                (root / family).mkdir()
                for i in range(5):
                    (root / family / f"{i}.smt2").write_text(
                        "(set-info :status unsat)(assert false)(check-sat)"
                    )
            first = bench.discover(root, 2)
            self.assertEqual(first, bench.discover(root, 2))
            self.assertEqual(len(first), 4)
            self.assertEqual({c["expected"] for c in first}, {"unsat"})
            self.assertEqual(len(bench.discover(root, 0)), 10)

    def test_raw_logs_statistics_and_timeout(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            solver = {"command": [sys.executable, "-c", "print('sat\\n(:memory 1.25)')"]}
            result = bench.run_case(solver, root / "input.smt2", root / "fast", 10)
            self.assertEqual(result["result"], "sat")
            self.assertEqual(result["statistics"], {"memory": "1.25"})
            self.assertTrue((root / "fast.stdout").exists())
            self.assertTrue((root / "fast.stderr").exists())
            solver = {"command": [sys.executable, "-c", "import time; time.sleep(10)"]}
            result = bench.run_case(solver, root / "input.smt2", root / "slow", 0.05)
            self.assertEqual(result["result"], "timeout")
            self.assertLess(result["elapsed"], 5)

    def test_wrong_answer_is_not_a_success(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            corpus = root / "corpus"
            corpus.mkdir()
            (corpus / "case.smt2").write_text(
                "(set-info :status unsat)(assert false)(check-sat)"
            )
            args = argparse.Namespace(
                corpus=corpus, per_family=0, timeout=10, output=root / "results",
            )
            configurations = [{
                "name": "broken", "qsat": True,
                "command": [sys.executable, "-c", "print('sat')"],
            }]
            self.assertEqual(bench.evaluate(args, configurations), 1)
            record = json.loads((args.output / "results.jsonl").read_text())
            self.assertEqual(record["result"], "wrong")
            self.assertEqual(record["answer"], "sat")
            summary = json.loads((args.output / "summary.json").read_text())
            self.assertEqual(summary["counts"]["broken"], {"wrong": 1})
            with patch.object(bench, "solvers", return_value=configurations):
                with self.assertRaises(FileExistsError):
                    bench.evaluate(args)


if __name__ == "__main__":
    unittest.main()
