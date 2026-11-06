"""End-to-end tests for the Cherry-extracted SQL user propagator."""

import argparse
import re
import subprocess
import unittest
from pathlib import Path


PRELUDE = """
(define-fun a () SqlQuery (sql.scan "a"))
(define-fun b () SqlQuery (sql.scan "b"))
(define-fun c () SqlQuery (sql.scan "c"))
(define-fun p () SqlPred (sql.predicate 0))
(define-fun q () SqlPred (sql.predicate 1))
(define-fun f () SqlProjection (sql.mapping 0))
(define-fun g () SqlProjection (sql.mapping 1))
"""

PAIRS = [
    ("filter-true", "(sql.filter sql.true a)", "a"),
    ("filter-false", "(sql.filter sql.false a)", "sql.empty"),
    ("filter-empty", "(sql.filter p sql.empty)", "sql.empty"),
    ("filter-idempotent", "(sql.filter p (sql.filter p a))", "(sql.filter p a)"),
    ("filter-fusion", "(sql.filter p (sql.filter q a))", "(sql.filter (sql.and p q) a)"),
    ("filter-project", "(sql.filter p (sql.project f a))",
     "(sql.project f (sql.filter (sql.preimage p f) a))"),
    ("filter-union", "(sql.filter p (sql.unionAll a b))",
     "(sql.unionAll (sql.filter p a) (sql.filter p b))"),
    ("filter-join", "(sql.filter p (sql.join q a b))", "(sql.join (sql.and q p) a b)"),
    ("project-empty", "(sql.project f sql.empty)", "sql.empty"),
    ("project-identity", "(sql.project sql.identity a)", "a"),
    ("project-fusion", "(sql.project f (sql.project g a))", "(sql.project (sql.compose f g) a)"),
    ("project-union", "(sql.project f (sql.unionAll a b))",
     "(sql.unionAll (sql.project f a) (sql.project f b))"),
    ("union-empty-left", "(sql.unionAll sql.empty a)", "a"),
    ("union-empty-right", "(sql.unionAll a sql.empty)", "a"),
    ("union-associative", "(sql.unionAll (sql.unionAll a b) c)", "(sql.unionAll a (sql.unionAll b c))"),
    ("cross-empty-left", "(sql.cross sql.empty a)", "sql.empty"),
    ("cross-empty-right", "(sql.cross a sql.empty)", "sql.empty"),
    ("cross-union", "(sql.cross (sql.unionAll a b) c)", "(sql.unionAll (sql.cross a c) (sql.cross b c))"),
    ("join-false", "(sql.join sql.false a b)", "sql.empty"),
    ("join-empty-left", "(sql.join p sql.empty a)", "sql.empty"),
    ("join-empty-right", "(sql.join p a sql.empty)", "sql.empty"),
    ("join-cross", "(sql.join sql.true a b)", "(sql.cross a b)"),
    ("join-union", "(sql.join p (sql.unionAll a b) c)",
     "(sql.unionAll (sql.join p a c) (sql.join p b c))"),
    ("count-one", "(sql.countOne a)", "(sql.count a)"),
    ("count-nullable", "(sql.countValue (sql.column 0) a)",
     "(sql.count (sql.filter (sql.notNull (sql.column 0)) a))"),
    ("count-case", "(sql.countWhen p a)", "(sql.count (sql.filter p a))"),
    ("count-union", "(sql.count (sql.unionAll a b))",
     "(sql.addCounts (sql.count a) (sql.count b))"),
]

SOLVER = None


class SqlSolverTests(unittest.TestCase):
    def run_solver(self, text, expected, *args):
        result = subprocess.run(
            [str(SOLVER), "--stats", *args], input=text, text=True,
            capture_output=True, timeout=30, check=True)
        self.assertEqual(result.stdout.strip(), expected, result.stderr)
        return result.stderr

    def test_all_rewrites(self):
        for name, left, right in PAIRS:
            with self.subTest(rule=name):
                stats = self.run_solver(
                    PRELUDE + f"(assert (distinct {left} {right}))", "unsat")
                self.assertRegex(stats, r"rewrites=[1-9]\d*")

    def test_egraph_and_saturation(self):
        stats = self.run_solver("""
            (declare-const x SqlQuery)
            (assert (= x (sql.unionAll (sql.scan "a") (sql.scan "b"))))
            (assert (distinct (sql.countOne x)
              (sql.addCounts (sql.count (sql.scan "a")) (sql.count (sql.scan "b")))))
            """, "unsat")
        self.assertRegex(stats, r"egraph_rewrites=[1-9]\d*")
        self.assertGreaterEqual(int(re.search(r"rewrites=(\d+)", stats).group(1)), 2)

    def test_builtin_theories(self):
        self.run_solver("""
            (assert (= (+ 1 1) 2))
            (assert (distinct
              (sql.project (sql.one (sql.column (+ 1 1))) (sql.scan (str.++ "ord" "ers")))
              (sql.project (sql.one (sql.column 2)) (sql.scan "orders"))))
            """, "unsat")

    def test_multiple_eclass_arguments(self):
        stats = self.run_solver("""
            (declare-const x SqlQuery)
            (declare-const p SqlPred)
            (declare-const q SqlPred)
            (assert (= p q))
            (assert (= x (sql.filter q (sql.scan "a"))))
            (assert (distinct (sql.filter p x) x))
            """, "unsat")
        self.assertRegex(stats, r"egraph_rewrites=[1-9]\d*")

    def test_registered_function_congruence(self):
        stats = self.run_solver("""
            (declare-const i Int)
            (declare-const j Int)
            (assert (<= i j))
            (assert (>= i j))
            (assert (distinct
              (sql.project (sql.one (sql.column i)) (sql.scan "a"))
              (sql.project (sql.one (sql.column j)) (sql.scan "a"))))
            """, "unsat")
        self.assertRegex(stats, r"congruences=[1-9]\d*")

    def test_non_theorems_are_not_equated(self):
        for left, right in [
                ("(sql.filter p a)", "a"),
                ("(sql.count a)", "(sql.count b)"),
                ("(sql.count sql.empty)", "sql.empty"),
                ("(sql.unionAll a b)", "(sql.unionAll b a)")]:
            with self.subTest(left=left):
                self.run_solver(PRELUDE + f"(assert (distinct {left} {right}))", "sat")

    def test_resource_limit(self):
        self.run_solver(PRELUDE + """
            (assert (distinct (sql.countOne (sql.unionAll a b))
              (sql.addCounts (sql.count a) (sql.count b))))
            """, "unknown", "--max-steps", "0")

    def test_cyclic_eclass_limit(self):
        self.run_solver("""
            (declare-const x SqlQuery)
            (declare-const a SqlQuery)
            (assert (= x (sql.unionAll x a)))
            """, "unknown", "--max-steps", "10")

    def test_backtracking(self):
        result = subprocess.run(
            [str(SOLVER), "--self-test"], capture_output=True, text=True, timeout=30, check=True)
        self.assertIn("self-tests passed", result.stdout)

    def test_bad_input(self):
        result = subprocess.run(
            [str(SOLVER)], input="(assert (= (sql.count 1) sql.empty))",
            capture_output=True, text=True, timeout=30)
        self.assertNotEqual(result.returncode, 0)
        self.assertNotIn(result.stdout.strip(), ("sat", "unsat"))

    def test_examples(self):
        examples = Path(__file__).resolve().parents[1] / "sql_solver" / "examples"
        for path in sorted(examples.glob("*.smt2")):
            expected = "sat" if path.stem == "non-equivalent" else "unsat"
            with self.subTest(example=path.name):
                self.run_solver(path.read_text(encoding="utf-8"), expected)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solver", required=True, type=Path)
    args, remaining = parser.parse_known_args()
    SOLVER = args.solver.resolve()
    unittest.main(argv=[__file__, *remaining], verbosity=2)
