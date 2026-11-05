import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from sleec import Translator, emit, parse, run_one, summarize


CVC5 = os.environ.get("CVC5") or shutil.which("cvc5")


class SleecTests(unittest.TestCase):
    def test_quantifiers_and_tuple_selectors(self):
        text = """
        (set-logic HO_ALL)
        (set-option :sets-exp true)
        (declare-const s (Set (Tuple Int Bool)))
        (assert (set.all (lambda ((x (Tuple Int Bool)))
          (set.some (lambda ((y (Tuple Int Bool)))
            (= ((_ tuple.select 0) x) ((_ tuple.select 0) y))) s)) s))
        (check-sat)
        (get-model)
        """
        result = Translator().translate(parse(text))
        self.assertIn("(FiniteSet __sleec_T0)", result)
        self.assertIn("(set.filter (lambda ((x __sleec_T0))", result)
        self.assertIn("(__sleec_T0_0 x)", result)
        self.assertIn("(__sleec_T0_0 y)", result)
        self.assertIn("(as set.empty (FiniteSet __sleec_T0))", result)
        self.assertNotIn("get-model", result)
        self.assertNotIn("set.all", result)
        self.assertNotIn("set.some", result)

    def test_product_is_nested_and_selectors_are_remapped(self):
        text = """
        (declare-const a (Set (Tuple Int)))
        (declare-const b (Set (Tuple Bool Int)))
        (assert (not (set.all (lambda ((p (Tuple Int Bool Int)))
          (and ((_ tuple.select 1) p)
               (= ((_ tuple.select 0) p) ((_ tuple.select 2) p))))
          (rel.product a b))))
        (check-sat)
        """
        result = Translator().translate(parse(text))
        self.assertNotIn("rel.product", result)
        self.assertIn("(__sleec_T0_0 __sleec_l1)", result)
        self.assertIn("(__sleec_T1_0 __sleec_r1)", result)
        self.assertIn("(__sleec_T1_1 __sleec_r1)", result)
        self.assertEqual(result.count("set.filter"), 2)

    def test_reject_unsupported_command(self):
        with self.assertRaises(ValueError):
            Translator().translate(parse("(push 1)"))

    def test_universal_counterexamples_preserves_nested_captures(self):
        source = """
        (declare-const s (Set (Tuple Int)))
        (assert (set.all (lambda ((x (Tuple Int)))
          (set.all (lambda ((y (Tuple Int)))
            (= ((_ tuple.select 0) x) ((_ tuple.select 0) y))) s)) s))
        (check-sat)
        """
        result = Translator(universal_counterexamples=True).translate(parse(source))
        self.assertIn("(lambda ((x __sleec_T0)) (not", result)
        self.assertIn("(lambda ((y __sleec_T0)) (not", result)
        self.assertIn("(= (__sleec_T0_0 x) (__sleec_T0_0 y))", result)
        self.assertEqual(result.count("(as set.empty (FiniteSet __sleec_T0))"), 2)

    def test_reject_nested_product_instead_of_mistranslating(self):
        source = """
        (declare-const s (Set (Tuple Int)))
        (assert (set.all (lambda ((p (Tuple Int Int Int))) true)
                        (rel.product (rel.product s s) s)))
        (check-sat)
        """
        with self.assertRaisesRegex(ValueError, "nested relational products"):
            Translator().translate(parse(source))

    def test_parser_comments_strings_and_balance(self):
        text = '; comment\n(set-info :source "text ; with ""quotes""")'
        self.assertEqual(emit(parse(text)[0]),
                         '(set-info :source "text ; with ""quotes""")')
        with self.assertRaises(ValueError):
            parse("(assert true")

    def test_summary_excludes_unknown_from_solved(self):
        rows = [
            dict(file="a", solver="z3", result="unknown", seconds=0.1),
            dict(file="a", solver="cvc5", result="sat", seconds=0.2),
            dict(file="b", solver="z3", result="unsat", seconds=0.3),
            dict(file="b", solver="cvc5", result="unsat", seconds=0.4),
        ]
        result = summarize(rows, 20)
        self.assertEqual(result["common_solved"], 1)
        self.assertEqual(result["disagreements"], [])
        self.assertAlmostEqual(result["z3"]["par2_seconds"], 40.3)

    def test_runner_distinguishes_timeout_unknown_and_error(self):
        cases = [
            (b"sat\n", b"", 0, "sat"),
            (b'unknown\n(:reason-unknown "incomplete (theory array)")\n',
             b"", 0, "unknown"),
            (b'unknown\n(:reason-unknown "timeout")\n', b"", 0, "timeout"),
            (b"timeout\n", b"", 0, "timeout"),
            (b"", b"cvc5 interrupted by timeout.\n", 1, "timeout"),
            (b'(error "bad input")\nsat\n', b"", 0, "error"),
        ]
        with tempfile.TemporaryDirectory() as directory:
            for stdout, stderr, code, expected in cases:
                with self.subTest(expected=expected, stdout=stdout):
                    proc = subprocess.CompletedProcess([], code, stdout, stderr)
                    with patch("sleec.subprocess.run", return_value=proc):
                        row = run_one("z3", Path("z3.exe"), Path("test.smt2"),
                                      20, Path(directory))
                    self.assertEqual(row["result"], expected)

    def test_runner_passes_solver_options(self):
        proc = subprocess.CompletedProcess([], 0, b"sat\n", b"")
        with tempfile.TemporaryDirectory() as directory:
            with patch("sleec.subprocess.run", return_value=proc) as run:
                run_one("z3", Path("z3.exe"), Path("test.smt2"), 20,
                        Path(directory), ["smt.finite_set.reuse_witness=true"])
            self.assertIn("smt.finite_set.reuse_witness=true", run.call_args.args[0])

    @unittest.skipUnless(CVC5, "set CVC5 to enable reference-solver checks")
    def test_reference_solver_semantics(self):
        some = "(set.some (lambda ((x (Tuple Int))) true) s)"
        empty = "(set.all (lambda ((x (Tuple Int))) false) s)"
        product = """(set.some (lambda ((p (Tuple Int Int)))
            (= ((_ tuple.select 0) p) ((_ tuple.select 1) p)))
            (rel.product s s))"""
        nested = """(set.all (lambda ((x (Tuple Int)))
            (set.some (lambda ((y (Tuple Int)))
              (= ((_ tuple.select 0) x) ((_ tuple.select 0) y))) s)) s)"""
        product_all = """(set.all (lambda ((p (Tuple Int Int)))
            (= ((_ tuple.select 0) p) ((_ tuple.select 1) p)))
            (rel.product s s))"""
        cases = [
            (empty, "sat"),
            (f"(and {empty} {some})", "unsat"),
            (some, "sat"),
            (f"(and {empty} {product})", "unsat"),
            (f"(and {some} (not {product}))", "unsat"),
            (f"(and {some} (not {nested}))", "unsat"),
            (f"(and {some} (not {product_all}))", "sat"),
            (f"(and {empty} (not {product_all}))", "unsat"),
        ]
        for expression, expected in cases:
            with self.subTest(expression=expression):
                source = ("(declare-const s (Set (Tuple Int)))"
                          f"(assert {expression})(check-sat)")
                translated = [
                    Translator(mode).translate(parse(source))
                    .replace("FiniteSet", "Set")
                    .replace("(set-logic ALL)", "(set-logic HO_ALL)")
                    for mode in (False, True)
                ]
                original = ("(set-logic HO_ALL)"
                            "(set-option :sets-exp true)" + source)
                for text in (original, *translated):
                    proc = subprocess.run(
                        [CVC5, "--lang=smt2", "--tlimit=20000"],
                        input=text, capture_output=True, text=True, timeout=22)
                    self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
                    answers = [line for line in proc.stdout.splitlines()
                               if line in ("sat", "unsat", "unknown")]
                    self.assertEqual(answers, [expected])


if __name__ == "__main__":
    unittest.main()
