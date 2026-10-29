"""Taelja orchestration tests, with optional real checker/converter integration."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from convert_taelja import convert


HORN = """(declare-sort U 0)
(declare-const a U)
(declare-fun p (U) Bool)
(declare-fun q (U) Bool)
(assert (p a))
(assert (or (not (p a)) (q a)))
(assert (not (q a)))
"""

EQUALITY = """(declare-sort U 0)
(declare-const a U)(declare-const b U)(declare-const c U)(declare-const d U)
(declare-fun f (U) U)(declare-fun g (U U) U)
(declare-fun p (U) Bool)(declare-fun q (U) Bool)
"""

EQUALITY_CASES = (
    ("transitivity", "(assert (= a b))(assert (= b c))(assert (not (= a c)))"),
    ("symmetry", "(assert (= a b))(assert (= c b))(assert (not (= a c)))"),
    ("congruence", "(assert (= a b))(assert (not (= (f a) (f b))))"),
    ("multiple-congruence", "(assert (= a b))(assert (= c d))"
                           "(assert (not (= (g a c) (g b d))))"),
    ("repeated-argument-congruence", "(assert (= a b))"
                                    "(assert (not (= (g a a) (g b b))))"),
    ("predicate-rewrite", "(assert (= a b))(assert (= b c))"
                          "(assert (p (f a)))(assert (not (p (f c))))"),
    ("negative-predicate-rewrite", "(assert (= a b))(assert (not (p (f a))))"
                                   "(assert (p (f b)))"),
    ("clause-rewrite", "(assert (= a b))(assert (p b))"
                       "(assert (or (not (p a)) (q c)))(assert (not (q c)))"),
    ("equality-resolution", "(assert (not (= a a)))"),
    ("equality-resolution-clause", "(assert (or (not (= a a)) (p a)))"
                                   "(assert (not (p a)))"),
    ("multiple-reflexive-disequalities", "(assert (or (not (= a a)) (not (= b b)) (p a)))"
                                        "(assert (not (p a)))"),
)

QUANTIFIED_CASES = (
    ("universal-unit", """(declare-sort U 0)(declare-const a U)(declare-fun p (U) Bool)
        (assert (forall ((x U)) (p x)))(assert (not (p a)))"""),
    ("universal-horn", HORN.replace("(assert (or (not (p a)) (q a)))",
        "(assert (forall ((x U)) (=> (p x) (q x))))")),
    ("repeated-instantiation", """(declare-sort U 0)(declare-const a U)
        (declare-fun f (U) U)(declare-fun p (U) Bool)
        (assert (forall ((x U)) (=> (p x) (p (f x)))))
        (assert (p a))(assert (not (p (f (f a)))))"""),
    ("many-sorted-binders", """(declare-sort U 0)(declare-sort V 0)
        (declare-const a U)(declare-const b V)
        (declare-fun p (U V) Bool)(declare-fun q (V U) Bool)
        (assert (forall ((x U) (y V)) (=> (p x y) (q y x))))
        (assert (p a b))(assert (not (q b a)))"""),
    ("nested-universals", """(declare-sort U 0)(declare-sort V 0)
        (declare-const a U)(declare-const b V)(declare-fun p (U V) Bool)
        (assert (forall ((x U)) (forall ((y V)) (p x y))))
        (assert (not (p a b)))"""),
    ("shadowed-binder", """(declare-sort U 0)(declare-const a U)(declare-fun p (U) Bool)
        (assert (forall ((x U)) (forall ((x U)) (p x))))(assert (not (p a)))"""),
    ("unused-binder", """(declare-sort U 0)(declare-sort V 0)
        (declare-const a U)(declare-fun p (U) Bool)
        (assert (forall ((x U) (y V)) (p x)))(assert (not (p a)))"""),
    ("universal-equality", """(declare-sort U 0)(declare-const a U)
        (declare-fun f (U) U)(declare-fun p (U) Bool)
        (assert (forall ((x U)) (= (f x) x)))
        (assert (p a))(assert (not (p (f a))))"""),
    ("universal-negative", """(declare-sort U 0)(declare-const a U)(declare-fun p (U) Bool)
        (assert (forall ((x U)) (not (p x))))(assert (p a))"""),
)


class TaeljaTests(unittest.TestCase):
    def test_checker_then_converter_and_atomic_publication(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source, output = root / "input.smt2", root / "proof.p"
            source.write_text(HORN, encoding="ascii")
            output.write_text("old output", encoding="ascii")

            def execute(command, **kwargs):
                if command[0] == "checker path":
                    self.assertEqual(command[1], "--tstp-out")
                    self.assertEqual(command[3], str(source))
                    Path(command[2]).write_text("cnf(a,axiom,p).\n", encoding="ascii")
                    return subprocess.CompletedProcess(command, 0, "ACCEPT\n", "")
                self.assertEqual(command[:2], ["taelja path", "--tptp"])
                self.assertTrue(Path(command[2]).is_file())
                self.assertEqual(output.read_text(), "old output")
                return subprocess.CompletedProcess(command, 0, "fof(goal,theorem,p).\n", "")

            with patch("convert_taelja.subprocess.run", side_effect=execute) as run:
                convert(source, output, "checker path", "taelja path")
            self.assertEqual(run.call_count, 2)
            self.assertEqual(output.read_text(), "fof(goal,theorem,p).\n")
            self.assertEqual(sorted(p.name for p in root.iterdir()), ["input.smt2", "proof.p"])
            output.write_text("old output", encoding="ascii")
            with patch("convert_taelja.subprocess.run", side_effect=execute), \
                 patch("convert_taelja.os.replace", side_effect=PermissionError("locked output")):
                with self.assertRaisesRegex(PermissionError, "locked output"):
                    convert(source, output, "checker path", "taelja path")
            self.assertEqual(output.read_text(), "old output")
            self.assertEqual(sorted(p.name for p in root.iterdir()), ["input.smt2", "proof.p"])

    def test_rejection_partial_sat_and_unknown_never_invoke_taelja(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for status, verdict in ((1, "REJECT"), (3, "PARTIAL 1"), (4, "SAT"), (5, "UNKNOWN timeout")):
                with self.subTest(verdict=verdict):
                    error = subprocess.CalledProcessError(status, ["checker"], verdict, "diagnostic")
                    with patch("convert_taelja.subprocess.run", side_effect=error) as run:
                        with self.assertRaisesRegex(RuntimeError, verdict):
                            convert(root / "input", root / "output", "checker", "taelja")
                    self.assertEqual(run.call_count, 1)
                    self.assertFalse((root / "output").exists())

    def test_converter_failure_preserves_existing_output_and_reports_diagnostics(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            output = root / "proof.p"
            output.write_text("old output", encoding="ascii")

            def execute(command, **kwargs):
                if command[0] == "checker":
                    Path(command[2]).write_text("proof", encoding="ascii")
                    return subprocess.CompletedProcess(command, 0, "ACCEPT\n", "")
                raise subprocess.CalledProcessError(1, command, "partial output", "not Horn")

            with patch("convert_taelja.subprocess.run", side_effect=execute):
                with self.assertRaisesRegex(RuntimeError, "not Horn"):
                    convert(root / "input", output, "checker", "taelja")
            self.assertEqual(output.read_text(), "old output")
            self.assertEqual([p.name for p in root.iterdir()], ["proof.p"])

    def test_timeout_missing_tool_and_invalid_timeout_are_errors(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for error, message in (
                    (subprocess.TimeoutExpired(["checker"], 1), "exceeded"),
                    (FileNotFoundError("missing checker"), "Cannot execute")):
                with self.subTest(error=error):
                    with patch("convert_taelja.subprocess.run", side_effect=error):
                        with self.assertRaisesRegex(RuntimeError, message):
                            convert(root / "input", root / "output", "checker", "taelja")
            for timeout in (0, -1, float("inf"), float("nan")):
                with self.subTest(timeout=timeout):
                    with self.assertRaisesRegex(ValueError, "finite positive"):
                        convert(root / "input", root / "output", "checker", "taelja", timeout)
            with self.assertRaisesRegex(ValueError, "overwrite"):
                convert(root / "input", root / "input", "checker", "taelja")

    def test_missing_export_and_empty_translation_are_errors(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            with patch("convert_taelja.subprocess.run",
                       return_value=subprocess.CompletedProcess([], 0, "ACCEPT\n", "")):
                with self.assertRaisesRegex(RuntimeError, "did not produce"):
                    convert(root / "input", root / "output", "checker", "taelja")

            def execute(command, **kwargs):
                if command[0] == "checker":
                    Path(command[2]).write_text("proof", encoding="ascii")
                    return subprocess.CompletedProcess(command, 0, "ACCEPT\n", "")
                return subprocess.CompletedProcess(command, 0, "", "")

            with patch("convert_taelja.subprocess.run", side_effect=execute):
                with self.assertRaisesRegex(RuntimeError, "empty derivation"):
                    convert(root / "input", root / "output", "checker", "taelja")
            self.assertFalse((root / "output").exists())

    @unittest.skipUnless(os.name != "nt" and os.environ.get("Z3_FSTAR_CHECKER") and
                         os.environ.get("TAELJA"),
                         "Set Z3_FSTAR_CHECKER and TAELJA for real conversion")
    def test_real_native_checker_and_taelja(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source, output = root / "input.smt2", root / "proof.p"
            cases = (
                    ("resolution", HORN),
                    ("implication", HORN.replace("(or (not (p a)) (q a))", "(=> (p a) (q a))")),
                    ("equality", HORN.replace("(declare-const a U)",
                                             "(declare-const a U)(declare-const b U)")
                                     .replace("(q a)", "(= a b)")),
                    ("multiple-premises", """(declare-sort U 0)(declare-const a U)
                     (declare-fun p (U) Bool)(declare-fun q (U) Bool)
                     (declare-fun r (U) Bool)(assert (p a))(assert (q a))
                     (assert (or (not (p a)) (not (q a)) (r a)))
                     (assert (not (r a)))"""))
            cases += tuple((name, EQUALITY + assertions) for name, assertions in EQUALITY_CASES)
            cases += QUANTIFIED_CASES
            for name, problem in cases:
                with self.subTest(name=name):
                    source.write_text(problem, encoding="ascii")
                    convert(source, output, os.environ["Z3_FSTAR_CHECKER"], os.environ["TAELJA"])
                    derivation = output.read_text(encoding="utf-8")
                    self.assertIn("inference(", derivation)
                    self.assertIn("theorem", derivation)
            source.write_text("(declare-sort U 0)(assert (forall ((x U)) false))",
                              encoding="ascii")
            output.write_text("existing output", encoding="ascii")
            with self.assertRaisesRegex(RuntimeError, "truth constant"):
                convert(source, output, os.environ["Z3_FSTAR_CHECKER"], os.environ["TAELJA"])
            self.assertEqual(output.read_text(), "existing output")


if __name__ == "__main__":
    unittest.main()
