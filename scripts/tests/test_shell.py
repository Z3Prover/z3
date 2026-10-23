############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Regression tests for shell argument parsing.
############################################
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


class TestShellArguments(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        default = Path(__file__).resolve().parents[2] / "build" / (
            "z3.exe" if os.name == "nt" else "z3"
        )
        cls.z3 = Path(os.environ.get("Z3_EXE", default)).resolve()
        if not cls.z3.is_file():
            raise unittest.SkipTest("build the shell or set Z3_EXE to its path")

    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        (self.root / "input.cnf").write_text(
            "p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n"
        )

    def run_z3(self, *arguments):
        return subprocess.run(
            [str(self.z3), *arguments], cwd=self.root,
            text=True, capture_output=True, timeout=30,
        )

    def test_proof_output_assignments(self):
        (self.root / "proofs").mkdir()
        for filename in ("proof.out", "proof.drat", "proofs/proof.drat",
                         str(self.root / "absolute.drat")):
            for binary in ("true", "false"):
                for before_input in (True, False):
                    with self.subTest(filename=filename, binary=binary,
                                      before_input=before_input):
                        proof = self.root / filename
                        proof.unlink(missing_ok=True)
                        assignment = "sat.drat.file=" + filename
                        arguments = ([assignment, "input.cnf"] if before_input
                                     else ["input.cnf", assignment])
                        result = self.run_z3(
                            "-dimacs", *arguments, "sat.drat.binary=" + binary
                        )
                        self.assertEqual(result.returncode, 0, result.stderr)
                        self.assertIn("s UNSATISFIABLE", result.stdout)
                        self.assertTrue(proof.is_file(), result.stderr)
                        if binary == "false":
                            self.assertGreater(proof.stat().st_size, 0)

    def test_filenames_containing_equals(self):
        (self.root / "nested").mkdir()
        for filename in ("formula=value.cnf", "nested/formula=value.cnf",
                         "./timeout=10.cnf", "./sat.drat.file=input.cnf"):
            with self.subTest(filename=filename):
                (self.root / filename).write_text("p cnf 1 1\n1 0\n")
                result = self.run_z3("-dimacs", filename)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("s SATISFIABLE", result.stdout)

    def test_invalid_registered_values_remain_errors(self):
        for assignment in ("sat.drat.binary=bad.drat",
                           "sat.drat.binary=bad/value",
                           "timeout=bad.cnf"):
            for before_input in (True, False):
                with self.subTest(assignment=assignment,
                                  before_input=before_input):
                    arguments = ([assignment, "input.cnf"] if before_input
                                 else ["input.cnf", assignment])
                    result = self.run_z3("-dimacs", *arguments)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("parameter", result.stderr)
                    self.assertNotIn("s UNSATISFIABLE", result.stdout)

    def test_unknown_parameters_remain_errors(self):
        for assignment in ("unknown_parameter=true", "sat.unknown_parameter=true",
                           "unknown_module.parameter=true"):
            with self.subTest(assignment=assignment):
                result = self.run_z3("-dimacs", "input.cnf", assignment)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("unknown", result.stderr)

    def test_unknown_parameters_with_filename_values(self):
        (self.root / "input.smt2").write_text("(assert false)\n(check-sat)\n")
        for parameter in ("solver.unknown_parameter", "pp.unknown_parameter",
                          "unknown_module.parameter"):
            for value in ("out.plog.smt2", "out.log", "out.drat", "nested/out.smt2",
                          str(self.root / "out.smt2")):
                for before_input in (True, False):
                    with self.subTest(parameter=parameter, value=value,
                                      before_input=before_input):
                        assignment = parameter + "=" + value
                        arguments = ([assignment, "input.smt2"] if before_input
                                     else ["input.smt2", assignment])
                        result = self.run_z3("-smt2", *arguments)
                        self.assertNotEqual(result.returncode, 0)
                        self.assertIn("unknown", result.stderr)
                        self.assertIn(parameter, result.stderr)
                        self.assertNotIn("failed to open file", result.stdout)
                        self.assertNotIn("unsat", result.stdout)
                        self.assertFalse((self.root / value).exists())

    def test_solver_proof_log_assignments(self):
        (self.root / "input.smt2").write_text(
            "(declare-const x Int)\n(assert (> x 0))\n(check-sat-using smt)\n"
        )
        (self.root / "proofs").mkdir()
        for filename in ("out.plog.smt2", "out.log", "proofs/out.smt2",
                         str(self.root / "absolute.smt2")):
            for before_input in (True, False):
                with self.subTest(filename=filename, before_input=before_input):
                    proof = self.root / filename
                    proof.unlink(missing_ok=True)
                    assignment = "solver.proof.log=" + filename
                    arguments = ([assignment, "input.smt2"] if before_input
                                 else ["input.smt2", assignment])
                    result = self.run_z3("-smt2", *arguments)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertEqual(result.stdout.strip(), "sat")
                    self.assertTrue(proof.is_file(), result.stderr)
                    self.assertGreater(proof.stat().st_size, 0)

    def test_registered_parameter_before_and_after_input(self):
        (self.root / "input.smt2").write_text("(assert false)\n(check-sat)\n")
        for arguments in (("pp.max_width=50", "input.smt2"),
                          ("input.smt2", "pp.max_width=50")):
            with self.subTest(arguments=arguments):
                result = self.run_z3("-smt2", *arguments)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout.strip(), "unsat")

    def test_explicit_filenames_containing_equals(self):
        filename = "solver.proof.log=input.smt2"
        (self.root / filename).write_text("(check-sat)\n")
        for arguments in (("--", filename), ("-file:" + filename,),
                          ("./" + filename,)):
            with self.subTest(arguments=arguments):
                result = self.run_z3("-smt2", *arguments)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout.strip(), "sat")

    def test_log_extension_diagnostic(self):
        (self.root / "input.log").write_text("(check-sat)\n")
        result = self.run_z3("input.log")
        self.assertIn("input.log", result.stderr)
        self.assertIn("API trace", result.stderr)
        self.assertIn(".log extension", result.stderr)
        self.assertIn("-smt2", result.stderr)

        result = self.run_z3("-smt2", "input.log")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), "sat")
        self.assertNotIn("API trace", result.stderr)

        result = self.run_z3("-log", "input.log")
        self.assertNotIn(".log extension", result.stderr)

    def test_api_trace_compatibility(self):
        (self.root / "trace.log").write_text('M "trace replayed"\n')
        for arguments in (("trace.log",), ("-log", "trace.log"),
                          ("warning=false", "trace.log")):
            with self.subTest(arguments=arguments):
                result = self.run_z3(*arguments)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("trace replayed", result.stdout)
                self.assertNotIn("Error", result.stderr)
                if arguments[0] != "trace.log":
                    self.assertNotIn("WARNING", result.stderr)


if __name__ == "__main__":
    unittest.main()
