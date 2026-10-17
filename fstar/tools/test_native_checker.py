"""End-to-end direct SMT-LIB tests; no Python Z3 binding or proof transport."""
import os
from pathlib import Path
import subprocess
import queue
import tempfile
import threading
import unittest


@unittest.skipUnless(os.environ.get("Z3_FSTAR_CHECKER"),
                     "Set Z3_FSTAR_CHECKER to the built native checker")
class DirectCheckerTests(unittest.TestCase):
    def run_checker(self, source, *args):
        checker = os.environ["Z3_FSTAR_CHECKER"]
        command = (["wsl", "-e", "bash", "-c", checker + ' "$@"', "checker", *args]
                   if os.name == "nt" else [os.path.expanduser(checker), *args])
        return subprocess.run(command, input=source, text=True, capture_output=True, timeout=30)

    def test_checked_boolean_equality_and_array_refutations(self):
        for source in (
                "(assert false)",
                "(declare-const p Bool)(assert p)(assert (not p))",
                "(declare-sort U 0)(declare-const x U)(declare-const y U)"
                "(declare-fun f (U) U)(assert (= x y))(assert (not (= (f x) (f y))))",
                "(declare-const p Bool)(declare-const q Bool)(declare-const r Bool)"
                "(assert (or (and p q) r))(assert (not p))(assert (not r))",
                "(declare-const a (Array Int Int))(declare-const i Int)(declare-const v Int)"
                "(assert (not (= (select (store a i v) i) v)))"):
            with self.subTest(source=source):
                result = self.run_checker(source, "--stats")
                self.assertEqual((result.returncode, result.stdout.strip()), (0, "ACCEPT"),
                                 result.stderr)
                self.assertRegex(result.stderr, r"marshal_ms=\d+\.\d+")
                self.assertRegex(result.stderr, r"expressions=\d+")

    def test_linear_arithmetic_is_fully_checked(self):
        result = self.run_checker(
            "(declare-const x Real)(declare-const y Real)"
            "(assert (<= (+ x y) 0))(assert (> x 0))(assert (> y 0))")
        self.assertEqual((result.returncode, result.stdout.strip()), (0, "ACCEPT"),
                         result.stderr)

    def test_uncertified_nonlinear_arithmetic_remains_partial(self):
        result = self.run_checker(
            "(declare-const x Real)"
            "(assert (= (* x x) 2))(assert (= (* x x x) 3))")
        self.assertEqual(result.returncode, 3, result.stdout + result.stderr)
        self.assertRegex(result.stdout.strip(), r"^PARTIAL [1-9][0-9]*$")

    def test_sat_is_not_certified_unsat(self):
        result = self.run_checker("(declare-const x Int)(assert (> x 0))")
        self.assertEqual((result.returncode, result.stdout.strip()), (4, "SAT"), result.stderr)

    def test_timeout_is_not_certified_unsat(self):
        n = 20
        terms = ["(declare-const p%d_%d Bool)" % (i, j)
                 for i in range(n) for j in range(n - 1)]
        terms.extend("(assert (or %s))" % " ".join("p%d_%d" % (i, j) for j in range(n - 1))
                     for i in range(n))
        terms.extend("(assert (or (not p%d_%d) (not p%d_%d)))" % (i, j, k, j)
                     for j in range(n - 1) for i in range(n) for k in range(i))
        result = self.run_checker("\n".join(terms), "--timeout-ms", "1")
        self.assertEqual(result.returncode, 5, result.stdout + result.stderr)
        self.assertRegex(result.stdout, r"^UNKNOWN .*timeout")

    def test_malformed_input_and_arguments_report_errors(self):
        for source, args in (
                ("(assert missing)", ()),
                ('{"format":"resolution-v1","root":0}', ()),
                ("(assert false)", ("--smt2",)),
                ("(assert false)", ("--check-original-assertions",)),
                ("(assert false)", ("--timeout-ms", "-1")),
                ("(assert false)", ("--timeout-ms", "not-a-number")),
                ("(assert false)", ("--timeout-ms", "4294967296"))):
            with self.subTest(source=source, args=args):
                result = self.run_checker(source, *args)
                self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
                self.assertTrue(result.stderr.strip())
                self.assertNotIn("ACCEPT", result.stdout)

    def test_help_describes_only_smtlib_input(self):
        result = self.run_checker("", "--help")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("input.smt2", result.stdout)
        self.assertNotIn("JSON", result.stdout)
        self.assertNotIn("--smt2", result.stdout)

    def test_diagnostics_preserve_results_and_count_typed_obligations(self):
        for source in (
                "(assert false)",
                "(declare-const x Real)(declare-const y Real)"
                "(assert (<= (+ x y) 0))(assert (> x 0))(assert (> y 0))",
                "(declare-const x Real)"
                "(assert (= (* x x) 2))(assert (= (* x x x) 3))"):
            with self.subTest(source=source):
                plain = self.run_checker(source)
                diagnostic = self.run_checker(source, "--diagnostics", "--stats")
                self.assertEqual((diagnostic.returncode, diagnostic.stdout),
                                 (plain.returncode, plain.stdout), diagnostic.stderr)
                rows = [line.split("\t") for line in diagnostic.stderr.splitlines()
                        if line.startswith("obligation\t")]
                expected = int(plain.stdout.split()[1]) if plain.returncode == 3 else 0
                self.assertEqual(sum(int(row[2]) for row in rows), expected)
                self.assertIn("diagnostic\tchecked\tpending=%d\t" % expected, diagnostic.stderr)
                self.assertRegex(diagnostic.stderr, r"diagnose_ms=\d+\.\d+")
                if expected:
                    renamed = self.run_checker(source.replace("x", "a").replace("y", "b"),
                                               "--diagnostics")
                    shapes = lambda result: [(row[1], row[2], row[4]) for row in
                        (line.split("\t") for line in result.stderr.splitlines()
                         if line.startswith("obligation\t"))]
                    self.assertEqual(shapes(diagnostic), shapes(renamed))

    def test_file_mode_creates_no_proof_artifacts(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "input.smt2"
            path.write_text("(assert false)", encoding="ascii")
            native_path = str(path)
            if os.name == "nt":
                native_path = "/mnt/" + path.drive[0].lower() + "/" + str(path)[3:].replace("\\", "/")
            result = self.run_checker("", native_path)
            self.assertEqual((result.returncode, result.stdout.strip()), (0, "ACCEPT"), result.stderr)
            self.assertEqual(list(Path(directory).iterdir()), [path])

    def test_interactive_checks_scoped_assumptions_and_tactics(self):
        result = self.run_checker(
            "(declare-const p Bool)(assert p)(check-sat)(get-model)\n"
            "(check-sat-assuming ((not p)))\n"
            "(push)(assert (not p))(check-sat-using smt)(pop)(check-sat)\n"
            "(reset-assertions)(assert false)(check-sat)(exit)\n",
            "--interactive", "--stats", "--diagnostics")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout.splitlines().count("sat"), 2)
        self.assertEqual(result.stdout.splitlines().count("unsat"), 3)
        self.assertEqual(result.stdout.count("; proof-check ACCEPT"), 3)
        self.assertIn("define-fun p", result.stdout)
        self.assertEqual(result.stderr.count("marshal_ms="), 3)
        self.assertEqual(result.stderr.count("diagnostic\tchecked\tpending=0"), 3)

    def test_interactive_frames_multiline_strings_comments_and_quoted_symbols(self):
        result = self.run_checker(
            '; comment with ) and "\n'
            '(echo "a ""quoted (value)"" ; text")\n'
            '(declare-const |p(;)| Bool)\n(assert\n |p(;)|\n)\n'
            '(assert (not ; ignored closing )\n |p(;)|)) (check-sat)\n',
            "--interactive")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('quoted (value)', result.stdout)
        self.assertIn("unsat\n; proof-check ACCEPT\n", result.stdout)

    def test_interactive_reset_and_named_assertions(self):
        result = self.run_checker(
            "(assert false)(check-sat)(reset)"
            "(set-option :produce-unsat-cores true)"
            "(declare-const p Bool)(assert (! p :named A))"
            "(assert (! (not p) :named B))(check-sat)(get-unsat-core)",
            "--interactive")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout.count("; proof-check ACCEPT"), 2)
        self.assertIn("(A B)", result.stdout)

    def test_interactive_partial_is_not_a_certificate(self):
        result = self.run_checker(
            "(declare-const x Real)"
            "(assert (= (* x x) 2))(assert (= (* x x x) 3))(check-sat)",
            "--interactive")
        self.assertEqual(result.returncode, 3, result.stdout + result.stderr)
        self.assertRegex(result.stdout, r"unsat\n; proof-check PARTIAL [1-9][0-9]*")
        self.assertNotIn("ACCEPT", result.stdout)
        pending = next(line.split()[-1] for line in result.stdout.splitlines()
                       if line.startswith("; proof-check PARTIAL "))
        self.assertIn("pending=" + pending, result.stdout)

    def test_interactive_reports_per_check_proof_statistics(self):
        result = self.run_checker(
            "(assert false)(check-sat)(reset)"
            "(declare-const p Bool)(assert p)(check-sat-assuming ((not p)))",
            "--interactive")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        rows = [dict(field.split("=", 1) for field in line.split()[2:])
                for line in result.stdout.splitlines() if line.startswith("; proof-stats ")]
        self.assertEqual(len(rows), 2, result.stdout)
        self.assertEqual([int(row["assertions"]) for row in rows], [1, 2])
        self.assertEqual(int(rows[0]["proof_nodes"]), 1)
        self.assertEqual(int(rows[0]["proof_edges"]), 0)
        self.assertGreater(int(rows[1]["proof_nodes"]), 1)
        self.assertGreater(int(rows[1]["proof_edges"]), 0)
        for row in rows:
            self.assertEqual(row["pending"], "0")
            for key in ("expressions", "declarations"):
                self.assertGreater(int(row[key]), 0)
            for key in ("solve_ms", "marshal_ms", "check_ms"):
                self.assertGreaterEqual(float(row[key]), 0)
        self.assertEqual(result.stderr, "")

    def test_interactive_errors_do_not_disable_certification(self):
        result = self.run_checker(
            "(set-option :produce-proofs false)"
            "(assert missing)(assert false)(check-sat)",
            "--interactive")
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("interactive mode requires", result.stdout)
        self.assertIn("unknown constant missing", result.stdout)
        self.assertIn("unsat\n; proof-check ACCEPT\n", result.stdout)

    def test_interactive_exit_unknown_and_incomplete_input(self):
        result = self.run_checker("( ; comment\n exit )\n(assert missing)", "--interactive")
        self.assertEqual((result.returncode, result.stdout), (0, ""), result.stderr)
        result = self.run_checker(
            "(declare-const p Bool)(assert p)(check-sat-using skip)", "--interactive")
        self.assertEqual((result.returncode, result.stdout), (0, "unknown\n"), result.stderr)
        for source in ("(assert", '(echo "unfinished', "(assert |unfinished"):
            result = self.run_checker(source, "--interactive")
            self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
            self.assertIn("incomplete SMT-LIB command", result.stderr)
        result = self.run_checker("", "--interactive", "unused.smt2")
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)

    def test_interactive_replies_before_stdin_closes(self):
        checker = os.environ["Z3_FSTAR_CHECKER"]
        command = (["wsl", "-e", "bash", "-c", checker + ' "$@"',
                    "checker", "--interactive"]
                   if os.name == "nt" else [os.path.expanduser(checker), "--interactive"])
        process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE, text=True)
        replies = queue.Queue()
        reader = threading.Thread(
            target=lambda: replies.put([process.stdout.readline() for _ in range(3)]),
            daemon=True)
        try:
            reader.start()
            process.stdin.write("(assert false)(check-sat)\n")
            process.stdin.flush()
            lines = replies.get(timeout=15)
            self.assertEqual(lines[:2], ["unsat\n", "; proof-check ACCEPT\n"])
            self.assertTrue(lines[2].startswith("; proof-stats "), lines)
            _, error = process.communicate("(exit)\n", timeout=15)
            self.assertEqual(process.returncode, 0, error)
        finally:
            if process.poll() is None:
                process.kill()
                process.communicate()
            reader.join(timeout=5)


if __name__ == "__main__":
    unittest.main()
