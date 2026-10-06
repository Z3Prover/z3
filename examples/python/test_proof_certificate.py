############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Tests for native Boolean proof certificate export.
############################################
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import z3

_EXAMPLES = Path(__file__).resolve().parent
sys.path.insert(0, str(_EXAMPLES))
import proof_certificate


_CONTRADICTION = """\
(declare-const p Bool)
(assert p)
(assert (not p))
(check-sat)
(get-proof)
"""


class TestProofCertificate(unittest.TestCase):
    def assert_well_formed(self, certificate):
        declarations = certificate["declarations"]
        nodes = certificate["nodes"]
        proof_counts = {}
        for index, node in enumerate(nodes):
            self.assertGreaterEqual(node["declaration"], 0)
            self.assertLess(node["declaration"], len(declarations))
            decl = declarations[node["declaration"]]
            self.assertIn(decl["range"], ("Bool", "Proof"))
            self.assertEqual(decl["parameters"], [])
            for argument in node["arguments"]:
                self.assertGreaterEqual(argument, 0)
                self.assertLess(argument, index)
            if decl["range"] == "Proof":
                proof_counts[decl["name"]] = proof_counts.get(decl["name"], 0) + 1
        self.assertEqual(certificate["rule_counts"], proof_counts)
        for index in certificate["assertions"]:
            self.assertEqual(declarations[nodes[index]["declaration"]]["range"], "Bool")
        root = nodes[certificate["proof"]]
        self.assertEqual(declarations[root["declaration"]]["range"], "Proof")
        conclusion = nodes[root["arguments"][-1]]
        self.assertEqual(declarations[conclusion["declaration"]]["kind"], z3.Z3_OP_FALSE)

    def test_unsat_certificate_is_explicitly_unverified(self):
        certificate = proof_certificate.export_certificate(_CONTRADICTION)
        self.assertEqual(certificate["format"], "z3-native-proof-dag")
        self.assertEqual(certificate["format_version"], 1)
        self.assertEqual(certificate["z3_version"], z3.get_full_version())
        self.assertEqual(certificate["fragment"], "propositional")
        self.assertEqual(certificate["result"], "unsat")
        self.assertEqual(certificate["verification"], "unverified")
        self.assertEqual(certificate["source_smt2"], _CONTRADICTION)
        self.assertEqual(len(certificate["assertions"]), 2)
        self.assert_well_formed(certificate)
        self.assertEqual(json.loads(json.dumps(certificate)), certificate)

    def test_all_boolean_connectives(self):
        expressions = [
            "true", "false", "p", "(not p)", "(and p q r)", "(or p q r)",
            "(=> p q)", "(xor p q)", "(= p q)", "(distinct p q)",
            "(ite p q r)",
        ]
        prefix = "(declare-const p Bool)(declare-const q Bool)(declare-const r Bool)"
        for expression in expressions:
            with self.subTest(expression=expression):
                source = prefix + "(assert %s)(assert (not %s))" % (expression, expression)
                self.assert_well_formed(proof_certificate.export_certificate(source))

    def test_native_dag_is_preserved_exactly(self):
        context = z3.Context(proof=True)
        assertions = z3.parse_smt2_string("""
            (declare-const p Bool)(declare-const q Bool)
            (assert (or p q))(assert (=> p q))(assert (not q))
        """, ctx=context)
        solver = z3.Solver(ctx=context)
        solver.add(assertions)
        self.assertEqual(solver.check(), z3.unsat)
        proof = solver.proof()
        certificate = proof_certificate._encode_proof(assertions, proof)
        self.assert_well_formed(certificate)
        pending = list(zip(assertions, certificate["assertions"]))
        pending.append((proof, certificate["proof"]))
        seen_nodes, seen_declarations = {}, {}
        while pending:
            expr, index = pending.pop()
            if expr.get_id() in seen_nodes:
                self.assertEqual(index, seen_nodes[expr.get_id()])
                continue
            seen_nodes[expr.get_id()] = index
            node = certificate["nodes"][index]
            decl = expr.decl()
            declaration_index = node["declaration"]
            if decl.get_id() in seen_declarations:
                self.assertEqual(declaration_index, seen_declarations[decl.get_id()])
            seen_declarations[decl.get_id()] = declaration_index
            declaration = certificate["declarations"][declaration_index]
            self.assertEqual(declaration["name"], str(decl.name()))
            self.assertEqual(declaration["kind"], decl.kind())
            self.assertEqual(declaration["domain"], [str(decl.domain(i)) for i in range(decl.arity())])
            self.assertEqual(declaration["range"], str(decl.range()))
            self.assertEqual(declaration["parameters"], decl.params())
            self.assertEqual(len(node["arguments"]), expr.num_args())
            pending.extend(zip(expr.children(), node["arguments"]))
        self.assertEqual(len(seen_nodes), len(certificate["nodes"]))
        self.assertEqual(len(set(seen_nodes.values())), len(seen_nodes))
        self.assertEqual(len(seen_declarations), len(certificate["declarations"]))
        self.assertEqual(len(set(seen_declarations.values())), len(seen_declarations))

    def test_duplicate_assertions_share_nodes(self):
        source = "(declare-const p Bool)(assert p)(assert p)(assert (not p))"
        certificate = proof_certificate.export_certificate(source)
        self.assertEqual(len(certificate["assertions"]), 3)
        self.assertEqual(certificate["assertions"][0], certificate["assertions"][1])
        self.assert_well_formed(certificate)

    def test_deep_assertions_do_not_require_python_recursion(self):
        depth = 1200
        source = "(declare-const p Bool)(assert " + "(not " * depth + "p"
        source += ")" * depth + ")(assert false)"
        certificate = proof_certificate.export_certificate(source)
        self.assertGreater(len(certificate["nodes"]), depth)
        self.assert_well_formed(certificate)

    def test_named_assertions_do_not_introduce_tracking_assumptions(self):
        source = """\
(declare-const p Bool)
(assert (! p :named positive))
(assert (! (not p) :named negative))
"""
        certificate = proof_certificate.export_certificate(source)
        declarations = certificate["declarations"]
        names = {decl["name"] for decl in declarations}
        self.assertNotIn("positive", names)
        self.assertNotIn("negative", names)
        for node in certificate["nodes"]:
            decl = declarations[node["declaration"]]
            if decl["kind"] == z3.Z3_OP_PR_ASSERTED:
                self.assertIn(node["arguments"][-1], certificate["assertions"])
        self.assert_well_formed(certificate)

    def test_quoted_tokens_comments_and_definitions(self):
        source = '''\
; (push 1) is only a comment
(set-option :produce-proofs true)
(set-logic QF_UF)
(set-info :source "Text with ""quotes"", (check-sat), and ; comments")
(declare-const |p; (push 1)| Bool)
(define-fun negate ((x Bool)) Bool (not x))
(assert |p; (push 1)|)
(assert (negate |p; (push 1)|))
(check-sat)
(get-proof)
(exit)
'''
        certificate = proof_certificate.export_certificate(source)
        self.assertEqual(certificate["source_smt2"], source)
        self.assert_well_formed(certificate)

    def test_unsupported_commands_are_rejected(self):
        commands = [
            "(push 1)", "(pop 1)", "(reset)", "(reset-assertions)",
            "(check-sat-assuming ())", "(get-model)", "(get-unsat-core)",
            '(include "other.smt2")', '(echo "unsat")', "(minimize 0)",
            "(set-option :produce-proofs false)",
            '(set-option :regular-output-channel "output.txt")',
        ]
        for command in commands:
            with self.subTest(command=command):
                with self.assertRaises(proof_certificate.ProofExportError):
                    proof_certificate.export_certificate(command + "(assert false)")

    def test_quoted_symbols_match_the_z3_scanner(self):
        for name in ["||", "|p with spaces|", "|p; (push 1)|", "|p\nq|"]:
            with self.subTest(name=name):
                source = "(declare-const %s Bool)(assert %s)(assert (not %s))" % (name, name, name)
                self.assert_well_formed(proof_certificate.export_certificate(source))

    def test_backslashes_in_quoted_symbols_are_rejected(self):
        for name in [r"|p\|;(push 1)|", r"|p\\|", r"|p\q|"]:
            with self.subTest(name=name):
                source = "(declare-const %s Bool)(assert %s)(assert (not %s))" % (name, name, name)
                with self.assertRaisesRegex(proof_certificate.ProofExportError, "unsupported or unterminated token"):
                    proof_certificate.export_certificate(source)

    def test_nonstandard_block_comments_are_rejected(self):
        with self.assertRaises(proof_certificate.ProofExportError):
            proof_certificate.export_certificate("(assert #| comment |# false)")

    def test_invalid_query_sequences_are_rejected(self):
        suffixes = [
            "(check-sat)(check-sat)", "(get-proof)",
            "(check-sat)(get-proof)(get-proof)",
            "(check-sat)(assert false)", "(check-sat)(declare-const q Bool)",
            "(exit)(assert false)", "(check-sat p)",
            "(check-sat)(get-proof p)", "(exit now)",
        ]
        for suffix in suffixes:
            with self.subTest(suffix=suffix):
                with self.assertRaises(proof_certificate.ProofExportError):
                    proof_certificate.export_certificate("(assert false)" + suffix)

    def test_malformed_input_is_rejected(self):
        for source in ["(", ")", "()", "assert false", '(set-info :source "broken)',
                       "(declare-const |broken Bool)", "(assert false"]:
            with self.subTest(source=source):
                with self.assertRaises(proof_certificate.ProofExportError):
                    proof_certificate.export_certificate(source)
        with self.assertRaises(z3.Z3Exception):
            proof_certificate.export_certificate("(assert undeclared)")

    def test_nonpropositional_input_is_rejected_even_with_false(self):
        problems = [
            "(declare-const x Int)(assert (= x 0))",
            "(declare-const x Real)(assert (< x 0.0))",
            "(declare-const x (_ BitVec 8))(assert (= x #x00))",
            "(declare-const a (Array Bool Bool))(assert (select a true))",
            "(declare-fun f (Bool) Bool)(assert (f true))",
            "(assert (forall ((p Bool)) p))",
            "(declare-const p Bool)(assert ((_ at-most 1) p))",
        ]
        for problem in problems:
            with self.subTest(problem=problem):
                with self.assertRaises(proof_certificate.ProofExportError):
                    proof_certificate.export_certificate(problem + "(assert false)")

    def test_parameterized_declarations_are_not_silently_dropped(self):
        context = z3.Context(proof=True)
        p = z3.Bool("p", ctx=context)
        solver = z3.Solver(ctx=context)
        solver.add(p, z3.Not(p))
        self.assertEqual(solver.check(), z3.unsat)
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "parameters"):
            proof_certificate._encode_proof([z3.PbLe([(p, 1)], 0)], solver.proof())

    def test_sat_has_no_certificate(self):
        for source in ["", "(assert true)", "(declare-const p Bool)(assert p)"]:
            with self.subTest(source=source):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, "^sat:"):
                    proof_certificate.export_certificate(source)

    def test_unknown_preserves_reason_and_never_requests_a_proof(self):
        with patch.object(z3.Solver, "check", return_value=z3.unknown), \
                patch.object(z3.Solver, "reason_unknown", return_value="resource limit"), \
                patch.object(z3.Solver, "proof") as proof:
            with self.assertRaisesRegex(proof_certificate.ProofExportError, "unknown: resource limit"):
                proof_certificate.export_certificate(_CONTRADICTION)
            proof.assert_not_called()

    def test_missing_proof_is_an_error(self):
        with patch.object(z3.Solver, "proof", side_effect=z3.Z3Exception("no current proof")):
            with self.assertRaisesRegex(z3.Z3Exception, "no current proof"):
                proof_certificate.export_certificate(_CONTRADICTION)

    def test_nonproof_or_wrong_conclusion_is_rejected(self):
        with patch.object(z3.Solver, "proof", return_value=z3.And(True, False)):
            with self.assertRaisesRegex(proof_certificate.ProofExportError, "does not conclude false"):
                proof_certificate.export_certificate(_CONTRADICTION)

    def test_other_contexts_are_unaffected(self):
        context = z3.Context(proof=False)
        solver = z3.Solver(ctx=context)
        solver.add(z3.BoolVal(False, ctx=context))
        proof_certificate.export_certificate(_CONTRADICTION)
        self.assertEqual(solver.check(), z3.unsat)
        with self.assertRaises(z3.Z3Exception):
            solver.proof()

    def run_cli(self, *args, source=None):
        return subprocess.run(
            [sys.executable, str(_EXAMPLES / "proof_certificate.py"), *args],
            input=source, text=True, capture_output=True, check=False,
        )

    def test_cli_standard_input(self):
        result = self.run_cli("-", source=_CONTRADICTION)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stderr, "")
        certificate = json.loads(result.stdout)
        self.assertEqual(certificate["source_smt2"], _CONTRADICTION)
        self.assert_well_formed(certificate)

    def test_cli_file_preserves_source(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "input.smt2"
            source = _CONTRADICTION.replace("\n", "\r\n")
            path.write_bytes(source.encode("utf-8"))
            result = self.run_cli(str(path))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)["source_smt2"], source)

    def test_cli_failures_have_no_certificate(self):
        cases = [
            ("(assert true)", "sat:"),
            ("(check-sat-assuming ())", "unsupported SMT-LIB command"),
            ("(assert undeclared)", "undeclared"),
        ]
        for source, message in cases:
            with self.subTest(source=source):
                result = self.run_cli("-", source=source)
                self.assertEqual(result.returncode, 2)
                self.assertEqual(result.stdout, "")
                self.assertIn(message, result.stderr)
        with tempfile.TemporaryDirectory() as directory:
            result = self.run_cli(str(Path(directory) / "missing.smt2"))
        self.assertEqual(result.returncode, 2)
        self.assertEqual(result.stdout, "")
        self.assertIn("missing.smt2", result.stderr)


if __name__ == "__main__":
    unittest.main()
