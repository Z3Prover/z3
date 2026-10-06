############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Tests for native Boolean proof certificate export.
############################################
from fractions import Fraction
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
import proof_clause_log


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



_LRA = """\
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (>= (+ (* 2.0 x) y) 5.0))
(assert (<= (+ x (* 3.0 z)) 1.0))
(assert (<= (- y (* 6.0 z)) 2.0))
(assert (<= x 0.0))
(check-sat)
"""
# The clause log Z3 writes for _LRA with sat.smt=true and preprocessing off.
_LRA_LOG = """\
(declare-fun y () Real)
(declare-fun x () Real)
(define-const $7 Real (* 2.0 x))
(define-const $9 Real (+ $7 y))
(define-const $11 Bool (>= $9 5.0))
(assume $11)
(declare-fun z () Real)
(define-const $14 Real (* 3.0 z))
(define-const $15 Real (+ x $14))
(define-const $17 Bool (<= $15 1.0))
(assume $17)
(define-const $19 Real (* 6.0 z))
(define-const $20 Real (- y $19))
(define-const $21 Bool (<= $20 2.0))
(assume $21)
(define-const $23 Bool (<= x 0.0))
(assume $23)
(declare-fun farkas (Int Bool Int Bool Int Bool) Proof)
(define-const $27 Proof (farkas 1 $11 2 $17 1 $21))
(infer (not $11) (not $17) (not $21) $27)
(declare-fun rup () Proof)
(infer rup)
"""


def _z3_available():
    try:
        return subprocess.run([proof_certificate.default_z3_executable(), "--version"],
                              capture_output=True).returncode == 0
    except OSError:
        return False


class TestFragmentClassification(unittest.TestCase):
    def classify(self, source):
        assertions, fragment = proof_certificate.parse_assertions(source, z3.Context())
        return fragment

    def test_propositional_and_linear_real_inputs_are_classified(self):
        self.assertEqual(self.classify(_CONTRADICTION), "propositional")
        self.assertEqual(self.classify(_LRA), "qf_lra")
        mixed = "(declare-const p Bool)(declare-const x Real)(assert (or p (< (/ x 2.0) (- 1.5))))"
        self.assertEqual(self.classify(mixed), "qf_lra")

    def test_nonlinear_integer_and_other_inputs_are_rejected(self):
        for source, message in [
            ("(declare-const x Real)(assert (> (* x x) 1.0))", "nonlinear"),
            ("(declare-const x Real)(declare-const y Real)(assert (> (/ x y) 1.0))", "division"),
            ("(declare-const x Int)(assert (> x 1))", "unsupported sort"),
            ("(declare-fun f (Real) Real)(declare-const x Real)(assert (> (f x) 1.0))", "uninterpreted functions"),
            ("(declare-const p Bool)(declare-const x Real)(assert (> (ite p x 1.0) 2.0))", "ite"),
        ]:
            with self.subTest(source=source):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, message):
                    self.classify(source)

    def test_legacy_exporter_still_rejects_arithmetic(self):
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "clause-log"):
            proof_certificate.export_certificate(_LRA)


class TestLinearCombination(unittest.TestCase):
    def test_farkas_sum_refutes(self):
        F = Fraction
        constraints = [  # 2x + y >= 5, x + 3z <= 1, y - 6z <= 2 with coefficients 1, 2, 1
            (F(1), "<=", {"x": F(-2), "y": F(-1)}, F(5)),
            (F(2), "<=", {"x": F(1), "z": F(3)}, F(-1)),
            (F(1), "<=", {"y": F(1), "z": F(-6)}, F(-2)),
        ]
        self.assertTrue(proof_certificate.linear_combination_refutes(constraints))
        self.assertFalse(proof_certificate.linear_combination_refutes(constraints[:2]))
        # Wrong coefficients leave a variable or make the constant harmless.
        wrong = [(F(1),) + constraint[1:] for constraint in constraints]
        self.assertFalse(proof_certificate.linear_combination_refutes(wrong))
        self.assertFalse(proof_certificate.linear_combination_refutes(
            [(F(-1),) + constraints[0][1:]] + constraints[1:]))

    def test_strictness_and_equalities(self):
        F = Fraction
        # x <= 0 and x >= 0 are consistent, x < 0 and x >= 0 are not.
        weak = [(F(1), "<=", {"x": F(1)}, F(0)), (F(1), "<=", {"x": F(-1)}, F(0))]
        self.assertFalse(proof_certificate.linear_combination_refutes(weak))
        strict = [(F(1), "<", {"x": F(1)}, F(0)), (F(1), "<=", {"x": F(-1)}, F(0))]
        self.assertTrue(proof_certificate.linear_combination_refutes(strict))
        # Equality multipliers are solved for: 15 * (x3 - x4 = 1) is needed here.
        hint = [
            (F(1), "=", {"x3": F(2), "x4": F(-2)}, F(-2)),
            (F(1), "<", {"x2": F(-3), "x1": F(2)}, F(-1)),
            (F(8), "<=", {"x1": F(2), "x4": F(3)}, F(3)),
            (F(10), "<", {"x3": F(-3), "x1": F(-1)}, F(5)),
            (F(1), "<=", {"x2": F(3), "x5": F(2)}, F(-1)),
            (F(2), "<=", {"x5": F(-1), "x1": F(-3), "x0": F(-3)}, F(-5)),
            (F(2), "<=", {"x4": F(3), "x0": F(3), "x1": F(-1)}, F(0)),
        ]
        self.assertTrue(proof_certificate.linear_combination_refutes(hint))
        inconsistent = [(F(1), "=", {"x": F(1)}, F(-1)), (F(1), "=", {"x": F(1)}, F(-2))]
        self.assertTrue(proof_certificate.linear_combination_refutes(inconsistent))
        consistent = [(F(1), "=", {"x": F(1)}, F(-1)), (F(1), "=", {"y": F(1)}, F(-2))]
        self.assertFalse(proof_certificate.linear_combination_refutes(consistent))


class TestClauseLogReplay(unittest.TestCase):
    def replay(self, source, log):
        context = z3.Context()
        assertions, fragment = proof_certificate.parse_assertions(source, context)
        return proof_clause_log.build_certificate(source, fragment, assertions, log, context)

    def test_recorded_log_becomes_a_well_formed_dag(self):
        certificate = self.replay(_LRA, _LRA_LOG)
        self.assertEqual(certificate["fragment"], "qf_lra")
        self.assertEqual(certificate["verification"], "unverified")
        self.assertEqual(certificate["source_smt2"], _LRA)
        self.assertEqual(len(certificate["assertions"]), 4)
        counts = certificate["rule_counts"]
        self.assertEqual(counts["th-lemma"], 1)
        self.assertEqual(counts["asserted"], 4)
        self.assertEqual(counts["lemma"], 1)  # the final rup step
        self.assertIn("unit-resolution", counts)
        th_lemma = [d for d in certificate["declarations"] if d["name"] == "th-lemma"]
        self.assertEqual(th_lemma[0]["parameters"], ["farkas", "1", "2", "1"])
        self.assertEqual(th_lemma[0]["domain"], ["Bool"])
        sorts = {d["range"] for d in certificate["declarations"]}
        self.assertEqual(sorts, {"Bool", "Real", "Proof"})
        numerals = sorted(d["name"] for d in certificate["declarations"] if d["kind"] == z3.Z3_OP_ANUM)
        self.assertEqual(numerals, ["1", "2", "3", "5", "6", "0"][:0] + sorted(["0", "1", "2", "3", "5", "6"]))
        root = certificate["nodes"][certificate["proof"]]
        conclusion = certificate["nodes"][root["arguments"][-1]]
        self.assertEqual(certificate["declarations"][conclusion["declaration"]]["kind"], z3.Z3_OP_FALSE)
        for index, node in enumerate(certificate["nodes"]):
            self.assertTrue(all(argument < index for argument in node["arguments"]))

    def test_rewritten_assumptions_are_tied_to_their_assertions(self):
        source = ("(declare-const x Real)(declare-const y Real)"
                  "(assert (and (> x 5.0) (< y 2.0)))(assert (= x (+ y 1.0)))")
        log = """\
(declare-fun x () Real)
(define-const $1 Bool (<= x 5.0))
(assume (not $1))
(declare-fun y () Real)
(define-const $2 Bool (>= y 2.0))
(assume (not $2))
(define-const $3 Real (+ 1.0 y))
(define-const $4 Bool (= x $3))
(assume $4)
(declare-fun farkas (Int Bool Int Bool Int Bool) Proof)
(define-const $5 Bool (not $1))
(define-const $6 Bool (not $2))
(define-const $7 Proof (farkas 1 $4 1 $6 1 $5))
(infer $1 $2 (not $4) $7)
(declare-fun rup () Proof)
(infer rup)
"""
        certificate = self.replay(source, log)
        counts = certificate["rule_counts"]
        self.assertEqual(counts["and-elim"], 2)
        self.assertEqual(counts["rewrite"], 3)
        self.assertEqual(counts["mp"], 3)
        self.assertEqual(counts["th-lemma"], 1)

    def test_split_assertions_use_a_cnf_lemma_and_tautologies_need_no_source(self):
        source = "(declare-const p Bool)(declare-const q Bool)(assert (xor p q))(assert (= p q))"
        log = """\
(declare-fun p () Bool)
(declare-fun q () Bool)
(assume p q)
(assume (not p) (not q))
(assume (not p) q)
(assume p (not q))
(assume (not false))
(assume p (not p))
(declare-fun rup () Proof)
(infer p rup)
(infer q rup)
(infer rup)
"""
        certificate = self.replay(source, log)
        counts = certificate["rule_counts"]
        cnf = [d for d in certificate["declarations"] if d["name"] == "th-lemma"]
        self.assertEqual([d["parameters"] for d in cnf], [["cnf"]])
        self.assertEqual(counts["th-lemma"], 4)
        self.assertEqual(counts["def-axiom"], 2)
        self.assertEqual(counts["lemma"], 3)

    def test_tseitin_hints_are_gate_clauses_and_gates_support_propagation(self):
        source = ("(declare-const p Bool)(declare-const q Bool)(declare-const r Bool)"
                  "(assert (or p (and q r)))(assert (not p))(assert (not q))")
        log = """\
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun r () Bool)
(define-const $1 Bool (and q r))
(assume p $1)
(assume (not p))
(assume (not q))
(declare-fun tseitin (Bool Bool) Proof)
(define-const $2 Proof (tseitin (not $1) q))
(infer (not $1) q $2)
(declare-fun rup () Proof)
(infer rup)
"""
        certificate = self.replay(source, log)
        counts = certificate["rule_counts"]
        self.assertGreaterEqual(counts["def-axiom"], 1)
        self.assertNotIn("th-lemma", counts)
        self.assertEqual(counts["lemma"], 1)

    def test_deleted_and_repeated_empty_clauses_are_handled(self):
        log = _LRA_LOG.replace("(infer rup)\n", "(del (not $11) (not $17) (not $21))\n(infer rup)\n(infer rup)\n")
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "not derivable"):
            self.replay(_LRA, log)
        log = _LRA_LOG + "(infer rup)\n"
        certificate = self.replay(_LRA, log)
        self.assertEqual(certificate["rule_counts"]["lemma"], 2)

    def test_bad_hints_and_logs_are_rejected(self):
        cases = [
            (_LRA_LOG.replace("(farkas 1 $11 2 $17 1 $21)", "(farkas 1 $11 1 $17 1 $21)"), "do not refute"),
            (_LRA_LOG.replace("(assume $23)\n", "(assume $23)\n(infer (not $23) rup)\n"), "not derivable"),
            (_LRA_LOG.replace("(declare-fun z () Real)", "(declare-fun w () Real)"), "absent from the input"),
            (_LRA_LOG.replace("(farkas 1 $11 2 $17 1 $21)", "(nla 1 $11)"), "unsupported clause-log hint"),
            ("(assume $9)", "undeclared or fresh symbol"),
        ]
        for log, message in cases:
            with self.subTest(message=message):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, message):
                    self.replay(_LRA, log)

    def test_contradictions_outside_the_log_are_tied_to_the_assertions(self):
        # Without the final rup step, propagation still closes the database.
        certificate = self.replay(_LRA, _LRA_LOG.replace("(infer rup)\n", ""))
        self.assertEqual(certificate["rule_counts"]["lemma"], 1)
        # An empty log: the contradiction was found while asserting.
        source = "(declare-const p Bool)(assert p)(assert (not p))"
        certificate = self.replay(source, "")
        self.assertEqual(certificate["fragment"], "propositional")
        self.assertEqual([d["parameters"] for d in certificate["declarations"] if d["name"] == "th-lemma"],
                         [["cnf"]])
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "does not match any original"):
            self.replay("(declare-const p Bool)(assert p)", "")

    def test_unrelated_assumptions_are_rejected(self):
        source = "(declare-const x Real)(assert (>= x 1.0))"
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "does not match any original"):
            self.replay(source, "(declare-fun x () Real)\n(define-const $1 Bool (<= x 5.0))\n(assume $1)\n")

    def test_log_terms_are_parsed_exactly(self):
        self.assertEqual(proof_clause_log._number("5"), 5)
        self.assertEqual(proof_clause_log._number(["-", ["/", "13.0", "2.0"]]), Fraction(-13, 2))
        with self.assertRaises(proof_certificate.ProofExportError):
            proof_clause_log._number(["/", "1.0", "0.0"])
        commands = proof_clause_log._sexpressions("(a (b c) |d e|) ; comment\n(f)")
        self.assertEqual(commands, [["a", ["b", "c"], "|d e|"], ["f"]])
        with self.assertRaises(proof_certificate.ProofExportError):
            proof_clause_log._sexpressions("(a (b)")

    @unittest.skipUnless(_z3_available(), "the z3 executable is required for the clause log")
    def test_executable_export_and_cli(self):
        certificate = proof_certificate.export_clause_log_certificate(_LRA)
        self.assertEqual(certificate["fragment"], "qf_lra")
        self.assertEqual(certificate["rule_counts"]["th-lemma"], 1)
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "sat: no unsat proof"):
            proof_certificate.export_clause_log_certificate(
                "(declare-const x Real)(assert (> x 1.0))")
        # Boolean input through the clause log, selected explicitly.
        result = subprocess.run(
            [sys.executable, str(_EXAMPLES / "proof_certificate.py"), "--core", "clause-log", "-"],
            input=_CONTRADICTION, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)["fragment"], "propositional")
        result = subprocess.run(
            [sys.executable, str(_EXAMPLES / "proof_certificate.py"), "-"],
            input=_LRA, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)["fragment"], "qf_lra")


if __name__ == "__main__":
    unittest.main()
