############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Tests for native Boolean proof certificate export.
############################################
from fractions import Fraction
import json
from pathlib import Path
import re
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


_ITE = """\
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(declare-const p Bool)
(assert (> (ite p x y) 3.0))
(assert (< x 1.0))
(assert (< y 2.0))
(check-sat)
"""
# The clause log for _ITE: the Real ite is tied to its branches by tseitin
# clauses and otherwise treated as an opaque arithmetic variable.
_ITE_LOG = """\
(declare-fun p () Bool)
(declare-fun x () Real)
(declare-fun y () Real)
(define-const $8 Real (ite p x y))
(define-const $25 Bool (= $8 x))
(declare-fun tseitin (Bool Bool) Proof)
(define-const $24 Bool (not p))
(define-const $27 Proof (tseitin $24 $25))
(infer (not p) $25 $27)
(define-const $26 Bool (= $8 y))
(define-const $28 Proof (tseitin p $26))
(infer p $26 $28)
(define-const $15 Bool (<= $8 3.0))
(assume (not $15))
(define-const $17 Bool (<= 1.0 x))
(assume (not $17))
(define-const $19 Bool (<= 2.0 y))
(assume (not $19))
(define-const $29 Bool (= y $8))
(declare-fun farkas (Int Bool Int Bool Int Bool) Proof)
(define-const $16 Bool (not $15))
(define-const $20 Bool (not $19))
(define-const $30 Proof (farkas 1 $29 1 $20 1 $16))
(infer $19 $15 (not $29) $30)
(declare-fun euf (Bool Bool) Proof)
(define-const $31 Bool (not $29))
(define-const $32 Proof (euf $31 $26))
(infer (not $26) $29 $32)
(declare-fun rup () Proof)
(infer (not $26) rup)
(infer p rup)
(infer $25 rup)
(define-const $34 Bool (= x $8))
(define-const $18 Bool (not $17))
(define-const $35 Proof (farkas 1 $34 1 $18 1 $16))
(infer $17 $15 (not $34) $35)
(define-const $36 Bool (not $34))
(define-const $37 Proof (euf $36 $25))
(infer (not $25) $34 $37)
(infer rup)
"""


_UF = """\
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun f (U) U)
(declare-fun g (U U) U)
(declare-fun p (U) Bool)
(assert (= a b))
(assert (or (not (= (f a) (f b))) (p (g a c))))
(assert (not (p (g b c))))
(check-sat)
"""
# The clause log for _UF: euf hints list jointly contradictory literals and
# carry (cc ...) congruence claims as Proof-sorted arguments.
_UF_LOG = """\
(declare-sort U 0)
(declare-fun b () U)
(declare-fun a () U)
(define-const $7 Bool (= a b))
(assume $7)
(declare-fun f (U) U)
(define-const $9 U (f b))
(define-const $8 U (f a))
(define-const $10 Bool (= $8 $9))
(declare-fun p (U) Bool)
(declare-fun g (U U) U)
(declare-fun c () U)
(define-const $13 U (g a c))
(define-const $14 Bool (p $13))
(assume (not $10) $14)
(define-const $16 U (g b c))
(define-const $17 Bool (p $16))
(assume (not $17))
(declare-fun euf (Bool Bool Proof) Proof)
(declare-fun cc (Bool) Proof)
(define-const $19 Bool (= $9 $8))
(define-const $20 Proof (cc $19))
(define-const $11 Bool (not $10))
(define-const $21 Proof (euf $11 $7 $20))
(infer (not $7) $10 $21)
(declare-fun rup () Proof)
(infer $10 rup)
(declare-fun euf (Bool Bool Bool Proof Proof) Proof)
(define-const $25 Bool (= $14 $17))
(define-const $26 Proof (cc $25))
(define-const $23 Bool (= $16 $13))
(define-const $24 Proof (cc $23))
(define-const $18 Bool (not $17))
(define-const $27 Proof (euf $14 $7 $18 $24 $26))
(infer (not $7) $17 (not $14) $27)
(infer (not $14) rup)
(infer rup)
"""

_UF_TWO_SORTS = """\
(set-logic QF_UF)
(declare-sort A 0)
(declare-sort B 0)
(declare-fun a1 () A)
(declare-fun a2 () A)
(declare-fun b () B)
(declare-fun f (A) B)
(declare-fun g (B A) A)
(declare-fun p (B) Bool)
(declare-const q Bool)
(assert (= (f a1) b))
(assert (or q (= (f a2) b)))
(assert (not q))
(assert (or (not (= (f a1) (f a2))) (p (f (g b a1)))))
(assert (not (p (f (g (f a1) a1)))))
(check-sat)
"""
# The clause log for _UF_TWO_SORTS: every sort is declared, and the functions
# between sorts are declared and applied exactly as functions over one sort.
_UF_TWO_SORTS_LOG = """\
(declare-sort B 0)
(declare-sort A 0)
(declare-fun b () B)
(declare-fun f (A) B)
(declare-fun a1 () A)
(define-const $6 B (f a1))
(define-const $8 Bool (= $6 b))
(assume $8)
(declare-fun a2 () A)
(define-const $11 B (f a2))
(define-const $12 Bool (= $11 b))
(assume $12)
(declare-fun q () Bool)
(assume (not q))
(define-const $15 Bool (= $6 $11))
(declare-fun p (B) Bool)
(declare-fun g (B A) A)
(define-const $17 A (g b a1))
(define-const $18 B (f $17))
(define-const $19 Bool (p $18))
(assume (not $15) $19)
(define-const $21 A (g $6 a1))
(define-const $22 B (f $21))
(define-const $23 Bool (p $22))
(assume (not $23))
(declare-fun euf (Bool Bool Bool Proof) Proof)
(declare-fun comm (Bool) Proof)
(define-const $27 Bool (= $15 $12))
(define-const $25 Proof (comm $27))
(define-const $16 Bool (not $15))
(define-const $28 Proof (euf $16 $8 $12 $25))
(infer (not $8) (not $12) $15 $28)
(declare-fun rup () Proof)
(infer $15 rup)
(declare-fun euf (Bool Bool Bool Proof Proof Proof) Proof)
(declare-fun cc (Bool) Proof)
(define-const $34 Bool (= $19 $23))
(define-const $35 Proof (cc $34))
(define-const $32 Bool (= $22 $18))
(define-const $33 Proof (cc $32))
(define-const $30 Bool (= $17 $21))
(define-const $31 Proof (cc $30))
(define-const $24 Bool (not $23))
(define-const $36 Proof (euf $19 $8 $24 $31 $33 $35))
(infer (not $8) $23 (not $19) $36)
(infer (not $19) rup)
(infer rup)
"""

_UF_ITE = """\
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-const p Bool)
(assert (= c (ite p a b)))
(assert (not (= (f c) (f a))))
(assert (not (= (f c) (f b))))
(check-sat)
"""
# The clause log for _UF_ITE: the ite over the sort is tied to its branches
# by tseitin clauses, exactly as a Real ite, and is otherwise an opaque element.
_UF_ITE_LOG = """\
(declare-fun p () Bool)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(define-const $9 U (ite p a b))
(define-const $19 Bool (= $9 a))
(declare-fun tseitin (Bool Bool) Proof)
(define-const $18 Bool (not p))
(define-const $21 Proof (tseitin $18 $19))
(infer (not p) $19 $21)
(define-const $20 Bool (= $9 b))
(define-const $22 Proof (tseitin p $20))
(infer p $20 $22)
(declare-fun c () U)
(define-const $10 Bool (= c $9))
(assume $10)
(declare-fun f (U) U)
(define-const $12 U (f a))
(define-const $11 U (f c))
(define-const $13 Bool (= $11 $12))
(assume (not $13))
(define-const $15 U (f b))
(define-const $16 Bool (= $11 $15))
(assume (not $16))
(declare-fun euf (Bool Bool Bool Proof) Proof)
(declare-fun cc (Bool) Proof)
(define-const $23 Proof (cc $16))
(define-const $17 Bool (not $16))
(define-const $24 Proof (euf $17 $10 $20 $23))
(infer (not $10) (not $20) $16 $24)
(declare-fun rup () Proof)
(infer (not $20) $16 rup)
(infer (not $20) rup)
(infer p rup)
(infer $19 rup)
(define-const $26 Proof (cc $13))
(define-const $14 Bool (not $13))
(define-const $27 Proof (euf $14 $10 $19 $26))
(infer (not $10) (not $19) $13 $27)
(infer $13 rup)
(infer rup)
"""

_UF_ITE_ALLDIFF = """\
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun g (U U) U)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-const q Bool)
(assert q)
(assert (= c a))
(assert (distinct (g c a) (ite (not q) b a) c))
(check-sat)
"""
# The clause log for _UF_ITE_ALLDIFF: Z3 internalizes the distinct after q is
# asserted, so its alldiff clauses mention a where the input has the ite, and
# the last one is the empty clause because (= c a) is already asserted.
_UF_ITE_ALLDIFF_LOG = """\
(declare-fun q () Bool)
(assume q)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun c () U)
(define-const $8 Bool (= c a))
(assume $8)
(declare-fun g (U U) U)
(define-const $9 U (g c a))
(define-const $22 Bool (= $9 a))
(declare-fun alldiff (Bool) Proof)
(define-const $17 Bool (not $22))
(define-const $20 Proof (alldiff $17))
(infer (not $22) $20)
(define-const $24 Bool (= $9 c))
(define-const $23 Bool (not $24))
(define-const $25 Proof (alldiff $23))
(infer (not $24) $25)
(define-const $26 Bool (not $8))
(define-const $27 Proof (alldiff $26))
(infer $27)
(declare-fun rup () Proof)
(infer rup)
"""

_UF_BOOL_ARGS = """\
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun f (Bool) U)
(declare-const q Bool)
(declare-const r Bool)
(declare-const s Bool)
(assert q)
(assert (= (f q) a))
(assert (or s r))
(assert (or (not s) r))
(assert (not (= (f r) a)))
(check-sat)
"""
# The clause log for _UF_BOOL_ARGS: with q asserted, Z3 internalizes (f q) as
# (f true) and assumes the true literal itself; r is decided during search and
# the euf hint lists it as a premise of the congruence (f r) = (f true).
_UF_BOOL_ARGS_LOG = """\
(declare-fun q () Bool)
(assume q)
(assume true)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun f (Bool) U)
(define-const $18 U (f true))
(define-const $19 Bool (= $18 a))
(assume $19)
(declare-fun s () Bool)
(declare-fun r () Bool)
(assume s r)
(assume (not s) r)
(define-const $14 U (f r))
(define-const $15 Bool (= $14 a))
(assume (not $15))
(declare-fun rup () Proof)
(infer r rup)
(declare-fun euf (Bool Bool Bool Proof Proof) Proof)
(declare-fun cc (Bool) Proof)
(define-const $23 Bool (= $19 $15))
(define-const $24 Proof (cc $23))
(define-const $21 Bool (= $14 $18))
(define-const $22 Proof (cc $21))
(define-const $16 Bool (not $15))
(define-const $25 Proof (euf $19 $16 r $22 $24))
(infer (not $19) $15 (not r) $25)
(infer rup)
"""

_UF_NEGATIVE_UNIT = """\
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun p (U) Bool)
(declare-const s Bool)
(assert (or s (p a)))
(assert (not s))
(assert (= a b))
(assert (not (p b)))
(check-sat)
"""
# The clause log for _UF_NEGATIVE_UNIT: the negated unit makes the sat core
# log its internal true literal, a Boolean variable without an expression,
# as the fresh constant k!0; the clause assuming it is used by nothing. The
# input carries no set-logic line: with (set-logic QF_UF) the same
# assertions are logged without the phantom.
_UF_NEGATIVE_UNIT_LOG = """\
(declare-sort U 0)
(declare-fun p (U) Bool)
(declare-fun a () U)
(define-const $7 Bool (p a))
(assume $7)
(declare-fun k!0 () Bool)
(assume k!0)
(declare-fun b () U)
(define-const $11 Bool (= a b))
(assume $11)
(define-const $12 Bool (p b))
(assume (not $12))
(declare-fun euf (Bool Bool Bool Proof) Proof)
(declare-fun cc (Bool) Proof)
(define-const $16 Bool (= $12 $7))
(define-const $17 Proof (cc $16))
(define-const $13 Bool (not $12))
(define-const $18 Proof (euf $13 $7 $11 $17))
(infer $12 (not $7) (not $11) $18)
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
        # A Real ite with linear branches is a linear term; the condition may be any formula.
        ite = ("(declare-const p Bool)(declare-const x Real)"
               "(assert (> (* 2.0 (ite (and p (< x 1.0)) x (ite p 1.0 (- x)))) 2.0))")
        self.assertEqual(self.classify(ite), "qf_lra")

    def test_nonlinear_integer_and_other_inputs_are_rejected(self):
        for source, message in [
            ("(declare-const x Real)(assert (> (* x x) 1.0))", "nonlinear"),
            ("(declare-const x Real)(declare-const y Real)(assert (> (/ x y) 1.0))", "division"),
            ("(declare-const x Int)(assert (> x 1))", "unsupported sort"),
            ("(declare-fun f (Real) Real)(declare-const x Real)(assert (> (f x) 1.0))", "uninterpreted functions"),
            ("(declare-const p Bool)(declare-const x Real)(assert (> (* x (ite p x 1.0)) 2.0))", "nonlinear"),
            ("(declare-const p Bool)(declare-const x Real)(assert (> (/ 1.0 (ite p x 1.0)) 2.0))", "division"),
        ]:
            with self.subTest(source=source):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, message):
                    self.classify(source)

    def test_uninterpreted_function_inputs_are_classified(self):
        self.assertEqual(self.classify(_UF), "qf_uf")
        # (declare-sort U) without an arity, chained equality, and distinct over the sort.
        chained = ("(declare-sort U)(declare-fun b (U U) U)(declare-fun c () U)(declare-fun d () U)"
                   "(declare-fun e () U)(assert (= e d (b e c)))(assert (distinct e (b d c)))")
        self.assertEqual(self.classify(chained), "qf_uf")
        # A declared sort that no assertion uses does not change the fragment.
        self.assertEqual(self.classify("(declare-sort U 0)(declare-const p Bool)(assert p)"), "propositional")
        # An ite over the sort, nested and under any supported condition, stays in the fragment;
        # an ite is also enough to use the sort.
        ite = ("(declare-sort U 0)(declare-fun a () U)(declare-fun f (U) U)(declare-fun p (U) Bool)"
               "(declare-const q Bool)(assert (not (= (ite (and q (p a)) (f a) (ite (= a (f a)) a (f (f a)))) a)))")
        self.assertEqual(self.classify(ite), "qf_uf")
        self.assertEqual(self.classify("(declare-sort U 0)(declare-fun a () U)(declare-const q Bool)"
                                       "(assert (not (= (ite q a a) a)))"), "qf_uf")
        # Several uninterpreted sorts, with functions between them, predicates
        # over several of them, and ite over each, are one fragment.
        declarations = "(declare-sort U 0)(declare-sort V 0)(declare-fun a () U)(declare-fun v () V)"
        for source in [
            declarations + "(assert (and (= a a) (= v v)))",
            declarations + "(declare-fun h (U) V)(assert (= (h a) v))",
            declarations + "(declare-fun h (V U) U)(declare-fun r (U V) Bool)(assert (and (= (h v a) a) (r a v)))",
            declarations + "(declare-const p Bool)(assert (and (= a a) (= (ite p v v) v)))",
        ]:
            with self.subTest(source=source):
                self.assertEqual(self.classify(source), "qf_uf")
        # Functions and predicates may take Bool arguments, including formulas,
        # once the input uses a sort; a Bool-only signature is not enough.
        for source in [
            declarations + "(declare-fun h (Bool) U)(assert (= (h true) a))",
            declarations + "(declare-fun h (U Bool) V)(declare-fun r (Bool) Bool)"
                           "(assert (= (h a (r (= v v))) v))",
            declarations + "(declare-fun r (Bool Bool) Bool)(declare-const p Bool)(assert (and (= a a) (r p (not p))))",
        ]:
            with self.subTest(source=source):
                self.assertEqual(self.classify(source), "qf_uf")
        for source, message in [
            (declarations + "(declare-const x Real)(assert (and (= a a) (> x 1.0)))", "mixing uninterpreted sorts"),
            ("(declare-fun r (Bool) Bool)(declare-const p Bool)(assert (r p))", "over Bool alone"),
            ("(declare-sort U 0)(declare-fun r (Bool Bool) Bool)(declare-const p Bool)(assert (r p p))",
             "over Bool alone"),
            (declarations + "(declare-fun h (U) V)(declare-const x Real)(assert (and (= (h a) v) (> x 1.0)))",
             "mixing uninterpreted sorts"),
            (declarations + "(declare-fun h (U) Real)(assert (> (h a) 1.0))", "uninterpreted functions"),
            (declarations + "(declare-fun r (Bool Real) Bool)(assert (r true 1.0))", "functions over Real"),
            (declarations + "(declare-fun q (Real) Bool)(assert (q 1.0))", "functions over Real"),
            ("(declare-sort W 1)(declare-fun w () (W Bool))(assert (= w w))", "arity 0"),
            # Z3 accepts one name declared with several signatures and tells the
            # declarations apart by sort; the certificate binds symbols by name.
            (declarations + "(declare-fun a () V)(declare-fun h (U) V)(assert (= (h (as a U)) (as a V)))",
             "several signatures: a"),
            (declarations + "(declare-fun r (U) Bool)(declare-fun r (V) Bool)(assert (and (r a) (r v)))",
             "several signatures: r"),
            ("(declare-sort U 0)(declare-fun a () U)(declare-fun f (U) U)(declare-fun f (U U) U)"
             "(assert (= (f a) (f a a)))", "several signatures: f"),
            ("(declare-const x Bool)(declare-const x Real)(assert (and (as x Bool) (> (as x Real) 1.0)))",
             "several signatures: x"),
        ]:
            with self.subTest(source=source):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, message):
                    self.classify(source)

    def test_legacy_exporter_still_rejects_arithmetic(self):
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "clause-log"):
            proof_certificate.export_certificate(_LRA)
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "clause-log.*qf_uf"):
            proof_certificate.export_certificate(_UF)


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

    def test_euf_congruence_annotations_are_not_assumptions(self):
        source = ("(declare-const x Real)(declare-const y Real)"
                  "(assert (= x y))(assert (<= x 0.0))(assert (not (<= y 0.0)))")
        log = """\
(declare-fun x () Real)
(declare-fun y () Real)
(define-const $1 Bool (= x y))
(define-const $2 Bool (<= x 0.0))
(define-const $3 Bool (<= y 0.0))
(define-const $4 Proof (cc (= $2 $3)))
(assume $1)
(assume $2)
(assume (not $3))
(define-const $5 Proof (euf $1 $2 (not $3) $4))
(infer (not $1) (not $2) $3 $5)
(infer rup)
"""
        for name in ("cc", "comm"):
            with self.subTest(annotation=name):
                certificate = self.replay(source, log.replace("(cc ", "(%s " % name))
                hints = [d["parameters"] for d in certificate["declarations"] if d["name"] == "th-lemma"]
                self.assertEqual(hints, [["euf"]])
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "malformed euf congruence"):
            self.replay(source, log.replace("(cc (= $2 $3))", "(cc true)"))

    def test_assumption_index_normalizes_boolean_constants_without_search(self):
        source = ("(declare-const x Real)"
                  "(assert (and true (or false (<= (+ (* 1.0 x) 0.0) 1.0))))")
        context = z3.Context()
        assertions, fragment = proof_certificate.parse_assertions(source, context)
        replay = proof_clause_log._Replay(source, fragment, assertions, context)
        x = z3.Real("x", context)
        with patch.object(replay, "_valid", side_effect=AssertionError("unnecessary solver search")):
            replay.assume([x <= 1])
            index = replay.assumptions_by_key
            cache_size = len(replay.normalizer.cache)
            replay.assume([x <= 1])
        self.assertIs(replay.assumptions_by_key, index)
        self.assertEqual(len(replay.normalizer.cache), cache_size)

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

    def test_real_ite_terms_are_opaque_in_hints_and_get_gate_clauses(self):
        certificate = self.replay(_ITE, _ITE_LOG)
        counts = certificate["rule_counts"]
        self.assertEqual(counts["th-lemma"], 4)  # two farkas and two euf hints
        self.assertEqual(counts["def-axiom"], 2)  # the two ite gate clauses
        ite = [d for d in certificate["declarations"] if d["kind"] == z3.Z3_OP_ITE]
        self.assertEqual([(d["name"], d["domain"], d["range"]) for d in ite], [("if", ["Bool", "Real", "Real"], "Real")])
        # A combination that refutes only if the ite were replaced by a branch is not a Farkas proof.
        log = _ITE_LOG.replace("(farkas 1 $29 1 $20 1 $16)", "(farkas 1 $20 1 $16)")
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "do not refute"):
            self.replay(_ITE, log)
        # The log's ite must be built from declared symbols like any other term.
        log = _ITE_LOG.replace("(ite p x y)", "(ite q x y)")
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "undeclared or fresh symbol"):
            self.replay(_ITE, log)

    def test_congruence_claims_in_euf_hints_are_not_literals(self):
        # Z3 guides its own checker with (cc (= a b)) or (comm (= a b)) proof
        # arguments; the lemma clause consists of the Boolean arguments only.
        claim = ("(declare-fun cc (Bool) Proof)\n(define-const $40 Bool (= $29 $26))\n"
                 "(define-const $41 Proof (cc $40))\n")
        log = _ITE_LOG.replace("(define-const $32 Proof (euf $31 $26))",
                               claim + "(define-const $32 Proof (euf $31 $26 $41 (comm (= $29 $26))))")
        certificate = self.replay(_ITE, log)
        self.assertEqual(certificate["rule_counts"], self.replay(_ITE, _ITE_LOG)["rule_counts"])
        for broken in ["(cc $15)", "(cc $40 $40)", "(cc)"]:
            with self.subTest(broken=broken):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, "malformed euf congruence"):
                    self.replay(_ITE, log.replace("(cc $40)", broken))
        # Only euf hints carry claims; in any other literal hint they are not literals either.
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "undeclared or fresh symbol"):
            self.replay(_ITE, log.replace("(tseitin $24 $25)", "(tseitin $24 $25 $41)"))

    def test_uninterpreted_functions_in_the_clause_log(self):
        certificate = self.replay(_UF, _UF_LOG)
        self.assertEqual(certificate["fragment"], "qf_uf")
        counts = certificate["rule_counts"]
        self.assertEqual(counts["th-lemma"], 2)  # the two euf hints, their cc claims dropped
        self.assertEqual(counts["asserted"], 3)
        self.assertNotIn("def-axiom", counts)
        signatures = {(d["name"], tuple(d["domain"]), d["range"]) for d in certificate["declarations"]
                      if d["kind"] == z3.Z3_OP_UNINTERPRETED}
        self.assertEqual(signatures, {("a", (), "U"), ("b", (), "U"), ("c", (), "U"), ("f", ("U",), "U"),
                                      ("g", ("U", "U"), "U"), ("p", ("U",), "Bool")})
        self.assertEqual({d["range"] for d in certificate["declarations"]}, {"Bool", "U", "Proof"})
        equality = [d for d in certificate["declarations"] if d["kind"] == z3.Z3_OP_EQ]
        self.assertEqual([tuple(d["domain"]) for d in equality], [("U", "U")])
        for log, message in [
            (_UF_LOG.replace("(declare-fun f (U) U)", "(declare-fun h (U) U)"), "absent from the input"),
            (_UF_LOG.replace("(declare-fun f (U) U)", "(declare-fun f (U U) U)"), "absent from the input"),
            (_UF_LOG.replace("(declare-fun f (U) U)", "(declare-fun f U U)"), "malformed declaration"),
            (_UF_LOG.replace("(declare-sort U 0)", "(declare-sort V 0)"), "sort absent from the input"),
            (_UF_LOG.replace("(declare-sort U 0)", "(declare-sort U 1)"), "malformed sort declaration"),
            (_UF_LOG.replace("(f b)", "(f b a)"), "wrong number of arguments"),
            (_UF_LOG.replace("(g b c)", "(g b $7)"), "ill-sorted application"),
            (_UF_LOG.replace("(g b c)", "(h b c)"), "unsupported operator in the clause log"),
            (_UF_LOG.replace("(define-const $9 U (f b))", "(define-const $9 Bool (f b))"), "has sort U, declared Bool"),
        ]:
            with self.subTest(message=message):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, message):
                    self.replay(_UF, log)
        # The log quotes a sort name the way it quotes symbols; the certificate keeps the bare name.
        quoted = self.replay(re.sub(r"\bU\b", "|my sort|", _UF), re.sub(r"\bU\b", "|my sort|", _UF_LOG))
        self.assertEqual({d["range"] for d in quoted["declarations"]}, {"Bool", "my sort", "Proof"})
        self.assertEqual(quoted["rule_counts"], certificate["rule_counts"])

    def test_several_uninterpreted_sorts_in_the_clause_log(self):
        certificate = self.replay(_UF_TWO_SORTS, _UF_TWO_SORTS_LOG)
        self.assertEqual(certificate["fragment"], "qf_uf")
        # Two euf hints, plus a cnf lemma: Z3 assumed (= (f a2) b) with q already false.
        self.assertEqual(certificate["rule_counts"]["th-lemma"], 3)
        self.assertEqual({tuple(d["parameters"]) for d in certificate["declarations"] if d["name"] == "th-lemma"},
                         {("euf",), ("cnf",)})
        # The certificate keeps every sort name: declarations stay many-sorted.
        signatures = {(d["name"], tuple(d["domain"]), d["range"]) for d in certificate["declarations"]
                      if d["kind"] == z3.Z3_OP_UNINTERPRETED}
        self.assertEqual(signatures, {("a1", (), "A"), ("a2", (), "A"), ("b", (), "B"), ("f", ("A",), "B"),
                                      ("g", ("B", "A"), "A"), ("p", ("B",), "Bool"), ("q", (), "Bool")})
        self.assertEqual({d["range"] for d in certificate["declarations"]}, {"Bool", "A", "B", "Proof"})
        self.assertEqual({tuple(d["domain"]) for d in certificate["declarations"] if d["kind"] == z3.Z3_OP_EQ},
                         {("B", "B")})
        for log, message in [
            (_UF_TWO_SORTS_LOG.replace("(declare-sort A 0)", "(declare-sort C 0)"), "sort absent from the input"),
            (_UF_TWO_SORTS_LOG.replace("(f a1)", "(f b)"), "ill-sorted application"),
            (_UF_TWO_SORTS_LOG.replace("(g b a1)", "(g a1 b)"), "ill-sorted application"),
            (_UF_TWO_SORTS_LOG.replace("(define-const $6 B (f a1))", "(define-const $6 A (f a1))"),
             "has sort B, declared A"),
            (_UF_TWO_SORTS_LOG.replace("(= $6 b)", "(= $6 a1)"), "ill-sorted application"),
        ]:
            with self.subTest(message=message):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, message):
                    self.replay(_UF_TWO_SORTS, log)

    def test_ite_over_the_uninterpreted_sort_in_the_clause_log(self):
        certificate = self.replay(_UF_ITE, _UF_ITE_LOG)
        self.assertEqual(certificate["fragment"], "qf_uf")
        counts = certificate["rule_counts"]
        self.assertEqual(counts["def-axiom"], 2)  # the two ite gate clauses
        self.assertEqual(counts["th-lemma"], 2)   # the two euf hints
        ite = [d for d in certificate["declarations"] if d["kind"] == z3.Z3_OP_ITE]
        self.assertEqual([(d["name"], d["domain"], d["range"]) for d in ite], [("if", ["Bool", "U", "U"], "U")])
        self.assertEqual({d["range"] for d in certificate["declarations"]}, {"Bool", "U", "Proof"})
        # The gate clauses are def-axiom nodes, not assumptions and not theory lemmas, so
        # a log that never records them still replays: rup steps find them as gates.
        trimmed = _UF_ITE_LOG.replace("(infer (not p) $19 $21)\n", "").replace("(infer p $20 $22)\n", "")
        self.assertEqual(self.replay(_UF_ITE, trimmed)["rule_counts"], counts)
        # The log's ite must be built from declared symbols with the input's sort.
        for log, message in [
            (_UF_ITE_LOG.replace("(ite p a b)", "(ite q a b)"), "undeclared or fresh symbol"),
            (_UF_ITE_LOG.replace("(ite p a b)", "(ite a a b)"), "ill-sorted application of ite"),
            (_UF_ITE_LOG.replace("(ite p a b)", "(ite p a p)"), "ill-sorted application of ite"),
            (_UF_ITE_LOG.replace("(define-const $9 U (ite p a b))", "(define-const $9 Bool (ite p a b))"),
             "has sort U, declared Bool"),
        ]:
            with self.subTest(message=message):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, message):
                    self.replay(_UF_ITE, log)

    def test_boolean_arguments_in_the_clause_log(self):
        certificate = self.replay(_UF_BOOL_ARGS, _UF_BOOL_ARGS_LOG)
        self.assertEqual(certificate["fragment"], "qf_uf")
        counts = certificate["rule_counts"]
        self.assertEqual(counts["asserted"], 5)
        self.assertEqual(counts["def-axiom"], 1)  # (assume true) is a tautology
        f = [d for d in certificate["declarations"] if d["name"] == "f" and d["kind"] == z3.Z3_OP_UNINTERPRETED]
        self.assertEqual([(d["domain"], d["range"]) for d in f], [(["Bool"], "U")])
        # (= (f true) a) is not an assertion: it is (= (f q) a) under the unit q,
        # tied to both by a cnf lemma; the euf hint becomes the other th-lemma.
        self.assertEqual(sorted(tuple(d["parameters"]) for d in certificate["declarations"] if d["name"] == "th-lemma"),
                         [("cnf",), ("euf",)])
        self.assertEqual(counts["th-lemma"], 2)
        # Without the tautological unit the certificate only loses the def-axiom.
        trimmed = self.replay(_UF_BOOL_ARGS, _UF_BOOL_ARGS_LOG.replace("(assume true)\n", ""))
        self.assertEqual(trimmed["rule_counts"], {k: v for k, v in counts.items() if k != "def-axiom"})
        for log, message in [
            (_UF_BOOL_ARGS_LOG.replace("(f true)", "(f a)"), "ill-sorted application of f"),
            (_UF_BOOL_ARGS_LOG.replace("(f r)", "(f r r)"), "wrong number of arguments"),
            (_UF_BOOL_ARGS_LOG.replace("(define-const $14 U (f r))", "(define-const $14 Bool (f r))"),
             "has sort U, declared Bool"),
        ]:
            with self.subTest(message=message):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, message):
                    self.replay(_UF_BOOL_ARGS, log)

    def test_phantom_literals_of_the_sat_core_are_dropped(self):
        certificate = self.replay(_UF_NEGATIVE_UNIT, _UF_NEGATIVE_UNIT_LOG)
        self.assertEqual(certificate["rule_counts"]["asserted"], 4)
        self.assertEqual(certificate["rule_counts"]["th-lemma"], 2)  # euf, and cnf for (p a) under (not s)
        self.assertFalse([d for d in certificate["declarations"] if d["name"].startswith("k!")])
        # Only nullary Bool constants named k!<n> are phantoms, and only in
        # assumed or deleted clauses: an inference over one is rejected.
        for log, message in [
            (_UF_NEGATIVE_UNIT_LOG.replace("(infer rup)", "(infer k!0 rup)\n(infer rup)"), "undeclared or fresh symbol"),
            (_UF_NEGATIVE_UNIT_LOG.replace("(define-const $7 Bool (p a))", "(define-const $7 Bool (and k!0 (p a)))"),
             "undeclared or fresh symbol"),
            (_UF_NEGATIVE_UNIT_LOG.replace("(declare-fun k!0 () Bool)", "(declare-fun k!0 () U)"),
             "absent from the input"),
            (_UF_NEGATIVE_UNIT_LOG.replace("(declare-fun k!0 () Bool)", "(declare-fun k!0 (Bool) Bool)"),
             "absent from the input"),
            (_UF_NEGATIVE_UNIT_LOG.replace("k!0", "j!0"), "absent from the input"),
            (_UF_NEGATIVE_UNIT_LOG.replace("(assume k!0)", "(assume (not k!0))"), None),
            (_UF_NEGATIVE_UNIT_LOG.replace("(assume k!0)", "(assume k!0 $7)\n(del k!0 $7)"), None),
        ]:
            with self.subTest(message=message, log=log):
                if message is None:
                    self.assertEqual(self.replay(_UF_NEGATIVE_UNIT, log)["rule_counts"], certificate["rule_counts"])
                else:
                    with self.assertRaisesRegex(proof_certificate.ProofExportError, message):
                        self.replay(_UF_NEGATIVE_UNIT, log)

    def test_alldiff_clauses_simplified_under_a_unit_are_tied_to_their_sources(self):
        certificate = self.replay(_UF_ITE_ALLDIFF, _UF_ITE_ALLDIFF_LOG)
        declarations = certificate["declarations"]
        hints = [tuple(d["parameters"]) for d in declarations if d["name"] == "th-lemma"]
        self.assertEqual(set(hints), {("cnf",)})
        self.assertEqual(certificate["rule_counts"]["asserted"], 3)
        self.assertNotIn("def-axiom", certificate["rule_counts"])
        # Each cnf lemma negates an unsat core of the assertions, not all of them:
        # (not (= (g c a) a)) follows from the distinct and q alone.
        nodes = certificate["nodes"]
        for index, node in enumerate(nodes):
            if declarations[node["declaration"]]["name"] == "th-lemma":
                clause = nodes[node["arguments"][0]]
                literals = clause["arguments"] if declarations[clause["declaration"]]["name"] == "or" else [clause]
                self.assertLessEqual(len(literals), 3, "cnf lemma %d over all assertions" % index)
        # The empty alldiff clause's literal (not (= c a)) is the negation of an
        # assertion; it stays a literal of the lemma instead of being resolved away.
        empty = [index for index, node in enumerate(nodes)
                 if declarations[node["declaration"]]["name"] == "unit-resolution"
                 and declarations[nodes[node["arguments"][-1]]["declaration"]]["name"] == "false"]
        self.assertTrue(empty)
        # Without q the input is satisfiable and no assertion subset implies the
        # empty clause's literal, so the replay rejects the log instead of guessing.
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "does not match any original assertion"):
            self.replay(_UF_ITE_ALLDIFF.replace("(assert q)\n", ""), _UF_ITE_ALLDIFF_LOG.replace("(assume q)\n", ""))
        # A core check cut off by the resource limit is reported as such, not as a mismatch.
        with patch.object(proof_clause_log, "_RLIMIT", 1):
            with self.assertRaisesRegex(proof_certificate.ProofExportError, "resource limit reached"):
                self.replay(_UF_ITE_ALLDIFF, _UF_ITE_ALLDIFF_LOG)

    def test_deleted_and_repeated_empty_clauses_are_handled(self):
        log = _LRA_LOG.replace("(infer rup)\n", "(del (not $11) (not $17) (not $21))\n(infer rup)\n(infer rup)\n")
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "not derivable"):
            self.replay(_LRA, log)
        log = _LRA_LOG + "(infer rup)\n"
        certificate = self.replay(_LRA, log)
        self.assertEqual(certificate["rule_counts"]["lemma"], 2)

    def test_implied_equality_hints_end_in_a_disequality(self):
        source = ("(declare-const x Real)(declare-const y Real)"
                  "(assert (<= x y))(assert (>= x y))(assert (not (= x y)))")
        log = """\
(declare-fun x () Real)
(declare-fun y () Real)
(define-const $1 Bool (<= x y))
(define-const $2 Bool (>= x y))
(define-const $3 Bool (= x y))
(assume $1)
(assume $2)
(assume (not $3))
(define-const $4 Proof (implied-eq 1 $1 1 $2 1 (not $3)))
(infer (not $1) (not $2) $3 $4)
(infer rup)
"""
        certificate = self.replay(source, log)
        hints = [d["parameters"] for d in certificate["declarations"] if d["name"] == "th-lemma"]
        self.assertEqual(hints, [["implied-eq", "1", "1", "1"]])
        malformed = log.replace("(implied-eq 1 $1 1 $2 1 (not $3))", "(implied-eq 1 $1 1 $2 1 $3)")
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "must end in a Real disequality"):
            self.replay(source, malformed)

    def test_alldiff_clauses_are_bound_to_original_assertions(self):
        declarations = "(declare-const x Real)(declare-const y Real)(declare-const z Real)"
        source = declarations + "(assert (distinct x y z))(assert (= x y))"
        log = """\
(declare-fun x () Real)
(declare-fun y () Real)
(define-const $1 Bool (= x y))
(define-const $2 Proof (alldiff (not $1)))
(infer (not $1) $2)
(assume $1)
(infer rup)
"""
        certificate = self.replay(source, log)
        hints = [d["parameters"] for d in certificate["declarations"] if d["name"] == "th-lemma"]
        self.assertEqual(hints, [["cnf"]])
        self.assertNotIn("def-axiom", certificate["rule_counts"])
        unrelated = declarations + "(assert (= x y))(assert (>= z 0.0))"
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "does not match any original"):
            self.replay(unrelated, log)

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
        # A negated unit makes the sat core log its internal true variable as
        # the phantom k!0; the raw log shows it and the certificate does not.
        log = proof_clause_log.run_clause_log(proof_certificate.default_z3_executable(),
                                              proof_certificate._assertion_commands(_UF_NEGATIVE_UNIT))
        self.assertIn("(declare-fun k!0 () Bool)", log)
        certificate = proof_certificate.export_clause_log_certificate(_UF_NEGATIVE_UNIT)
        self.assertEqual(certificate["fragment"], "qf_uf")
        self.assertNotIn("k!", json.dumps(certificate))
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


_DEPENDENCY_LOG = """\
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun rup () Proof)
(define-const d0 Proof (deps 0))
(define-const d1 Proof (deps 1))
(define-const d2 Proof (deps 2))
(define-const d3 Proof (deps 3 4))
(define-const d4 Proof (deps 4 0 1))
(define-const d5 Proof (deps 5 3))
(assume p d0)
(assume (not p) d1)
(assume q d2)
(infer rup d3)
(infer rup d4)
(infer rup d5)
"""


class TestClauseLogDependencies(unittest.TestCase):
    def test_dependency_core_orders_forward_references_and_keeps_assertion_roots(self):
        core = proof_clause_log._dependency_core(_DEPENDENCY_LOG)
        self.assertNotIn("(assume q", core)
        self.assertLess(core.index("(infer rup d4)"), core.index("(infer rup d3)"))
        source = "(declare-const p Bool)(declare-const q Bool)(assert p)(assert (not p))(assert q)"
        context = z3.Context()
        assertions, fragment = proof_certificate.parse_assertions(source, context)
        certificate = proof_clause_log.build_certificate(source, fragment, assertions, core, context)
        self.assertEqual(len(certificate["assertions"]), 3)
        reachable, pending = set(), certificate["assertions"] + [certificate["proof"]]
        while pending:
            node = pending.pop()
            if node not in reachable:
                reachable.add(node)
                pending.extend(certificate["nodes"][node]["arguments"])
        self.assertEqual(len(reachable), len(certificate["nodes"]))

    def test_invalid_dependency_graphs_are_rejected(self):
        for bad, message in [
            (_DEPENDENCY_LOG.replace("(deps 4 0 1)", "(deps 4 3)"), "cyclic"),
            (_DEPENDENCY_LOG.replace("(deps 4 0 1)", "(deps 4 99)"), "undefined clause"),
            (_DEPENDENCY_LOG.replace("(deps 4 0 1)", "(deps 4 -1)"), "malformed"),
            (_DEPENDENCY_LOG.replace("(deps 4 0 1)", "(deps 0)"), "duplicate"),
            (_DEPENDENCY_LOG.replace("(infer rup d5)", "(infer p rup d5)"), "final empty"),
        ]:
            with self.subTest(message=message):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, message):
                    proof_clause_log._dependency_core(bad)

    def test_dependencies_do_not_authorize_invalid_rup(self):
        log = _DEPENDENCY_LOG.replace("(assume (not p) d1)", "(assume q d1)")
        source = "(declare-const p Bool)(declare-const q Bool)(assert p)(assert q)"
        context = z3.Context()
        assertions, fragment = proof_certificate.parse_assertions(source, context)
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "not derivable"):
            proof_clause_log.build_certificate(source, fragment, assertions,
                                                proof_clause_log._dependency_core(log), context)

    def test_small_logs_do_not_invoke_native_trimming(self):
        with patch.object(proof_clause_log.subprocess, "run", side_effect=AssertionError("native trimming")):
            self.assertEqual(proof_clause_log.trim_clause_log("unused", _LRA_LOG), _LRA_LOG)

    def test_trimming_errors_and_diagnostics_are_visible(self):
        with patch.object(proof_clause_log, "_TRIM_THRESHOLD", 0):
            failed = subprocess.CompletedProcess([], 1, "", "trimmer failed")
            with patch.object(proof_clause_log.subprocess, "run", return_value=failed):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, "trimmer failed"):
                    proof_clause_log.trim_clause_log("unused", _LRA_LOG)
            warned = subprocess.CompletedProcess([], 0, _DEPENDENCY_LOG, "diagnostic")
            with patch.object(proof_clause_log.subprocess, "run", return_value=warned):
                with self.assertWarnsRegex(RuntimeWarning, "diagnostic"):
                    proof_clause_log.trim_clause_log("unused", _LRA_LOG)

    @unittest.skipUnless(_z3_available(), "the z3 executable is required for proof trimming")
    def test_native_trimmed_certificate_replays(self):
        with patch.object(proof_clause_log, "_TRIM_THRESHOLD", 0):
            certificate = proof_certificate.export_clause_log_certificate(_LRA)
        self.assertEqual(certificate["fragment"], "qf_lra")
        self.assertEqual(len(certificate["assertions"]), 4)


if __name__ == "__main__":
    unittest.main()
