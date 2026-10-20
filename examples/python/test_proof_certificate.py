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
# Front matter and queries that configure Z3's output, models, and search
# without changing the assertions, in the shapes z3test's regressions use
# (3220.smt2, core.smt2, strategy-par-or-2.smt2): a tactic in check-sat-using,
# a named assertion for the unsat core, and output queries after the check.
_CONFIGURED = """\
(set-logic QF_UF)
(set-option :print-success false)
(set-option :produce-models true)
(set-option :produce-unsat-cores true)
(set-option :produce-proofs false)
(set-option :proof true)
(set-option :model_validate true)
(set-option :model.compact true)
(set-option :pp.max-depth 100)
(set-option :auto-config true)
(set-option :smt.arith.solver 2)
(set-option :smt.phase-selection 3)
(set-option :smt.random_seed 7)
(set-option :sat.local_search true)
(set-option :timeout 10000)
(get-info :version)
(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (! (and (xor a b) a) :named left))
(assert b)
(check-sat-using (par-or (then simplify smt) smt))
(get-model)
(get-unsat-core)
(echo "done")
(get-option :produce-models)
(exit)
"""
# An incremental script in the shapes z3test's regressions use (incsat.smt2,
# t143.smt2, unsatcore.smt2, 3732.smt2): push and pop with counts, scoped
# declarations, assumptions as a check-sat-assuming list and as Z3's
# check-sat arguments, reset-assertions, and reset. Queries 1, 2, 3, and 5
# are unsat; 0 and 4 are sat.
_INCREMENTAL = """\
(set-logic QF_UF)
(declare-const p Bool)
(declare-const q Bool)
(assert (or p q))
(push)
(declare-const r Bool)
(assert (not p))
(assert (=> q r))
(check-sat)
(push 2)
(assert (not r))
(check-sat)
(get-model)
(pop 2)
(check-sat-assuming ((not r) (not q)))
(get-proof)
(pop)
(check-sat (not p) (not q))
(get-proof)
(reset-assertions)
(check-sat)
(assert (not p))
(reset)
(declare-const p Bool)
(assert p)
(assert (not p))
(check-sat)
(get-proof)
(exit)
"""


def _proof_nodes(proof):
    """Every proof step reachable from a native proof object."""
    seen, pending, nodes = set(), [proof], []
    while pending:
        node = pending.pop()
        if node.get_id() in seen:
            continue
        seen.add(node.get_id())
        if z3.is_app(node) and node.sort().eq(proof.sort()):
            nodes.append(node)
            pending.extend(node.children())
    return nodes


class _FakeDecl:
    """Stands in for a native th-lemma declaration with the given parameters."""

    def __init__(self, parameters):
        self._parameters = parameters

    def params(self):
        return self._parameters


def _z3_available():
    try:
        return subprocess.run([proof_certificate.default_z3_executable(), "--version"],
                              capture_output=True).returncode == 0
    except OSError:
        return False


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
        self.assertEqual(certificate["format_version"], 2)
        self.assertEqual(certificate["z3_version"], z3.get_full_version())
        self.assertEqual(certificate["fragment"], "propositional")
        self.assertEqual(certificate["result"], "unsat")
        self.assertEqual(certificate["verification"], "unverified")
        self.assertEqual(certificate["source_smt2"], _CONTRADICTION)
        self.assertEqual(certificate["query"], 0)
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
            "(get-value (false))", "(eval false)",
            '(include "other.smt2")', "(minimize 0)",
            '(set-option :regular-output-channel "output.txt")',
        ]
        for command in commands:
            with self.subTest(command=command):
                with self.assertRaises(proof_certificate.ProofExportError):
                    proof_certificate.export_certificate(command + "(assert false)")

    def test_define_sort_aliases_are_expanded_and_malformed_ones_rejected(self):
        # Z3's parser expands the alias, so the certificate is about Bool.
        certificate = proof_certificate.export_certificate(
            "(define-sort B () Bool)(define-sort Id (T) T)(declare-const p B)"
            "(declare-const q (Id Bool))(assert (= p q))(assert p)(assert (not q))")
        self.assertEqual(certificate["fragment"], "propositional")
        self.assert_well_formed(certificate)
        malformed = [
            "(define-sort B ())", "(define-sort B () Bool Bool)", "(define-sort B Bool)",
            "(define-sort (B) () Bool)", "(define-sort B (1) Bool)", "(define-sort B ((T)) T)",
            "(define-sort B () (Array Bool Bool) Bool)", "(define-sort 1 () Bool)",
        ]
        for command in malformed:
            with self.subTest(command=command):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, "define-sort takes"):
                    proof_certificate.export_certificate(command + "(assert false)")
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "repeats a parameter"):
            proof_certificate.export_certificate("(define-sort B (T T) T)(assert false)")
        # An alias of an unsupported sort is rejected where it is used, and
        # one defined in a popped scope is gone, as Z3 scopes it.
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "unsupported sort"):
            proof_certificate.export_certificate(
                "(define-sort A () (Array Bool Bool))(declare-const x A)(assert (= x x))(assert false)")
        with self.assertRaises(z3.Z3Exception):
            proof_certificate.export_certificate(
                "(push)(define-sort B () Bool)(pop)(declare-const p B)(assert p)(assert (not p))")
        # reset-assertions keeps aliases like declarations; reset drops them.
        snapshot, _, _ = proof_certificate.query_snapshot(
            "(define-sort B () Bool)(assert false)(reset-assertions)(check-sat)")
        self.assertEqual(snapshot, "(define-sort B () Bool)")
        snapshot, _, _ = proof_certificate.query_snapshot("(define-sort B () Bool)(reset)(check-sat)")
        self.assertEqual(snapshot, "")

    def test_configuration_options_and_output_queries_are_ignored(self):
        # The certificate is a statement about the parsed assertions, so
        # options that configure output, models, limits, or search (by Z3's
        # name with - and _ identified, and the pp.* and model.* families), a
        # tactic in check-sat-using, and output queries leave it unchanged.
        certificate = proof_certificate.export_certificate(_CONFIGURED)
        self.assertEqual(certificate["source_smt2"], _CONFIGURED)
        self.assertEqual(certificate["fragment"], "propositional")
        self.assert_well_formed(certificate)
        # The named assertion is the plain term: Z3's parser drops the label.
        declarations = certificate["declarations"]
        names = [declarations[certificate["nodes"][node]["declaration"]]["name"]
                 for node in certificate["assertions"]]
        self.assertEqual(names, ["and", "b"])
        self.assertNotIn("left", {declaration["name"] for declaration in declarations})
        commands = proof_certificate._assertion_commands(_CONFIGURED)
        self.assertNotIn("set-option", commands)
        self.assertNotIn("check-sat", commands)
        self.assertNotIn("get-", commands)
        self.assertNotIn("echo", commands)
        self.assertIn("(assert (! (and (xor a b) a) :named left))", commands)
        for option in ["produce-assignments true", "unsat_core true", "pp.decimal true", "model.v2 true",
                       "smt.mbqi false", "smt.auto-config false", "nlsat.inline_vars false",
                       "tactic.default_tactic smt", "rlimit 1000", "random-seed 3", "verbose 1"]:
            with self.subTest(option=option):
                proof_certificate.export_certificate("(set-option :%s)(assert false)" % option)
        for query in ["(check-sat-using smt)(get-model)(get-model)", "(check-sat-using aig)(get-assignment)",
                      "(check-sat-using (! smt :random-seed 1))(get-proof)(get-unsat-core)(exit)",
                      '(get-info :status)(echo "x")(check-sat)']:
            with self.subTest(query=query):
                proof_certificate.export_certificate("(assert false)" + query)

    def test_options_changing_the_input_or_the_proof_evidence_are_rejected(self):
        # numeral-as-real, int-real-coercions, smtlib2_compliant, and
        # rewriter.* change how the input is read; the proof-production and
        # preprocessing options are the exporter's own (z3test's matrix
        # harness pins the sat.smt rejection); anything not on the allowlist
        # is rejected rather than ignored.
        cases = [
            ("numeral-as-real true", "changes how the input is read"),
            ("int-real-coercions false", "changes how the input is read"),
            ("smtlib2_compliant true", "changes how the input is read"),
            ("smtlib2-compliant false", "changes how the input is read"),
            ("rewriter.flat false", "changes how the input is read"),
            ("rewriter.hi-div0 true", "changes how the input is read"),
            ("sat.smt true", "option :sat.smt is not supported"),
            ("smt.clause_proof true", "not supported"),
            ('solver.proof.log "proof.log"', "not supported"),
            ("combined_solver.ignore_solver1 true", "not supported"),
            ("smt.solve_eqs true", "not supported"),
            ("smt.bound_simplifier false", "not supported"),
            ("global-declarations true", "not supported"),
            ("encoding unicode", "not supported"),
            ("produce-models", "one keyword and one value"),
            ("produce-models true true", "one keyword and one value"),
        ]
        for option, message in cases:
            with self.subTest(option=option):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, message):
                    proof_certificate.export_certificate("(set-option :%s)(assert false)" % option)
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "one keyword and one value"):
            proof_certificate.export_certificate("(set-option produce-models true)(assert false)")
        # Under smtlib2_compliant Z3's scanner reads -1.0 as the symbol
        # declared below and answers sat; the exporter reads the numeral and
        # would certify a refutation of a different reading of the input.
        with self.assertRaisesRegex(proof_certificate.ProofExportError,
                                    "option :smtlib2_compliant changes how the input is read"):
            proof_certificate.export_certificate("""\
(set-option :smtlib2_compliant true)
(declare-const x Real)
(declare-const |-1.0| Real)
(assert (< x -1.0))
(assert (> x 0.0))
(check-sat)
""")

    def test_query_shapes_are_checked(self):
        cases = [
            ("(get-model)(assert false)", "get-model must occur after check-sat"),
            ("(assert false)(get-unsat-core)", "get-unsat-core must occur after check-sat"),
            ("(assert false)(check-sat-using)", "check-sat-using must name a tactic"),
            ("(assert false)(check-sat)(check-sat-using smt)", "has 2 check-sat queries; select one"),
            ("(assert false)(check-sat-using smt)(check-sat)", "has 2 check-sat queries; select one"),
            # The snapshot of the only query is empty: the assertion after it
            # belongs to no query.
            ("(check-sat-using smt)(assert false)", "sat: no unsat proof"),
            ("(assert false)(check-sat-assuming false)", "parenthesized list of assumptions"),
            ("(declare-const p Bool)(assert p)(check-sat-assuming (p) (p))", "parenthesized list of assumptions"),
            # reset forgets the last result, as in Z3 ("model is not available").
            ("(assert false)(check-sat)(reset)(get-model)", "get-model must occur after check-sat"),
            ("(assert false)(push x)", "push takes at most one numeral"),
            ("(assert false)(pop 2 3)", "pop takes at most one numeral"),
            ("(assert false)(push)(pop 2)", "pop 2 exceeds the 1 open scope"),
            ("(assert false)(reset 1)", "reset must have no arguments"),
            ("(assert false)(reset-assertions 1)", "reset-assertions must have no arguments"),
            ("(assert false)(check-sat-using smt)(get-model a)", "get-model must have no arguments"),
            ("(assert false)(get-info)", "get-info takes one argument"),
            ('(assert false)(echo "a" "b")', "echo takes one argument"),
            ("(assert false)(check-sat)(exit)(get-model)", "commands after exit"),
        ]
        for source, message in cases:
            with self.subTest(source=source):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, message):
                    proof_certificate.export_certificate(source)

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
            "(exit)(assert false)",
            "(check-sat)(get-proof p)", "(exit now)",
        ]
        for suffix in suffixes:
            with self.subTest(suffix=suffix):
                with self.assertRaises(proof_certificate.ProofExportError):
                    proof_certificate.export_certificate("(assert false)" + suffix)

    def test_incremental_scripts_certify_one_query(self):
        # The certificate is about the assertions in scope at one query, with
        # the query's assumptions; the index is recorded and both cores take it.
        snapshots = [
            "(set-logic QF_UF)\n(declare-const p Bool)\n(declare-const q Bool)\n(assert (or p q))\n"
            "(declare-const r Bool)\n(assert (not p))\n(assert (=> q r))",
            None, None,
            "(set-logic QF_UF)\n(declare-const p Bool)\n(declare-const q Bool)\n(assert (or p q))\n"
            "(assert ( not p ))\n(assert ( not q ))",
            "(set-logic QF_UF)\n(declare-const p Bool)\n(declare-const q Bool)",
            "(declare-const p Bool)\n(assert p)\n(assert (not p))",
        ]
        snapshots[1] = snapshots[0] + "\n(assert (not r))"
        snapshots[2] = snapshots[0] + "\n(assert ( not r ))\n(assert ( not q ))"
        for index, snapshot in enumerate(snapshots):
            with self.subTest(query=index):
                self.assertEqual(proof_certificate.query_snapshot(_INCREMENTAL, index), (snapshot, index, 6))
                if index in (0, 4):
                    with self.assertRaisesRegex(proof_certificate.ProofExportError, "sat: no unsat proof"):
                        proof_certificate.export_certificate(_INCREMENTAL, index)
                    continue
                certificate = proof_certificate.export_certificate(_INCREMENTAL, index)
                self.assert_well_formed(certificate)
                self.assertEqual(certificate["query"], index)
                self.assertEqual(certificate["source_smt2"], _INCREMENTAL)
                self.assertEqual(certificate["fragment"], "propositional")
                self.assertEqual(len(certificate["assertions"]), snapshot.count("(assert "))
        result = self.run_cli("--query", "3", "-", source=_INCREMENTAL)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)["query"], 3)
        # Selecting a query is required when there are several and an error
        # when it does not exist; a script without any query is query 0 over
        # its final state.
        cases = [
            (None, "has 6 check-sat queries; select one"), (6, "has 6 check-sat queries, so query 6 does not"),
            (-1, "nonnegative integer"), ("0", "nonnegative integer"), (True, "nonnegative integer"),
        ]
        for query, message in cases:
            with self.subTest(query=query):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, message):
                    proof_certificate.query_snapshot(_INCREMENTAL, query)
        self.assertEqual(proof_certificate.query_snapshot("(assert false)"), ("(assert false)", 0, 0))
        self.assertEqual(proof_certificate.query_snapshot("(assert false)", 0), ("(assert false)", 0, 0))
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "has 0 check-sat queries, so query 1"):
            proof_certificate.query_snapshot("(assert false)", 1)
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "has 1 check-sat query, so query 1"):
            proof_certificate.query_snapshot(_CONTRADICTION, 1)
        self.assertEqual(proof_certificate.query_snapshot(_CONTRADICTION, 0)[1:], (0, 1))
        # Declarations are scoped, as in Z3's default: a constant declared
        # inside a popped scope is unknown afterwards. reset-assertions is
        # Z3's (cmd_context::reset_assertions), not SMT-LIB's "pop every
        # scope": the assertions of every scope go, the declarations and the
        # open scopes stay, and a later pop still drops its scope's
        # declarations. Z3 answers unsat, unsat, unsat, and "unknown
        # constant q" to these four scripts.
        with self.assertRaisesRegex(z3.Z3Exception, "unknown constant q"):
            proof_certificate.export_certificate("(push)(declare-const q Bool)(assert q)(pop)(assert q)(check-sat)")
        scoped = ("(declare-const p Bool)(push 1)(declare-const q Bool)(assert q)(reset-assertions)"
                  "(assert q)(assert (not q))(check-sat)(pop 1)(assert (not p))(assert p)(check-sat)")
        self.assertEqual(proof_certificate.query_snapshot(scoped, 0),
                         ("(declare-const p Bool)\n(declare-const q Bool)\n(assert q)\n(assert (not q))", 0, 2))
        self.assertEqual(proof_certificate.query_snapshot(scoped, 1),
                         ("(declare-const p Bool)\n(assert (not p))\n(assert p)", 1, 2))
        for index in (0, 1):
            self.assert_well_formed(proof_certificate.export_certificate(scoped, index))
        popped = "(declare-const p Bool)(push)(assert p)(reset-assertions)(pop)(assert (not p))(assert p)(check-sat)"
        self.assertEqual(proof_certificate.query_snapshot(popped),
                         ("(declare-const p Bool)\n(assert (not p))\n(assert p)", 0, 1))
        self.assert_well_formed(proof_certificate.export_certificate(popped))
        with self.assertRaisesRegex(z3.Z3Exception, "unknown constant q"):
            proof_certificate.export_certificate("(declare-const p Bool)(push)(declare-const q Bool)(assert p)"
                                                 "(reset-assertions)(pop)(assert q)(check-sat)")
        # Z3 still answers get-model after reset-assertions (reset is the one
        # that forgets the result, see test_query_shapes_are_checked).
        self.assert_well_formed(proof_certificate.export_certificate(
            "(assert false)(check-sat)(reset-assertions)(get-model)(get-proof)"))
        # Assumptions need not be literals: Z3's parser checks them as assertions.
        assumed = "(declare-const p Bool)(declare-const q Bool)(assert (or p q))(check-sat-assuming ((not (or q p))))"
        self.assertEqual(proof_certificate.query_snapshot(assumed)[0].splitlines()[-1], "(assert ( not ( or q p ) ))")
        self.assert_well_formed(proof_certificate.export_certificate(assumed))
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "sat: no unsat proof"):
            proof_certificate.export_certificate("(declare-const p Bool)(assert p)(check-sat-assuming ())")

    @unittest.skipUnless(_z3_available(), "the z3 executable is required for the clause log")
    def test_incremental_scripts_certify_one_query_through_the_clause_log(self):
        certificate = proof_certificate.export_clause_log_certificate(_INCREMENTAL, query=2)
        self.assertEqual((certificate["query"], certificate["fragment"], len(certificate["assertions"])),
                         (2, "propositional", 5))
        result = self.run_cli("--core", "clause-log", "--query", "5", "-", source=_INCREMENTAL)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)["query"], 5)

    def test_malformed_input_is_rejected(self):
        for source in ["(", ")", "()", "assert false", '(set-info :source "broken)',
                       "(declare-const |broken Bool)", "(assert false"]:
            with self.subTest(source=source):
                with self.assertRaises(proof_certificate.ProofExportError):
                    proof_certificate.export_certificate(source)
        with self.assertRaises(z3.Z3Exception):
            proof_certificate.export_certificate("(assert undeclared)")

    def test_unsupported_input_is_rejected_even_with_false(self):
        problems = [
            "(declare-const x Int)(declare-const y Real)(assert (= (to_real x) y))",
            "(declare-const x Real)(assert (< (* x x) 0.0))",
            "(declare-const x (_ BitVec 8))(assert (= x #x00))",
            "(declare-const a (Array Bool Bool))(assert (select a true))",
            "(declare-fun f (Int) Bool)(declare-const x Real)(assert (and (f 1) (> x 1.0)))",
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
            ("(get-value (false))", "unsupported SMT-LIB command"),
            ("(assert undeclared)", "undeclared"),
            ("(assert false)(check-sat)(check-sat)", "select one by its zero-based index (--query)"),
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
# Uninterpreted predicates over Bool without any uninterpreted sort.
_BOOLEAN_PREDICATES = """\
(declare-fun r (Bool) Bool)
(declare-fun s (Bool Bool) Bool)
(declare-const p Bool)
(declare-const q Bool)
(assert (= p q))
(assert (or (r p) (s p q)))
(assert (not (r q)))
(assert (not (s q q)))
(check-sat)
"""
# QF_UFLRA in which y occurs in a single function argument: the frontend's
# elim-uncnstr tactic would replace (- x y) by a fresh constant.
_SINGLE_OCCURRENCE = """\
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun q (Real) Bool)
(declare-const x Real)
(declare-const y Real)
(assert (q (f (- x y))))
(assert (or (not (q (f (+ x (* (- 1.0) y))))) (< (f (+ 2.0 2.0)) 4.0)))
(assert (>= (f 4.0) (f (- x x))))
(assert (= (f 0.0) 4.0))
(check-sat)
"""
# QF_UFLRA: an uninterpreted sort next to Real variables, functions between
# the sort and Real, a Real-valued function, and a predicate over Real.
_UFLRA = """\
(set-logic QF_UFLRA)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun f (Real) Real)
(declare-fun g (U) Real)
(declare-fun h (Real) U)
(declare-fun q (Real) Bool)
(declare-const x Real)
(declare-const y Real)
(assert (= a b))
(assert (<= x y))
(assert (>= x y))
(assert (or (> (g a) (+ (g b) 1.0)) (q (f x))))
(assert (or (not (q (f y))) (not (= (h x) (h y))) (< (f (g a)) 0.0)))
(assert (>= (f (g b)) 0.0))
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


# The Int twin of _UFLRA, plus a gcd conflict through an application: two
# congruences and Farkas steps over Int-valued applications as opaque atoms.
_UFLIA = """\
(set-logic QF_UFLIA)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun f (Int) Int)
(declare-fun g (U) Int)
(declare-fun h (Int) U)
(declare-fun q (Int) Bool)
(declare-const x Int)
(declare-const y Int)
(assert (= a b))
(assert (<= x y))
(assert (>= x y))
(assert (or (> (g a) (+ (g b) 1)) (q (f x))))
(assert (or (not (q (f y))) (not (= (h x) (h y))) (= (* 2 (f (g a))) (+ (* 2 y) 1))))
(check-sat)
"""

# A Gomory cut: rationally feasible, integer infeasible, refuted by one cut
# hint over the four bounds. The log is the sat.smt core's output verbatim.
_LIA = """\
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (<= (+ (* 2 x) (* 2 y)) 3))
(assert (>= (+ (* 2 x) (* 2 y)) 1))
(assert (>= (- (* 4 x) (* 2 y)) 1))
(assert (<= (- (* 4 x) (* 2 y)) 3))
(check-sat)
"""

_LIA_LOG = """\
(declare-fun y () Int)
(declare-fun x () Int)
(define-const $9 Int (* 2 y))
(define-const $7 Int (* 2 x))
(define-const $10 Int (+ $7 $9))
(define-const $12 Bool (<= $10 3))
(assume $12)
(define-const $14 Bool (>= $10 1))
(assume $14)
(define-const $24 Int (* (- 2) y))
(define-const $16 Int (* 4 x))
(define-const $25 Int (+ $16 $24))
(define-const $26 Bool (>= $25 1))
(assume $26)
(define-const $27 Bool (<= $25 3))
(assume $27)
(declare-fun cut (Int Bool Int Bool Int Bool Int Bool) Proof)
(define-const $31 Proof (cut 1 $12 1 $14 1 $26 1 $27))
(infer (not $12) (not $14) (not $26) (not $27) $31)
(declare-fun rup () Proof)
(infer rup)
"""


# Integer div and mod by a numeral: the sat.smt arithmetic solver adds their
# defining clauses itself (3 (div x 3) + (mod x 3) = x, 0 <= mod x 3 <= 2)
# under the hint arith, whose argument is the negated clause literal; the
# euf step carries a comm annotation.
_LIA_DIV = """\
(declare-const x Int)
(assert (not (= x (+ (* 3 (div x 3)) (mod x 3)))))
(check-sat)
"""

_LIA_DIV_LOG = """\
(declare-fun x () Int)
(define-const $9 Int (mod x 3))
(define-const $7 Int (div x 3))
(define-const $8 Int (* 3 $7))
(define-const $10 Int (+ $8 $9))
(define-const $17 Bool (= $10 x))
(declare-fun arith (Bool) Proof)
(define-const $20 Bool (not $17))
(define-const $21 Proof (arith $20))
(infer $17 $21)
(define-const $18 Bool (>= $9 0))
(define-const $22 Bool (not $18))
(define-const $23 Proof (arith $22))
(infer $18 $23)
(define-const $24 Bool (<= $9 2))
(define-const $25 Bool (not $24))
(define-const $26 Proof (arith $25))
(infer $24 $26)
(define-const $11 Bool (= x $10))
(assume (not $11))
(declare-fun euf (Bool Bool Proof) Proof)
(declare-fun comm (Bool) Proof)
(define-const $27 Bool (= $11 $17))
(define-const $28 Proof (comm $27))
(define-const $12 Bool (not $11))
(define-const $29 Proof (euf $12 $17 $28))
(infer (not $17) $11 $29)
(declare-fun rup () Proof)
(infer $11 rup)
(infer rup)
"""


# A Real division by a numeral inside a ground atom, next to a conflict at
# level zero: the sat.smt arithmetic solver logs its axiom q = 0 or
# q * (p / q) = p for the quotient (/ 1.0 2.0) under the hint arith, with the
# first literal as the constant true (the negation of the false disequality
# (= 2.0 0.0), elided from the clause) and the second as the negated equality.
_LRA_DIV = """\
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (< x x))
(assert (or (< y z) (< (/ 1.0 2.0) 3.0)))
(check-sat)
"""

_LRA_DIV_LOG = """\
(assume (not false))
(assume)
(define-const $12 Real (/ 1.0 2.0))
(define-const $23 Real (* 2.0 $12))
(define-const $25 Bool (= $23 1.0))
(declare-fun arith (Bool Bool) Proof)
(define-const $24 Bool (not $25))
(define-const $26 Proof (arith true $24))
(infer $25 $26)
(declare-fun z () Real)
(declare-fun y () Real)
(define-const $9 Bool (< y z))
(define-const $14 Bool (< $12 3.0))
(assume $9 $14)
(declare-fun rup () Proof)
(infer rup)
"""


class TestFragmentClassification(unittest.TestCase):
    def classify(self, source):
        assertions, fragment = proof_certificate.parse_assertions(source, z3.Context(), integer=True)
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

    def test_linear_integer_inputs_are_classified(self):
        self.assertEqual(self.classify("(declare-const x Int)(assert (> x 1))"), "qf_lia")
        self.assertEqual(self.classify(_LIA), "qf_lia")
        # Scaling, negation, nested sums, a Boolean condition, an Int ite, and
        # distinct over Int all stay in the fragment; a numeral comparison too.
        shapes = ("(declare-const x Int)(declare-const y Int)(declare-const p Bool)"
                  "(assert (or p (< (- (* 2 x) (- y)) 1)))"
                  "(assert (= (ite (and p (< x 1)) x (ite p 1 (- x))) (+ y 2)))"
                  "(assert (distinct x y 3))(assert (<= 1 2))")
        self.assertEqual(self.classify(shapes), "qf_lia")
        # An unused Real declaration does not mix the sorts.
        self.assertEqual(self.classify("(declare-const r Real)(declare-const x Int)(assert (> x 1))"), "qf_lia")
        # Integer div and mod by a nonzero numeral (negative too, and written
        # as a negated numeral), of any linear term, variable-free as well,
        # and abs are opaque atoms of the linear forms.
        division = ("(declare-const x Int)(declare-const y Int)"
                    "(assert (= y (div x 3)))(assert (> (mod (+ x y) (- 2)) 0))(assert (< (div (* 2 x) -4) y))"
                    "(assert (= (mod (abs (- x y)) 7) (div 7 2)))(assert (> (* 2 (div (ite (> x 0) x y) 3)) 1))")
        self.assertEqual(self.classify(division), "qf_lia")
        self.assertEqual(self.classify(_LIA_DIV), "qf_lia")

    def test_integer_arithmetic_with_uninterpreted_symbols_is_qf_uflia(self):
        # Uninterpreted sorts or functions together with linear integer
        # arithmetic are QF_UFLIA, the Int twin of QF_UFLRA: functions and
        # predicates may take and return Int, a function whose signature
        # mentions Int makes the input arithmetic even without any Int atom,
        # and a Bool-only predicate over Int atoms belongs here too.
        declarations = "(declare-sort U 0)(declare-fun a () U)"
        for source in [
            "(declare-fun f (Int) Int)(declare-const x Int)(assert (> (f x) 1))",
            declarations + "(declare-const x Int)(assert (and (= a a) (> x 1)))",
            "(declare-fun p (Bool) Bool)(declare-const x Int)(assert (and (p true) (> x 1)))",
            "(declare-fun r (Bool) Bool)(declare-const x Int)(assert (r (> x 1)))",
            declarations + "(declare-fun h (U) Int)(assert (= (h a) (h a)))",
            declarations + "(declare-fun h (Int) U)(declare-fun q (Int) Bool)(assert (and (= (h 1) a) (q 2)))",
            declarations + "(declare-fun r (Bool Int) Bool)(assert (r true 1))",
            "(declare-fun f (Int Int) Int)(declare-const x Int)(declare-const p Bool)"
            "(assert (> (f (ite p x (- x)) (* 2 x)) (f 1 (+ x 1))))",
            declarations + "(declare-fun h (Int) U)(declare-const p Bool)(assert (= (ite p (h 1) a) a))",
            "(declare-fun h (Bool) Int)(declare-const p Bool)(assert (distinct (h p) (h (not p)) 3))",
            "(declare-fun f (Int) Int)(declare-const x Int)(assert (> (f (div x 2)) (mod (f x) 3)))",
        ]:
            with self.subTest(source=source):
                self.assertEqual(self.classify(source), "qf_uflia")
        self.assertEqual(self.classify(_UFLIA), "qf_uflia")

    def test_nonlinear_integer_and_other_inputs_are_rejected(self):
        for source, message in [
            ("(declare-const x Real)(assert (> (* x x) 1.0))", "nonlinear"),
            ("(declare-const x Real)(declare-const y Real)(assert (> (/ x y) 1.0))", "division"),
            # Integer arithmetic never mixes with Real, not even through a
            # function signature; no conversions.
            ("(declare-fun f (Int) Real)(declare-const x Int)(assert (> (f x) 1.0))", "mixing integer and real"),
            # Z3's parser coerces a Real argument of an Int-domain function with to_int.
            ("(declare-fun f (Int) Real)(declare-const x Real)(assert (> (f x) 1.0))", "operator: to_int"),
            ("(declare-fun f (Real) Int)(declare-const x Real)(assert (> (f x) 1))", "mixing integer and real"),
            ("(declare-fun f (Int) Int)(declare-const x Real)(declare-const y Int)(assert (and (> (f y) 1) (> x 1.0)))",
             "mixing integer and real"),
            ("(declare-const x Int)(declare-const y Real)(assert (> (to_real x) y))", "unsupported arithmetic operator"),
            ("(declare-const x Int)(declare-const y Real)(assert (and (> x 1) (> y 1.0)))", "mixing integer and real"),
            # Integer div and mod by zero are uninterpreted in SMT-LIB and
            # total in Lean, by a term nonlinear; rem is not SMT-LIB.
            ("(declare-const x Int)(assert (> (div x 0) 1))", "integer div is supported only by a nonzero constant"),
            ("(declare-const x Int)(assert (> (mod x (- 1 1)) 1))", "integer mod is supported only by a nonzero constant"),
            ("(declare-const x Int)(declare-const y Int)(assert (> (div x y) 1))",
             "integer div is supported only by a nonzero constant"),
            ("(declare-fun f (Int) Int)(declare-const x Int)(assert (> (mod x (f 2)) 1))",
             "integer mod is supported only by a nonzero constant"),
            ("(declare-const x Int)(assert (> (rem x 2) 1))", "unsupported arithmetic operator: rem"),
            # SMT-LIB defines abs on Int only; Z3 accepts it over Real, the reconstructor does not.
            ("(declare-const x Real)(assert (< (abs x) 0.0))", "unsupported arithmetic operator: abs over Real"),
            ("(declare-const x Int)(declare-const y Int)(assert (> (* x y) 1))", "nonlinear"),
            ("(declare-fun f (Real) Real)(declare-const x Real)(assert (> (* x (f x)) 1.0))", "nonlinear"),
            ("(declare-fun f (Real) Real)(declare-const x Real)(assert (> (/ 1.0 (f x)) 1.0))", "division"),
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
        # Functions and predicates may take Bool arguments, including formulas;
        # predicates over Bool alone are the fragment without a sort.
        for source in [
            declarations + "(declare-fun h (Bool) U)(assert (= (h true) a))",
            declarations + "(declare-fun h (U Bool) V)(declare-fun r (Bool) Bool)"
                           "(assert (= (h a (r (= v v))) v))",
            declarations + "(declare-fun r (Bool Bool) Bool)(declare-const p Bool)(assert (and (= a a) (r p (not p))))",
            "(declare-fun r (Bool) Bool)(declare-const p Bool)(assert (r p))",
            "(declare-sort U 0)(declare-fun r (Bool Bool) Bool)(declare-const p Bool)(assert (r p p))",
        ]:
            with self.subTest(source=source):
                self.assertEqual(self.classify(source), "qf_uf")
        # Uninterpreted sorts or functions together with linear real arithmetic
        # are QF_UFLRA: functions and predicates may take and return Real, and
        # a function whose signature mentions Real makes the input arithmetic
        # even without any Real atom.
        for source in [
            declarations + "(declare-const x Real)(assert (and (= a a) (> x 1.0)))",
            "(declare-fun r (Bool) Bool)(declare-const x Real)(assert (r (> x 1.0)))",
            declarations + "(declare-fun h (U) V)(declare-const x Real)(assert (and (= (h a) v) (> x 1.0)))",
            declarations + "(declare-fun h (U) Real)(assert (> (h a) 1.0))",
            declarations + "(declare-fun r (Bool Real) Bool)(assert (r true 1.0))",
            declarations + "(declare-fun q (Real) Bool)(assert (q 1.0))",
            "(declare-fun f (Real) Real)(declare-const x Real)(assert (> (f (f x)) (+ (f x) 1.0)))",
            "(declare-fun f (Real Real) Real)(declare-fun q (Real) Bool)(assert (q (f 1.0 2.0)))",
            declarations + "(declare-fun h (Real) U)(declare-const p Bool)(assert (= (ite p (h 1.0) a) a))",
            "(declare-fun h (Bool) Real)(declare-const p Bool)(assert (= (h p) (h (not p))))",
        ]:
            with self.subTest(source=source):
                self.assertEqual(self.classify(source), "qf_uflra")
        for source, message in [
            (declarations + "(declare-fun h (U) Int)(declare-const x Real)(assert (and (= (h a) (h a)) (> x 1.0)))",
             "mixing integer and real"),
            ("(declare-fun f (Real) Real)(declare-const x Real)(assert (> (* (f x) (f x)) 1.0))", "nonlinear"),
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

    def test_integer_fragments_are_opt_in_on_both_paths(self):
        # Both classifications accept the input once the consumer opts in to
        # the fragment; by default it stays unsupported, since the integer
        # solver's cut steps are certified by Lean alone. The exporters opt in.
        for parse in (proof_certificate.parse_assertions, proof_certificate.parse_legacy_assertions):
            with self.subTest(parse=parse.__name__):
                self.assertEqual(parse(_LIA, z3.Context(), integer=True)[1], "qf_lia")
                with self.assertRaisesRegex(proof_certificate.ProofExportError,
                                            r"\(qf_lia\).*accept the fragment explicitly"):
                    parse(_LIA, z3.Context())
                # The same for integers next to uninterpreted functions.
                self.assertEqual(parse(_UFLIA, z3.Context(), integer=True)[1], "qf_uflia")
                with self.assertRaisesRegex(proof_certificate.ProofExportError,
                                            r"\(qf_uflia\).*accept the fragment explicitly"):
                    parse(_UFLIA, z3.Context())
        with self.assertRaisesRegex(proof_certificate.ProofExportError, r"\(qf_lia\).*accept the fragment explicitly"):
            proof_certificate.parse_propositional_assertions(_LIA, z3.Context())
        self.assertEqual(proof_certificate.export_certificate(_LIA)["fragment"], "qf_lia")
        self.assertEqual(proof_certificate.export_certificate(_UFLIA)["fragment"], "qf_uflia")

    def test_legacy_exporter_exports_linear_real_arithmetic(self):
        # theory_lra records the Farkas coefficients of its LP conflicts as
        # th-lemma parameters, which the certificate keeps as the hint and its
        # coefficients; numerals are declared by value like the clause log does.
        certificate = proof_certificate.export_certificate(_LRA)
        self.assertEqual(certificate["fragment"], "qf_lra")
        declarations = certificate["declarations"]
        th_lemmas = [(d, [n for n in certificate["nodes"] if declarations[n["declaration"]] is d])
                     for d in declarations if d["name"] == "th-lemma"]
        self.assertTrue(th_lemmas)
        for declaration, nodes in th_lemmas:
            self.assertEqual(declaration["range"], "Proof")
            self.assertEqual(declaration["domain"][-1], "Bool")
            self.assertTrue(all(sort == "Proof" for sort in declaration["domain"][:-1]))
            self.assertIn(declaration["parameters"][0], ("farkas", "bound", "smt"))
            if declaration["parameters"][0] == "smt":
                self.assertEqual(declaration["parameters"], ["smt"])
                continue
            coefficients = [Fraction(c) for c in declaration["parameters"][1:]]
            self.assertTrue(all(c > 0 for c in coefficients))
            for node in nodes:
                premises = node["arguments"][:-1]
                conclusion = certificate["nodes"][node["arguments"][-1]]
                clause = (0 if declarations[conclusion["declaration"]]["kind"] == z3.Z3_OP_FALSE
                          else len(conclusion["arguments"]) if declarations[conclusion["declaration"]]["kind"] == z3.Z3_OP_OR
                          else 1)
                self.assertEqual(len(coefficients), len(premises) + clause)
        # Numerals are declared by value (the exact set depends on the smt
        # core's rewriting of the assertions, so only the form is checked).
        numerals = {d["name"] for d in declarations if d["kind"] == z3.Z3_OP_ANUM}
        self.assertTrue(numerals)
        self.assertEqual({str(Fraction(name)) for name in numerals}, numerals)
        self.assertTrue(all(d["range"] == "Real" for d in declarations if d["kind"] == z3.Z3_OP_ANUM))
        self.assertTrue(all(d["parameters"] == [] for d in declarations if d["name"] != "th-lemma"))
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "not propositional.*qf_uf"):
            proof_certificate.parse_propositional_assertions(_UF, z3.Context())
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "not propositional.*qf_lra"):
            proof_certificate.parse_propositional_assertions(_LRA, z3.Context())

    def test_legacy_th_lemma_parameters_are_validated(self):
        context = z3.Context(proof=True)
        x = z3.Real("x", ctx=context)
        solver = z3.Solver(ctx=context)
        solver.add(x > 1, x < 0)
        self.assertEqual(solver.check(), z3.unsat)
        proof = solver.proof()
        th_lemma = next(node for node in _proof_nodes(proof) if node.decl().name() == "th-lemma")
        self.assertEqual([str(p) for p in th_lemma.decl().params()][:2], ["arith", "farkas"])
        # A th-lemma declaration with a hint the reconstructor cannot replay is rejected at export.
        arith = th_lemma.decl().params()[0]
        for parameters, message in [
            ([], "without a replayable theory hint"),
            (["arith"], "without a replayable theory hint"),
            (["arith", "nla", 1], "without a replayable theory hint"),
            (["arith", "gomory-cut", 1], "without a replayable theory hint"),
            (["farkas", "arith", 1], "without a replayable theory hint"),
            (["arith", "farkas", "x"], "not a rational"),
        ]:
            with self.subTest(parameters=parameters):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, message):
                    proof_certificate._th_lemma_parameters(_FakeDecl(parameters), 2)
        parameters = proof_certificate._th_lemma_parameters
        self.assertEqual(parameters(_FakeDecl([arith, "farkas", 1, "1/2"]), 2), ["farkas", "1", "1/2"])
        self.assertEqual(parameters(_FakeDecl(["arith", "bound", "2", "1"]), 1), ["bound", "2", "1"])
        # theory_arith's sign and antecedent-only conventions are normalized.
        self.assertEqual(parameters(_FakeDecl(["arith", "farkas", "-1", "2"]), 2), ["farkas", "1", "2"])
        self.assertEqual(parameters(_FakeDecl(["arith", "assign-bounds", "-1", "1"]), 0), ["bound", "1", "1", "1"])
        self.assertEqual(parameters(_FakeDecl(["arith", "assign-bounds", "3", "1"]), 2), ["bound", "3", "1", "1"])
        self.assertEqual(parameters(_FakeDecl(["arith", "implied-eq"]), 3), ["implied-eq"])
        self.assertEqual(parameters(_FakeDecl(["arith", "eq-propagate", "1", "1"]), 2), ["implied-eq"])
        self.assertEqual(parameters(_FakeDecl(["arith", "triangle-eq"]), 0), ["triangle-eq"])

    def test_lp_inference_parameters_are_normalized(self):
        parameters = proof_certificate._th_lemma_parameters
        x = z3.Real("x")
        self.assertEqual(parameters(_FakeDecl(["arith", "lp-input", "0"]), 1), ["smt"])
        self.assertEqual(parameters(_FakeDecl(["arith", "lp-input", "0"]), 0), ["smt"])
        self.assertEqual(parameters(_FakeDecl(["arith", "lp-discharge", "7"]), 1), ["smt"])
        self.assertEqual(parameters(_FakeDecl(["arith", "lp-linear", "3", "1/2", "1", "1/2"]),
                                    3, z3.BoolVal(False)), ["farkas", "1/2", "1", "1/2"])
        self.assertEqual(parameters(_FakeDecl(["arith", "lp-linear", "5", "-2", "1"]),
                                    1, x <= 2), ["bound", "2", "1"])
        self.assertEqual(parameters(_FakeDecl(["arith", "lp-linear", "5", "-2", "1"]),
                                    1, x == 2), ["implied-eq"])
        self.assertEqual(parameters(_FakeDecl(["arith", "lp-linear", "5", "1"]),
                                    0, x == x), ["smt"])
        for raw, premises, message in [
            (["lp-input"], 1, "step index"),
            (["lp-input", "-1"], 1, "step index"),
            (["lp-input", "1/2"], 1, "step index"),
            (["lp-input", "4294967295"], 1, "step index"),
            (["lp-input", "x"], 1, "step index"),
            (["lp-input", "0", "1"], 1, "invalid lp-input"),
            (["lp-input", "0"], 2, "invalid lp-input"),
            (["lp-discharge", "0"], 0, "invalid lp-discharge"),
            (["lp-linear", "0", "1"], 2, "coefficient count"),
            (["lp-linear", "0", "x"], 1, "not a rational"),
            (["lp-integer-tighten", "0"], 1, "without a replayable theory hint"),
            (["lp-monomial-interval", "0"], 1, "without a replayable theory hint"),
            (["lp-unknown", "0"], 1, "without a replayable theory hint"),
        ]:
            with self.subTest(parameters=raw):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, message):
                    parameters(_FakeDecl(["arith"] + raw), premises, z3.BoolVal(False))

    def test_integer_lp_inferences_are_left_to_lean(self):
        parameters = proof_certificate._th_lemma_parameters
        x = z3.Int("x")
        for rule in ("lp-integer-tighten", "lp-integer-lattice", "lp-gomory"):
            with self.subTest(rule=rule):
                declaration = _FakeDecl(["arith", rule, "1"])
                self.assertEqual(parameters(declaration, 1, x <= 2, integer=True), ["arith"])
                self.assertEqual(parameters(declaration, 1, z3.BoolVal(False), integer=True), ["farkas"])
                with self.assertRaisesRegex(proof_certificate.ProofExportError, "without a replayable theory hint"):
                    parameters(declaration, 1, x <= 2)
                with self.assertRaisesRegex(proof_certificate.ProofExportError, "invalid .* inference"):
                    parameters(_FakeDecl(["arith", rule, "1", "2"]), 1, x <= 2, integer=True)
        for rule in ("lp-monomial-substitute", "lp-monomial-interval", "lp-unknown"):
            with self.subTest(rule=rule):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, "without a replayable theory hint"):
                    parameters(_FakeDecl(["arith", rule, "1"]), 1, x <= 2, integer=True)

    def test_lp_context_is_not_a_logical_premise(self):
        context = z3.Context(proof=True)
        assertions = z3.parse_smt2_string(_LRA, ctx=context)
        solver = z3.Solver(ctx=context)
        solver.add(assertions)
        self.assertEqual(solver.check(), z3.unsat)
        proof = solver.proof()
        linear = next(node for node in _proof_nodes(proof)
                      if node.decl().params()[:2] == ["arith", "lp-linear"])
        arguments = proof_certificate._proof_arguments(linear)
        self.assertEqual([arg.get_id() for arg in arguments],
                         [arg.get_id() for arg in linear.children()[1:]])
        lp_context = linear.arg(0)
        invalid_context = lp_context.decl()(z3.BoolVal(False, ctx=context))
        invalid_linear = linear.decl()(invalid_context, *linear.children()[1:])
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "invalid LP context"):
            proof_certificate._certificate_from_proof(_LRA, assertions, invalid_linear)
        certificate = proof_certificate._certificate_from_proof(_LRA, assertions, proof)
        self.assertFalse(any(parameter.startswith("lp-")
                             for decl in certificate["declarations"] for parameter in decl["parameters"]))
        self.assertTrue(all(sort != "Int" for decl in certificate["declarations"]
                            for sort in decl["domain"] + [decl["range"]]))

    def test_legacy_exporter_exports_uninterpreted_functions(self):
        # The smt core's proof object carries complete equality proofs, so QF_UF
        # goes through the legacy path too; the certificate keeps the sort name.
        certificate = proof_certificate.export_certificate(_UF)
        self.assertEqual(certificate["fragment"], "qf_uf")
        self.assertEqual(certificate["result"], "unsat")
        self.assertEqual(certificate["verification"], "unverified")
        declarations = certificate["declarations"]
        self.assertEqual({d["range"] for d in declarations} - {"Bool", "Proof"}, {"U"})
        self.assertEqual({(d["name"], tuple(d["domain"]), d["range"]) for d in declarations
                          if d["kind"] == z3.Z3_OP_UNINTERPRETED},
                         {("a", (), "U"), ("b", (), "U"), ("c", (), "U"), ("f", ("U",), "U"),
                          ("g", ("U", "U"), "U"), ("p", ("U",), "Bool")})
        self.assertTrue(all(d["parameters"] == [] for d in declarations))
        self.assertIn("monotonicity", certificate["rule_counts"])
        root = certificate["nodes"][certificate["proof"]]
        self.assertEqual(declarations[root["declaration"]]["range"], "Proof")
        conclusion = certificate["nodes"][root["arguments"][-1]]
        self.assertEqual(declarations[conclusion["declaration"]]["kind"], z3.Z3_OP_FALSE)

    def test_boolean_predicates_without_a_sort_export_through_the_legacy_core(self):
        # Predicates over Bool alone are qf_uf; the smt core's proof object
        # proves their congruences by monotonicity like any other predicate's.
        context = z3.Context()
        certificate = proof_certificate.export_certificate(_BOOLEAN_PREDICATES)
        self.assertEqual(certificate["fragment"], "qf_uf")
        declarations = certificate["declarations"]
        self.assertEqual({d["range"] for d in declarations}, {"Bool", "Proof"})
        self.assertEqual({(d["name"], tuple(d["domain"]), d["range"]) for d in declarations
                          if d["kind"] == z3.Z3_OP_UNINTERPRETED},
                         {("r", ("Bool",), "Bool"), ("s", ("Bool", "Bool"), "Bool"),
                          ("p", (), "Bool"), ("q", (), "Bool")})
        self.assertIn("monotonicity", certificate["rule_counts"])
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "not propositional.*qf_uf"):
            proof_certificate.parse_propositional_assertions(_BOOLEAN_PREDICATES, context)

    def test_legacy_exporter_exports_uninterpreted_functions_with_arithmetic(self):
        # QF_UFLRA through the legacy proof object: the sort name is kept, the
        # functions keep their Real arguments and results, numerals are declared
        # by value, and theory_lra's th-lemma steps carry their coefficients.
        certificate = proof_certificate.export_certificate(_UFLRA)
        self.assertEqual(certificate["fragment"], "qf_uflra")
        declarations = certificate["declarations"]
        self.assertEqual({d["range"] for d in declarations} - {"Bool", "Proof"}, {"U", "Real"})
        self.assertEqual({(d["name"], tuple(d["domain"]), d["range"]) for d in declarations
                          if d["kind"] == z3.Z3_OP_UNINTERPRETED},
                         {("a", (), "U"), ("b", (), "U"), ("x", (), "Real"), ("y", (), "Real"),
                          ("f", ("Real",), "Real"), ("g", ("U",), "Real"), ("h", ("Real",), "U"), ("q", ("Real",), "Bool")})
        self.assertLessEqual({"0", "1"}, {d["name"] for d in declarations if d["kind"] == z3.Z3_OP_ANUM})
        self.assertIn("monotonicity", certificate["rule_counts"])
        self.assertIn("th-lemma", certificate["rule_counts"])
        hints = set()
        for declaration in declarations:
            if declaration["name"] == "th-lemma":
                hints.add(declaration["parameters"][0])
                self.assertIn(declaration["parameters"][0], ("farkas", "bound", "implied-eq", "triangle-eq"))
                self.assertTrue(all(Fraction(c) > 0 for c in declaration["parameters"][1:]))
                if declaration["parameters"][0] == "triangle-eq":
                    # arith_eq_adapter's axiom tying x = y to its bounds: no premises, no coefficients.
                    self.assertEqual(declaration["parameters"], ["triangle-eq"])
                    self.assertEqual(declaration["domain"], ["Bool"])
                elif declaration["parameters"][0] == "implied-eq":
                    # theory_lra's equality propagation x = y from x <= y and
                    # x >= y, needed here for the congruence (h x) = (h y):
                    # premises, no coefficients, and a Real equality as conclusion.
                    self.assertEqual(declaration["parameters"], ["implied-eq"])
                    self.assertGreaterEqual(len(declaration["domain"]), 3)
                    for node in certificate["nodes"]:
                        if declarations[node["declaration"]] is declaration:
                            conclusion = certificate["nodes"][node["arguments"][-1]]
                            self.assertEqual(declarations[conclusion["declaration"]]["name"], "=")
                            self.assertEqual(declarations[conclusion["declaration"]]["domain"], ["Real", "Real"])
                else:
                    # One coefficient per premise and per literal of the concluding clause.
                    self.assertGreaterEqual(len(declaration["parameters"]) - 1, len(declaration["domain"]) - 1)
        self.assertIn("implied-eq", hints)
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "not propositional.*qf_uflra"):
            proof_certificate.parse_propositional_assertions(_UFLRA, z3.Context())

    def test_legacy_exporter_exports_integer_arithmetic(self):
        # The indexed LP proof separates integer rounding, proved by Lean
        # alone, from linear combinations whose local coefficients certify.
        certificate = proof_certificate.export_certificate(_LIA)
        self.assertEqual(certificate["fragment"], "qf_lia")
        declarations = certificate["declarations"]
        self.assertEqual({d["range"] for d in declarations}, {"Bool", "Int", "Proof"})
        self.assertTrue(all(d["range"] == "Int" and Fraction(d["name"]).denominator == 1
                            for d in declarations if d["kind"] == z3.Z3_OP_ANUM))
        parameters = [d["parameters"] for d in declarations if d["name"] == "th-lemma"]
        self.assertIn(["arith"], parameters)
        self.assertTrue(any(p[0] == "farkas" and len(p) > 1 for p in parameters), parameters)
        self.assertFalse(any(p.startswith("lp-") for d in declarations for p in d["parameters"]))
        # The div and mod definitions are bare (_ th-lemma arith) axioms
        # stated as (or false l) and resolved with the unit true; the Farkas
        # conflict over them re-derives and keeps its coefficients.
        certificate = proof_certificate.export_certificate(_LIA_DIV)
        self.assertEqual(certificate["fragment"], "qf_lia")
        self.assertEqual(certificate["rule_counts"]["true-axiom"], 1)
        hints = {tuple(d["parameters"]) for d in certificate["declarations"] if d["name"] == "th-lemma"}
        self.assertIn(("arith",), hints)
        self.assertTrue(any(h[0] == "farkas" and len(h) > 1 for h in hints), hints)
        # QF_UFLIA: the sort name and the Int signatures are kept.
        certificate = proof_certificate.export_certificate(_UFLIA)
        self.assertEqual(certificate["fragment"], "qf_uflia")
        self.assertEqual({(d["name"], tuple(d["domain"]), d["range"]) for d in certificate["declarations"]
                          if d["kind"] == z3.Z3_OP_UNINTERPRETED},
                         {("a", (), "U"), ("b", (), "U"), ("x", (), "Int"), ("y", (), "Int"),
                          ("f", ("Int",), "Int"), ("g", ("U",), "Int"), ("h", ("Int",), "U"), ("q", ("Int",), "Bool")})
        self.assertLessEqual({d["parameters"][0] for d in certificate["declarations"] if d["name"] == "th-lemma"},
                             {"farkas", "bound", "implied-eq", "triangle-eq", "arith", "smt"})

    def test_legacy_integer_coefficients_are_kept_only_when_they_certify(self):
        context = z3.Context(proof=True)
        x, y = z3.Ints("x y", ctx=context)
        solver = z3.Solver(ctx=context)
        solver.set("combined_solver.ignore_solver1", True)
        # Rationally infeasible: the LP conflict's coefficients re-derive.
        solver.add(x + y <= 1, x + y >= 2)
        self.assertEqual(solver.check(), z3.unsat)
        step = next(node for node in _proof_nodes(solver.proof()) if node.decl().name() == "th-lemma")
        parameters = [str(p) for p in step.decl().params()]
        self.assertEqual(parameters[:2], ["arith", "farkas"])
        coefficients = [Fraction(p) for p in parameters[2:]]
        self.assertTrue(proof_certificate._integer_coefficients_certify(step, "farkas", coefficients))
        # Wrong coefficients, or the wrong number of them (left to the reconstructor), are not certified.
        self.assertFalse(proof_certificate._integer_coefficients_certify(step, "farkas", [Fraction(1), Fraction(2)]))
        self.assertTrue(proof_certificate._integer_coefficients_certify(step, "farkas", coefficients[:1]))
        # Indexed LP coefficients weight logical premises, not the context.
        solver = z3.Solver(ctx=context)
        solver.set("combined_solver.ignore_solver1", True)
        solver.add(z3.parse_smt2_string(proof_certificate._assertion_commands(_LIA), ctx=context))
        self.assertEqual(solver.check(), z3.unsat)
        step = next(node for node in _proof_nodes(solver.proof())
                    if node.decl().params()[:2] == ["arith", "lp-linear"]
                    and z3.is_false(node.arg(node.num_args() - 1)))
        arguments = proof_certificate._proof_arguments(step)
        self.assertEqual(len(arguments), step.num_args() - 1)
        parameters = proof_certificate._th_lemma_parameters(
            step.decl(), len(arguments) - 1, arguments[-1], integer=True)
        coefficients = [Fraction(p) for p in parameters[1:]]
        self.assertTrue(proof_certificate._integer_coefficients_certify(step, "farkas", coefficients))
        coefficients[0] *= 2
        self.assertFalse(proof_certificate._integer_coefficients_certify(step, "farkas", coefficients))
        # Real steps are never stripped: the exporter calls this over Int only.
        self.assertEqual(proof_certificate._th_lemma_parameters(_FakeDecl(["arith"]), 0, integer=True), ["arith"])
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "without a replayable theory hint"):
            proof_certificate._th_lemma_parameters(_FakeDecl(["arith"]), 0)
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "without a replayable theory hint"):
            proof_certificate._th_lemma_parameters(_FakeDecl(["arith", "gomory-cut", 1]), 1, integer=True)


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


    def test_integer_tightening_and_bound_rounding(self):
        F = Fraction
        tighten = proof_certificate.integer_tightened
        # x < 3 over Int is x - 2 <= 0; non-strict constraints are unchanged.
        self.assertEqual(tighten("<", {"x": F(1)}, F(-3)), ("<=", {"x": F(1)}, F(-2)))
        self.assertEqual(tighten("<=", {"x": F(1)}, F(-3)), ("<=", {"x": F(1)}, F(-3)))
        self.assertEqual(tighten("=", {"x": F(1)}, F(-3)), ("=", {"x": F(1)}, F(-3)))
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "fractional coefficients"):
            tighten("<", {"x": F(1, 2)}, F(-3))
        bound = proof_certificate.bound_combination_refutes
        # 3x <= 4 propagates x <= 1: the denied consequent is x >= 2, which the
        # given coefficients (1, 1) do not refute rationally.
        rounded = [(F(1), "<=", {"x": F(3)}, F(-4)), (F(1), "<=", {"x": F(-1)}, F(2))]
        self.assertFalse(proof_certificate.linear_combination_refutes(rounded))
        self.assertTrue(bound(rounded))
        # A consequent that the rounded bound does not cancel (x <= 0 denied,
        # so the propagated literal would be x >= 1) is rejected.
        self.assertFalse(bound([(F(1), "<=", {"x": F(3)}, F(-4)), (F(1), "<=", {"x": F(1)}, F(0))]))
        # Premises with a shared gcd: 2x + 2y <= 3 rounds to x + y <= 1, denying x + y >= 2.
        gcd = [(F(1), "<=", {"x": F(2), "y": F(2)}, F(-3)), (F(1), "<=", {"x": F(-1), "y": F(-1)}, F(2))]
        self.assertTrue(bound(gcd))
        # An equality is eliminated first: y = x + 1 and 2x + 2y <= 3 give 4x <= 1, so x <= 0.
        equality = [(F(1), "=", {"y": F(1), "x": F(-1)}, F(-1)), (F(1), "<=", {"x": F(2), "y": F(2)}, F(-3)),
                    (F(1), "<=", {"x": F(-1)}, F(1))]
        self.assertTrue(bound(equality))
        # A consequent over other variables, a strict row, or a negative weight is rejected.
        self.assertFalse(bound([(F(1), "<=", {"x": F(3)}, F(-4)), (F(1), "<=", {"y": F(-1)}, F(2))]))
        self.assertFalse(bound([(F(1), "<", {"x": F(3)}, F(-4)), (F(1), "<=", {"x": F(-1)}, F(2))]))
        self.assertFalse(bound([(F(-1), "<=", {"x": F(3)}, F(-4)), (F(1), "<=", {"x": F(-1)}, F(2))]))
        self.assertFalse(bound(rounded[:1]))


class TestClauseLogReplay(unittest.TestCase):
    def replay(self, source, log):
        context = z3.Context()
        assertions, fragment = proof_certificate.parse_assertions(source, context, integer=True)
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

    def test_integer_log_is_replayed_over_int_with_cut_hints(self):
        certificate = self.replay(_LIA, _LIA_LOG)
        self.assertEqual(certificate["fragment"], "qf_lia")
        sorts = {d["range"] for d in certificate["declarations"]}
        self.assertEqual(sorts, {"Bool", "Int", "Proof"})
        numerals = sorted(d["name"] for d in certificate["declarations"] if d["kind"] == z3.Z3_OP_ANUM)
        self.assertEqual(numerals, ["1", "2", "3", "4"])  # (- 2) is unary minus applied to 2
        th_lemma = [d for d in certificate["declarations"] if d["name"] == "th-lemma"]
        self.assertEqual([d["parameters"] for d in th_lemma], [["cut"]])  # no coefficients certify a cut
        self.assertEqual(certificate["rule_counts"]["th-lemma"], 1)
        self.assertEqual(certificate["rule_counts"]["asserted"], 4)
        # The Real twin of the input never takes a cut, and an Int log cannot
        # carry a fractional numeral.
        twin = _LIA.replace(" Int)", " Real)")
        for digit in "1234":
            twin = twin.replace(" %s " % digit, " %s.0 " % digit).replace(" %s)" % digit, " %s.0)" % digit)
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "cut hint over Real atoms"):
            self.replay(twin, _LIA_LOG.replace(" Int", " Real"))
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "fractional numeral in an integer"):
            self.replay(_LIA, _LIA_LOG.replace("(<= $10 3)", "(<= $10 3.5)"))
        # A cut over a Boolean literal has no linear shape.
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "not an arithmetic atom"):
            self.replay(_LIA, _LIA_LOG.replace("(cut 1 $12 1 $14", "(cut 1 false 1 $14"))
        # Relabelled as farkas, the coefficients are summed exactly and do not
        # refute the literals; over Int that drops them (Lean alone proves the
        # clause) instead of rejecting the log, as the Real slice would.
        relabelled = self.replay(_LIA, _LIA_LOG.replace("cut", "farkas"))
        self.assertEqual([d["parameters"] for d in relabelled["declarations"] if d["name"] == "th-lemma"],
                         [["farkas"]])

    def test_arith_axiom_hints_become_coefficient_free_lemmas(self):
        certificate = self.replay(_LIA_DIV, _LIA_DIV_LOG)
        self.assertEqual(certificate["fragment"], "qf_lia")
        names = {d["name"]: d for d in certificate["declarations"] if d["range"] == "Int" and d["domain"]}
        self.assertEqual(set(names), {"div", "mod", "*", "+"})
        self.assertEqual((names["div"]["kind"], names["div"]["domain"]), (z3.Z3_OP_IDIV, ["Int", "Int"]))
        self.assertEqual((names["mod"]["kind"], names["mod"]["domain"]), (z3.Z3_OP_MOD, ["Int", "Int"]))
        th_lemma = [d["parameters"] for d in certificate["declarations"] if d["name"] == "th-lemma"]
        self.assertEqual(sorted(map(tuple, th_lemma)), [("arith",), ("euf",)])
        self.assertEqual(certificate["rule_counts"]["th-lemma"], 4)  # three axioms and the euf step
        # The lemma of an arith hint is the clause of its complements: the
        # three axioms are the unit clauses themselves.
        axioms = []
        for node in certificate["nodes"]:
            declaration = certificate["declarations"][node["declaration"]]
            if declaration["parameters"] == ["arith"]:
                clause = certificate["nodes"][node["arguments"][-1]]
                axioms.append(certificate["declarations"][clause["declaration"]]["name"])
        self.assertEqual(sorted(axioms), ["<=", "=", ">="])
        # The literals must be arithmetic atoms over linear terms: a Boolean
        # literal, a division by zero or by a term, and an empty hint are
        # rejected; rem is not an SMT-LIB operator.
        for tampered, message in [
            (_LIA_DIV_LOG.replace("(arith $22)", "(arith true)"), "arith hint has no literals besides true"),
            (_LIA_DIV_LOG.replace("(arith $22)", "(arith false)"), "not an arithmetic atom"),
            (_LIA_DIV_LOG.replace("(div x 3)", "(div x 0)"), "integer div is supported only by a nonzero constant"),
            (_LIA_DIV_LOG.replace("(mod x 3)", "(mod x x)"), "integer mod is supported only by a nonzero constant"),
            (_LIA_DIV_LOG.replace("(arith $22)", "(arith)"), "arith hint has no literals"),
            (_LIA_DIV_LOG.replace("(mod x 3)", "(rem x 3)"), "unsupported operator in the clause log: rem"),
        ]:
            with self.subTest(message=message):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, message):
                    self.replay(_LIA_DIV, tampered)

    def test_real_division_axiom_hints_drop_their_true_literal(self):
        certificate = self.replay(_LRA_DIV, _LRA_DIV_LOG)
        self.assertEqual(certificate["fragment"], "qf_lra")
        th_lemma = [d["parameters"] for d in certificate["declarations"] if d["name"] == "th-lemma"]
        self.assertEqual(th_lemma, [["arith"]])
        # The lemma is the unit equality 2 * (1 / 2) = 1 itself: the true
        # literal contributes nothing to the contradictory set, so its
        # complement false is not a literal of the clause.
        axioms = []
        for node in certificate["nodes"]:
            declaration = certificate["declarations"][node["declaration"]]
            if declaration["parameters"] == ["arith"]:
                clause = certificate["nodes"][node["arguments"][-1]]
                axioms.append(certificate["declarations"][clause["declaration"]]["name"])
        self.assertEqual(axioms, ["="])
        # Nothing but true is rejected, and false is not an arithmetic atom.
        for tampered, message in [
            (_LRA_DIV_LOG.replace("(arith true $24)", "(arith true)"), "arith hint has no literals besides true"),
            (_LRA_DIV_LOG.replace("(arith true $24)", "(arith false $24)"), "not an arithmetic atom"),
        ]:
            with self.subTest(message=message):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, message):
                    self.replay(_LRA_DIV, tampered)
        # A true literal in a coefficient hint goes with its coefficient.
        padded = _LRA_LOG.replace("(farkas 1 $11 2 $17 1 $21)", "(farkas 3 true 1 $11 2 $17 1 $21)")
        parameters = [[d["parameters"] for d in self.replay(_LRA, log)["declarations"] if d["name"] == "th-lemma"]
                      for log in (_LRA_LOG, padded)]
        self.assertEqual(parameters[0], parameters[1])
        self.assertEqual(parameters[0], [["farkas", "1", "2", "1"]])

    def test_integer_bound_hints_may_round(self):
        # 3x <= 4 (logged as x <= 1 by the rewriter normally; here kept as a
        # term) propagates x <= 1: the bound hint's unit coefficients do not
        # refute the literals rationally, the rounded combination does.
        source = "(declare-const x Int)(assert (<= (* 3 x) 4))(assert (>= x 2))"
        log = """\
(declare-fun x () Int)
(define-const $1 Int (* 3 x))
(define-const $2 Bool (<= $1 4))
(assume $2)
(define-const $3 Bool (>= x 2))
(assume $3)
(define-const $4 Bool (<= x 1))
(declare-fun bound (Int Bool Int Bool) Proof)
(define-const $5 Bool (not $4))
(define-const $6 Proof (bound 1 $2 1 $5))
(infer (not $2) $4 $6)
(declare-fun farkas (Int Bool Int Bool) Proof)
(define-const $7 Proof (farkas 1 $3 1 $4))
(infer (not $3) (not $4) $7)
(declare-fun rup () Proof)
(infer rup)
"""
        certificate = self.replay(source, log)

        def parameters(certificate):
            return sorted(d["parameters"] for d in certificate["declarations"] if d["name"] == "th-lemma")

        self.assertEqual(parameters(certificate), [["bound", "1", "1"], ["farkas", "1", "1"]])
        # A farkas gets no rounding, and a bound whose consequent the rounded
        # row does not cancel is not certified either: both keep the lemma
        # but drop the coefficients, leaving the clause to Lean.
        self.assertEqual(parameters(self.replay(source, log.replace("bound", "farkas"))),
                         [["farkas"], ["farkas", "1", "1"]])
        self.assertEqual(parameters(self.replay(source, log.replace("(<= x 1)", "(<= x 0)"))),
                         [["bound"], ["farkas", "1", "1"]])
        # The Real twin rejects the same hint outright.
        real_source = "(declare-const x Real)(assert (<= (* 3.0 x) 4.0))(assert (>= x 2.0))"
        real_log = """\
(declare-fun x () Real)
(define-const $1 Real (* 3.0 x))
(define-const $2 Bool (<= $1 4.0))
(assume $2)
(define-const $3 Bool (>= x 2.0))
(assume $3)
(define-const $4 Bool (<= x 1.0))
(declare-fun bound (Int Bool Int Bool) Proof)
(define-const $5 Bool (not $4))
(define-const $6 Proof (bound 1 $2 1 $5))
(infer (not $2) $4 $6)
"""
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "bound hint coefficients do not refute"):
            self.replay(real_source, real_log)

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
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "must end in an arithmetic disequality"):
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
        # Ignored options, a check-sat-using tactic, and output queries never
        # reach the executable; the log is produced under the exporter's own
        # options and the certificate keeps the source verbatim.
        certificate = proof_certificate.export_clause_log_certificate(_CONFIGURED)
        self.assertEqual(certificate["fragment"], "propositional")
        self.assertEqual(certificate["source_smt2"], _CONFIGURED)
        result = subprocess.run(
            [sys.executable, str(_EXAMPLES / "proof_certificate.py"), "--core", "clause-log", "-"],
            input=_CONFIGURED, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)["source_smt2"], _CONFIGURED)
        # A negated unit used to make the frontend's tactic preamble log the
        # core's internal true variable as the phantom k!0; with the preamble
        # bypassed the raw log assumes the unit itself (the replay still drops
        # clauses over such phantom constants, see
        # test_phantom_literals_of_the_sat_core_are_dropped).
        log = proof_clause_log.run_clause_log(proof_certificate.default_z3_executable(),
                                              proof_certificate._assertion_commands(_UF_NEGATIVE_UNIT))
        self.assertIn("(assume (not s))", log)
        self.assertNotIn("k!", log)
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
        # Predicates over Bool alone: --core auto takes the clause log like for
        # any other theory input (euf hints), --core legacy the proof object.
        result = subprocess.run(
            [sys.executable, str(_EXAMPLES / "proof_certificate.py"), "-"],
            input=_BOOLEAN_PREDICATES, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        certificate = json.loads(result.stdout)
        self.assertEqual(certificate["fragment"], "qf_uf")
        self.assertIn("th-lemma", certificate["rule_counts"])
        self.assertNotIn("monotonicity", certificate["rule_counts"])
        self.assertNotIn("!", json.dumps(certificate["declarations"]))
        result = subprocess.run(
            [sys.executable, str(_EXAMPLES / "proof_certificate.py"), "--core", "legacy", "-"],
            input=_BOOLEAN_PREDICATES, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        certificate = json.loads(result.stdout)
        self.assertIn("monotonicity", certificate["rule_counts"])
        self.assertNotIn("th-lemma", certificate["rule_counts"])

    @unittest.skipUnless(_z3_available(), "the z3 executable is required for the clause log")
    def test_the_frontend_tactic_preamble_is_bypassed(self):
        # For a non-incremental check-sat the frontend's combined solver runs
        # the tactic of the input's logic before either core. Its elim-uncnstr
        # pass replaces a subterm whose variable occurs nowhere else by a fresh
        # k!N constant (the smt core's proof names it by intro-def), and its
        # passes Ackermannize predicates over Bool alone; neither can be tied
        # to the input. Both exporters send the assertions to the core directly.
        bypass = "(set-option :combined_solver.ignore_solver1 true)\n"
        self.assertTrue(proof_certificate._NO_PREPROCESSING.startswith(bypass))
        z3_executable = proof_certificate.default_z3_executable()
        for source, fragment in ((_SINGLE_OCCURRENCE, "qf_uflra"), (_BOOLEAN_PREDICATES, "qf_uf")):
            with self.subTest(source=source):
                commands = proof_certificate._assertion_commands(source)
                with patch.object(proof_clause_log, "_NO_PREPROCESSING",
                                  proof_certificate._NO_PREPROCESSING.replace(bypass, "")):
                    tactic_log = proof_clause_log.run_clause_log(z3_executable, commands)
                # This half pins Z3's preamble (elim-uncnstr, Ackermannization),
                # not the exporter: if it fails, the preamble no longer rewrites
                # this input and the bypass needs a new witness.
                self.assertTrue("!" in tactic_log or "(infer" not in tactic_log,
                                "the tactic preamble (elim-uncnstr / Ackermannization) left the input's symbols "
                                "intact; pick another witness for the bypass:\n" + tactic_log)
                log = proof_clause_log.run_clause_log(z3_executable, commands)
                self.assertIn("(infer", log)
                self.assertNotIn("!", log)
                certificate = proof_certificate.export_clause_log_certificate(source)
                self.assertEqual(certificate["fragment"], fragment)
                self.assertIn("th-lemma", certificate["rule_counts"])
                self.assertNotIn("!", json.dumps(certificate["declarations"]))
        # The same input through the smt core: the default solver's proof has
        # the intro-def step, the exporter's has none.
        context = z3.Context(proof=True)
        solver = z3.Solver(ctx=context)
        solver.add(z3.parse_smt2_string(_SINGLE_OCCURRENCE, ctx=context))
        self.assertEqual(solver.check(), z3.unsat)
        self.assertIn("intro-def", solver.proof().sexpr())
        certificate = proof_certificate.export_certificate(_SINGLE_OCCURRENCE)
        self.assertEqual(certificate["fragment"], "qf_uflra")
        self.assertNotIn("intro-def", certificate["rule_counts"])
        self.assertIn("monotonicity", certificate["rule_counts"])
        self.assertNotIn("!", json.dumps(certificate["declarations"]))

    @unittest.skipUnless(_z3_available(), "the z3 executable is required for the clause log")
    def test_executable_exports_integer_arithmetic_with_uninterpreted_functions(self):
        # QF_UFLIA through the clause log: the sort name is kept, the functions
        # keep their Int arguments and results, numerals are Int, and the
        # integer solver's hints appear next to the euf congruences (the
        # gcd conflict through (f (g a)) is a cut, kept without coefficients).
        certificate = proof_certificate.export_clause_log_certificate(_UFLIA)
        self.assertEqual(certificate["fragment"], "qf_uflia")
        declarations = certificate["declarations"]
        self.assertEqual({d["range"] for d in declarations}, {"Bool", "Int", "U", "Proof"})
        self.assertEqual({(d["name"], tuple(d["domain"]), d["range"]) for d in declarations
                          if d["kind"] == z3.Z3_OP_UNINTERPRETED},
                         {("a", (), "U"), ("b", (), "U"), ("x", (), "Int"), ("y", (), "Int"),
                          ("f", ("Int",), "Int"), ("g", ("U",), "Int"), ("h", ("Int",), "U"), ("q", ("Int",), "Bool")})
        self.assertTrue(all(Fraction(d["name"]).denominator == 1 for d in declarations if d["kind"] == z3.Z3_OP_ANUM))
        hints = {}
        for declaration in declarations:
            if declaration["name"] == "th-lemma":
                hints.setdefault(declaration["parameters"][0], []).append(declaration["parameters"][1:])
        self.assertLessEqual({"cut", "euf", "farkas"}, set(hints))
        self.assertEqual(hints["cut"], [[]])
        self.assertTrue(all(Fraction(c) > 0 for c in sum(hints["farkas"], [])))
        # --core auto takes the clause log; --core legacy the proof object.
        result = subprocess.run(
            [sys.executable, str(_EXAMPLES / "proof_certificate.py"), "-"],
            input=_UFLIA, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)["fragment"], "qf_uflia")
        result = subprocess.run(
            [sys.executable, str(_EXAMPLES / "proof_certificate.py"), "--core", "legacy", "-"],
            input=_UFLIA, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        certificate = json.loads(result.stdout)
        self.assertEqual(certificate["fragment"], "qf_uflia")
        self.assertIn("monotonicity", certificate["rule_counts"])  # the legacy core's congruences
        self.assertEqual({d["range"] for d in certificate["declarations"]}, {"Bool", "Int", "U", "Proof"})


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
