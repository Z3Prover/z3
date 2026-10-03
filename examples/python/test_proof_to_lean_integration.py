############################################
# Copyright (c) 2026 Microsoft Corporation
#
# End-to-end tests requiring both native Z3 bindings and the pinned Lean toolchain.
############################################
import hashlib
import itertools
import json
import os
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
import proof_preprocessing
import proof_to_lean
from test_proof_to_lean import (
    BRANCHING, CLAUSE, CONJUNCTION, DEF_AXIOM_CLAUSES, LITERAL, REWRITE, STRUCTURAL,
    NESTED, XOR, make_certificate,
)


class TestProofToLeanIntegration(unittest.TestCase):
    def check(self, source, certificate):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "checked proof.lean"
            proof_to_lean.check_and_write(source, certificate, output)
            text = output.read_text()
            statement = text.split("theorem unsat", 1)[1].split(": False :=", 1)[0]
            self.assertEqual(statement.count("    (_h"), len(certificate["assertions"]))
            self.assertNotIn("_hyp", statement)
            self.assertNotIn("Decidable", statement)
            namespace = "Z3Proofs.NativeCertificate.p" + hashlib.sha256(source.encode()).hexdigest()
            theorem_rules = {z3.Z3_OP_PR_REWRITE: "rewrite", z3.Z3_OP_PR_DEF_AXIOM: "def_axiom"}
            theorems = ["unsat"]
            for node, raw in enumerate(certificate["nodes"]):
                rule = certificate["declarations"][raw["declaration"]]["kind"]
                if rule in theorem_rules:
                    theorems.append("%s_%d" % (theorem_rules[rule], node))
            output.write_text(text + "".join(
                "\n#print axioms %s.%s\n" % (namespace, theorem) for theorem in theorems))
            result = subprocess.run(
                [str(proof_to_lean._CHECK_LEAN), str(output)], text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout.count("does not depend on any axioms"), len(theorems))
            return text

    def test_real_exported_refutations_are_checked_without_axioms(self):
        for source in [LITERAL, CLAUSE, REWRITE, CONJUNCTION, STRUCTURAL, BRANCHING, XOR, NESTED,
                       "(assert false)", "(assert (not true))"]:
            with self.subTest(source=source):
                self.check(source, proof_certificate.export_certificate(source))

    def test_documented_boolean_rewrite_example(self):
        source = (_EXAMPLES.parents[1] / "lean" / "examples" / "boolean_rewrite.smt2").read_text()
        certificate = proof_certificate.export_certificate(source)
        self.assertTrue({"asserted", "mp", "rewrite"} <= set(certificate["rule_counts"]))
        with patch.object(z3.Solver, "check", side_effect=AssertionError("solver oracle invoked")):
            self.check(source, certificate)

    def test_documented_structural_boolean_example(self):
        source = (_EXAMPLES.parents[1] / "lean" / "examples" / "boolean_structural.smt2").read_text()
        certificate = proof_certificate.export_certificate(source)
        self.assertTrue({"trans", "monotonicity", "not-or-elim"} <= set(certificate["rule_counts"]))
        with patch.object(z3.Solver, "check", side_effect=AssertionError("solver oracle invoked")):
            self.check(source, certificate)

    def test_documented_branching_boolean_example(self):
        source = (_EXAMPLES.parents[1] / "lean" / "examples" / "boolean_branching.smt2").read_text()
        certificate = proof_certificate.export_certificate(source)
        self.assertTrue({"hypothesis", "lemma"} <= set(certificate["rule_counts"]))
        with patch.object(z3.Solver, "check", side_effect=AssertionError("solver oracle invoked")):
            self.check(source, certificate)

    def test_documented_def_axiom_xor_example(self):
        source = (_EXAMPLES.parents[1] / "lean" / "examples" / "boolean_def_axiom.smt2").read_text()
        certificate = proof_certificate.export_certificate(source)
        self.assertGreater(certificate["rule_counts"]["def-axiom"], 0)
        with patch.object(z3.Solver, "check", side_effect=AssertionError("solver oracle invoked")):
            self.check(source, certificate)

    def test_preprocessing_audit_requires_an_essential_equality_and_search(self):
        source = (_EXAMPLES.parents[1] / "lean" / "examples" / "boolean_solve_eqs.smt2").read_text()
        context = z3.Context()
        assertions = proof_certificate.parse_propositional_assertions(source, context)
        without_equality = z3.SimpleSolver(ctx=context)
        without_equality.add(list(assertions)[1:])
        self.assertEqual(without_equality.check(), z3.sat)
        goal = z3.Goal(ctx=context)
        goal.add(assertions)
        reduced = z3.Tactic("solve-eqs", ctx=context)(goal)
        self.assertEqual(len(reduced), 1)
        self.assertEqual(len(reduced[0]), 4)
        self.assertFalse(reduced[0].inconsistent())

        report = proof_preprocessing.audit_preprocessing(source, require_search=True)
        self.assertTrue(report["complete"], report)
        self.assertEqual(len(report["runs"]), 4)
        for run in report["runs"]:
            with self.subTest(pipeline=run["pipeline"], proofs=run["proofs_enabled"]):
                self.assertEqual(run["result"], "unsat")
                self.assertTrue(run["branching_search_observed"])
                self.assertTrue(run["preprocessing_observed"])
                self.assertEqual(run["preprocessing_observed"],
                                 run["statistics"].get("solve-eqs-elim-vars", 0) > 0)
                if not run["proofs_enabled"]:
                    self.assertTrue(run["preprocessing_observed"])
                    self.assertEqual(run["proof_status"], "disabled")
                else:
                    self.assertEqual(run["proof_status"], "lean-checked")
                self.assertFalse(run["diagnostics"])

    def test_preprocessing_audit_also_covers_preprocessing_only_refutations(self):
        source = (_EXAMPLES.parents[1] / "lean" / "examples" / "unit_resolution.smt2").read_text()
        report = proof_preprocessing.audit_preprocessing(source)
        self.assertTrue(report["complete"], report)
        for run in report["runs"]:
            self.assertEqual(run["result"], "unsat")
            self.assertTrue(run["preprocessing_observed"])
            self.assertFalse(run["branching_search_observed"])
            self.assertEqual(run["proof_status"], "lean-checked" if run["proofs_enabled"] else "disabled")
            self.assertFalse(run["diagnostics"])

    def test_preprocessing_audit_cli_never_reports_bypasses_as_success(self):
        source = (_EXAMPLES.parents[1] / "lean" / "examples" / "boolean_solve_eqs.smt2").read_text()
        with tempfile.TemporaryDirectory() as directory:
            original = Path(directory) / "input with spaces.smt2"
            original.write_text(source)
            command = [sys.executable, str(_EXAMPLES / "proof_preprocessing.py"),
                       str(original), "--require-search"]
            result = subprocess.run(command, capture_output=True, text=True)
            report = json.loads(result.stdout)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertTrue(report["complete"])
            self.assertEqual(len(report["runs"]), 4)
            result = subprocess.run(command + ["--timeout-ms", "0"], capture_output=True, text=True)
            self.assertEqual(result.returncode, 2)
            self.assertIn("positive integer", result.stderr)
            self.assertEqual(original.read_text(), source)
            self.assertEqual(list(Path(directory).iterdir()), [original])

    def test_iff_constant_rules_are_axiom_free(self):
        source = "(declare-const p Bool)(declare-const q Bool)"
        source += "(assert (and p q))(assert (not (and p q)))(assert true)"
        certificate = make_certificate(source, [
            ("iff-true", [0], "(= (and p q) true)"),
            ("iff-false", [1], "(= (and p q) false)"),
            ("symm", [3], "(= true (and p q))"),
            ("trans", [5, 4], "(= true false)"),
            ("mp", [2, 6], "false"),
        ])
        self.check(source, certificate)
        for declaration in certificate["declarations"]:
            if declaration["kind"] == z3.Z3_OP_EQ:
                declaration["kind"], declaration["name"] = z3.Z3_OP_IFF, "iff"
        self.check(source, certificate)

    def test_iff_constant_rules_preserve_hypothesis_scope(self):
        source = LITERAL + "(assert true)"
        self.check(source, make_certificate(source, [
            ("hypothesis", [], "p"),
            ("iff-true", [3], "(= p true)"),
            ("symm", [4], "(= true p)"),
            ("mp", [2, 5], "p"),
            ("unit-resolution", [1, 6], "false"),
            ("lemma", [7], "(not p)"),
            ("unit-resolution", [0, 8], "false"),
        ]))
        self.check(LITERAL, make_certificate(LITERAL, [
            ("hypothesis", [], "(not p)"),
            ("iff-false", [2], "(= p false)"),
            ("mp", [0, 3], "false"),
            ("lemma", [4], "(not (not p))"),
            ("unit-resolution", [5, 1], "false"),
        ]))

    def test_solve_eqs_native_boolean_proof_chains(self):
        prefix = "".join("(declare-const %s Bool)" % atom for atom in "pqrs")
        cases = [
            "(assert (= p q))(assert (= q r))(assert (or p s))(assert (not r))(assert (not s))",
            "(assert (= (not q) p))(assert (not q))(assert (not p))",
            "(assert (= p (or q r)))(assert (not q))(assert (not r))(assert p)",
            "(assert (= p q))(assert (= q p))(assert p)(assert (not q))",
            "(assert (= p (ite q r s)))(assert q)(assert (not r))(assert p)",
            "(assert (and p (not p)))",
            "(assert (not (or (not p) q)))(assert (or (not p) q))",
        ]
        for pipeline, constraints in itertools.product(("simplifier", "tactic"), cases):
            with self.subTest(pipeline=pipeline, constraints=constraints):
                source = prefix + constraints
                context = z3.Context(proof=True)
                assertions = proof_certificate.parse_propositional_assertions(source, context)
                if pipeline == "simplifier":
                    solver = z3.Simplifier("solve-eqs", ctx=context).add(z3.SimpleSolver(ctx=context))
                else:
                    solver = z3.Then(z3.Tactic("solve-eqs", ctx=context), z3.Tactic("smt", ctx=context)).solver()
                solver.add(assertions)
                self.assertEqual(solver.check(), z3.unsat)
                self.check(source, proof_certificate._certificate_from_proof(source, assertions, solver.proof()))

    def test_solve_eqs_incremental_proofs_and_models(self):
        prefix = "(declare-const p Bool)(declare-const q Bool)(assert (= p q))"
        source = prefix + "(assert p)(assert (not q))"
        for pipeline, mode in itertools.product(
                ("simplifier", "tactic"), ("append", "push-pop", "assumptions", "translate")):
            with self.subTest(pipeline=pipeline, mode=mode):
                context = z3.Context(proof=True)
                assertions = proof_certificate.parse_propositional_assertions(source, context)
                if pipeline == "simplifier":
                    solver = z3.Simplifier("solve-eqs", ctx=context).add(z3.SimpleSolver(ctx=context))
                else:
                    solver = z3.Then(z3.Tactic("solve-eqs", ctx=context), z3.Tactic("smt", ctx=context)).solver()
                solver.add(assertions[0])
                self.assertEqual(solver.check(), z3.sat)
                self.assertTrue(z3.is_true(solver.model().eval(assertions[0], model_completion=True)))
                if mode == "translate":
                    target = z3.Context(proof=True)
                    solver = solver.translate(target)
                    assertions = proof_certificate.parse_propositional_assertions(source, target)
                if mode == "push-pop":
                    solver.push()
                if mode == "assumptions":
                    result = solver.check(assertions[1], assertions[2])
                else:
                    solver.add(assertions[1], assertions[2])
                    result = solver.check()
                self.assertEqual(result, z3.unsat)
                self.check(source, proof_certificate._certificate_from_proof(source, assertions, solver.proof()))
                if mode == "push-pop":
                    solver.pop()
                    self.assertEqual(solver.check(), z3.sat)
                    solver.push()
                    flipped = [assertions[0], z3.Not(assertions[1]), assertions[2].arg(0)]
                    solver.add(flipped[1:])
                    self.assertEqual(solver.check(), z3.unsat)
                    flipped_source = prefix + "(assert (not p))(assert q)"
                    self.check(flipped_source, proof_certificate._certificate_from_proof(
                        flipped_source, flipped, solver.proof()))
                    solver.pop()
                    self.assertEqual(solver.check(), z3.sat)
                if mode == "assumptions":
                    self.assertEqual(solver.check(), z3.sat)

    def test_solve_eqs_tracked_proofs_do_not_introduce_proxy_assumptions(self):
        for count, translate in itertools.product((1, 2), (False, True)):
            with self.subTest(count=count, translate=translate):
                source = "".join("(declare-const %s Bool)" % atom for atom in "pqrab")
                if count == 1:
                    source += "(assert (=> a (= p q)))(assert a)(assert p)(assert (not q))"
                    tracked, start = [(0, 1)], 2
                else:
                    source += "(assert (=> a (= p q)))(assert (=> b (= q r)))"
                    source += "(assert a)(assert b)(assert p)(assert (not r))"
                    tracked, start = [(0, 2), (1, 3)], 4
                context = z3.Context(proof=True)
                assertions = proof_certificate.parse_propositional_assertions(source, context)
                solver = z3.Simplifier("solve-eqs", ctx=context).add(z3.SimpleSolver(ctx=context))
                for fact, label in tracked:
                    solver.assert_and_track(assertions[fact].arg(1), assertions[label])
                self.assertEqual(solver.check(), z3.sat)
                if translate:
                    target = z3.Context(proof=True)
                    solver = solver.translate(target)
                    assertions = proof_certificate.parse_propositional_assertions(source, target)
                solver.add(list(assertions)[start:])
                self.assertEqual(solver.check(), z3.unsat)
                self.assertEqual({str(label) for label in solver.unsat_core()}, set("ab"[:count]))
                self.check(source, proof_certificate._certificate_from_proof(source, assertions, solver.proof()))

    def test_solve_eqs_scoped_tracking_literals_are_removed_on_pop(self):
        source = "".join("(declare-const %s Bool)" % atom for atom in "pqabc")
        source += "(assert (=> a (= p q)))(assert a)"
        source += "(assert (=> b p))(assert b)(assert (=> c (not q)))(assert c)"
        context = z3.Context(proof=True)
        assertions = proof_certificate.parse_propositional_assertions(source, context)
        solver = z3.Simplifier("solve-eqs", ctx=context).add(z3.SimpleSolver(ctx=context))
        solver.assert_and_track(assertions[0].arg(1), assertions[1])
        self.assertEqual(solver.check(), z3.sat)
        solver.push()
        solver.assert_and_track(assertions[2].arg(1), assertions[3])
        solver.assert_and_track(assertions[4].arg(1), assertions[5])
        self.assertEqual(solver.check(), z3.unsat)
        self.assertEqual({str(label) for label in solver.unsat_core()}, set("abc"))
        self.check(source, proof_certificate._certificate_from_proof(source, assertions, solver.proof()))
        solver.pop()
        self.assertEqual(solver.check(z3.Not(assertions[3]), z3.Not(assertions[5])), z3.sat)

    def test_solve_eqs_tactic_tracked_proof(self):
        source = "(declare-const p Bool)(declare-const q Bool)(declare-const a Bool)"
        source += "(assert (=> a (= p q)))(assert a)(assert p)(assert (not q))"
        context = z3.Context(proof=True)
        assertions = proof_certificate.parse_propositional_assertions(source, context)
        solver = z3.Then(z3.Tactic("solve-eqs", ctx=context), z3.Tactic("smt", ctx=context)).solver()
        solver.assert_and_track(assertions[0].arg(1), assertions[1])
        self.assertEqual(solver.check(), z3.sat)
        solver.add(assertions[2], assertions[3])
        self.assertEqual(solver.check(), z3.unsat)
        self.check(source, proof_certificate._certificate_from_proof(source, assertions, solver.proof()))

    def test_solve_eqs_leaves_unproved_extraction_schemes_unchanged(self):
        context = z3.Context(proof=True)
        x, y, z = z3.Ints("x y z", ctx=context)
        a, b = z3.BitVecs("a b", 8, ctx=context)
        array = z3.Array("array", z3.IntSort(ctx=context), z3.IntSort(ctx=context))
        p = z3.Bool("p", ctx=context)
        expressions = [
            x + y == 0, a + b == 0, x % 3 == 1,
            z3.If(p, x == y, x == z), z3.Or(x == y, p),
            z3.ForAll(x, z3.Implies(x > 0, z3.Select(array, x) == x + 1)),
        ]
        for expression in expressions:
            with self.subTest(expression=expression):
                goal = z3.Goal(proofs=True, ctx=context)
                goal.add(expression)
                result = z3.Tactic("solve-eqs", ctx=context)(goal)
                self.assertEqual(len(result), 1)
                self.assertEqual(len(result[0]), 1)
                self.assertTrue(result[0][0].eq(expression))

    def test_solve_eqs_respects_the_goal_proof_setting(self):
        context = z3.Context(proof=True)
        x, y = z3.Ints("x y", ctx=context)
        goal = z3.Goal(proofs=False, ctx=context)
        goal.add(x + y == 0)
        result = z3.Tactic("solve-eqs", ctx=context)(goal)
        self.assertEqual(len(result), 1)
        self.assertEqual(len(result[0]), 0)

    def test_all_def_axiom_gate_schemas_and_literal_orders(self):
        source = "(declare-const p Bool)(declare-const q Bool)(declare-const r Bool)"
        source += "(assert (or p q r))(assert false)"
        steps = []
        context = z3.Context()
        for clause in DEF_AXIOM_CLAUSES:
            parsed = proof_certificate.parse_propositional_assertions(
                source + "(assert %s)" % clause, context)[-1]
            for arguments in [parsed.children(), list(reversed(parsed.children()))]:
                steps.append(("def-axiom", [], "(or %s)" % " ".join(arg.sexpr() for arg in arguments)))
        steps.append(("asserted", [], "false"))
        certificate = make_certificate(source, steps)
        text = self.check(source, certificate)
        self.assertEqual(text.count("private theorem def_axiom_"), 2 * len(DEF_AXIOM_CLAUSES))
        self.assertNotIn("cases ", text)
        self.assertNotIn("of_decide_eq_true", text)
        for declaration in certificate["declarations"]:
            if declaration["kind"] == z3.Z3_OP_EQ:
                declaration["kind"], declaration["name"] = z3.Z3_OP_IFF, "iff"
        self.check(source, certificate)

    def test_def_axiom_negated_compound_repeated_and_constant_operands(self):
        clauses = [
            "true", "(not false)", "(or false true)", "(or true false)",
            "(or (not (and p)) p)", "(or (and p) (not p))",
            "(or (not (or p)) p)", "(or (or p) (not p))",
            "(or (not (and p p q)) p)", "(or (and p p q) (not p) (not q))",
            "(or (not (and true p)) p)", "(or (and true p) (not p))",
            "(or (not (or false p)) p)", "(or (or false p) (not p))",
            "(or (not (and (not p) (not q))) (not p))",
            "(or (and (not p) (not q)) p q)",
            "(or (= (not p) (not q)) p q)",
            "(or (not (= (not p) (not q))) p (not q))",
            "(or (not (xor (not p) q)) p (not q))",
            "(or (ite (not p) q r) p (not q))",
            "(or (not (ite (not p) q r)) (not p) r)",
            "(or (not (=> (not p) (not q))) p (not q))",
            "(or (not (and (or p q) r)) (or p q))",
            "(or (or (and p q) r) (not (and p q)))",
            "(or (not (not (not p))) p)",
            "(or (not (not p)) (not (not (not p))))",
            "(or r (not (and p q)) p p false)",
        ]
        source = "(declare-const p Bool)(declare-const q Bool)(declare-const r Bool)"
        source += "(assert (or p q r))(assert false)"
        steps = [("def-axiom", [], clause) for clause in clauses]
        steps.append(("asserted", [], "false"))
        self.check(source, make_certificate(source, steps))

    def test_def_axiom_shared_with_scoped_proofs(self):
        source = "(declare-const p Bool)(declare-const q Bool)"
        source += "(assert (= p q))(assert p)(assert (not q))"
        certificate = make_certificate(source, [
            ("def-axiom", [], "(or (not (= p q)) (not p) q)"),
            ("hypothesis", [], "p"),
            ("unit-resolution", [3, 0, 4], "q"),
            ("unit-resolution", [5, 2], "false"),
            ("lemma", [6], "(not p)"),
            ("unit-resolution", [3, 0, 1], "q"),
            ("unit-resolution", [7, 1], "false"),
        ])
        text = self.check(source, certificate)
        self.assertEqual(text.count("private theorem def_axiom_"), 1)

    def test_large_def_axioms_do_not_enumerate_atom_assignments(self):
        size = 48
        atoms = ["p%d" % index for index in range(size)]
        source = "".join("(declare-const %s Bool)" % atom for atom in atoms)
        source += "(assert (or %s))(assert false)" % " ".join(atoms)
        conjunction, disjunction = "(and %s)" % " ".join(atoms), "(or %s)" % " ".join(atoms)
        clauses = [
            "(or %s %s)" % (conjunction, " ".join("(not %s)" % atom for atom in atoms)),
            "(or (not %s) %s)" % (disjunction, " ".join(atoms)),
            "(or (= %s %s) (not %s) (not %s))" % (
                conjunction, disjunction, conjunction, disjunction),
        ]
        steps = [("def-axiom", [], clause) for clause in clauses]
        steps.append(("asserted", [], "false"))
        text = self.check(source, make_certificate(source, steps))
        self.assertNotIn("cases ", text)
        self.assertNotIn("of_decide_eq_true", text)
        self.assertLess(len(text), 150_000)

    def test_lean_rechecks_def_axiom_lemmas_even_when_unused(self):
        source = "(declare-const p Bool)(assert p)(assert false)"
        certificate = make_certificate(source, [
            ("def-axiom", [], "(or p (not p))"), ("asserted", [], "false"),
        ])
        generator = proof_to_lean._def_axiom_lemma

        def corrupt_lemma(*args):
            lines, support, term = generator(*args)
            lines[-1] = "  True.intro"
            return lines, support, term

        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "proof.lean"
            output.write_text("previous artifact")
            with patch.object(proof_to_lean, "_def_axiom_lemma", side_effect=corrupt_lemma):
                with self.assertRaises(subprocess.CalledProcessError):
                    proof_to_lean.check_and_write(source, certificate, output)
            self.assertEqual(output.read_text(), "previous artifact")
            self.assertEqual(list(Path(directory).iterdir()), [output])

    def test_native_multiple_learned_clauses(self):
        for size in [3, 4]:
            with self.subTest(size=size):
                atoms = ["p%d" % index for index in range(size)]
                source = "".join("(declare-const %s Bool)" % atom for atom in atoms)
                for signs in itertools.product([False, True], repeat=size):
                    literals = [atom if positive else "(not %s)" % atom
                                for atom, positive in zip(atoms, signs)]
                    source += "(assert (or %s))" % " ".join(literals)
                certificate = proof_certificate.export_certificate(source)
                self.assertGreater(certificate["rule_counts"]["lemma"], 1)
                self.check(source, certificate)

    def test_lemma_single_hypothesis_orientations_and_compound_literals(self):
        for hypothesis, conclusion, premises in [
            ("p", "(not p)", [0, 2]),
            ("(not p)", "p", [0, 2]),
            ("(not p)", "(not (not p))", [0, 2]),
            ("(not (not p))", "(not p)", [0, 2]),
            ("(not (or p q))", "(or p q)", [2, 0]),
            ("(or p q)", "(not (or p q))", [0, 2]),
            ("false", "(not false)", [0, 2]),
            ("(not false)", "false", [2, 0]),
        ]:
            with self.subTest(hypothesis=hypothesis, conclusion=conclusion):
                source = "(declare-const p Bool)(declare-const q Bool)"
                source += "(assert %s)(assert (not %s))" % (conclusion, conclusion)
                self.check(source, make_certificate(source, [
                    ("hypothesis", [], hypothesis),
                    ("unit-resolution", premises, "false"),
                    ("lemma", [3], conclusion),
                    ("unit-resolution", [1, 4], "false"),
                ]))

    def test_lemma_clauses_allow_reordering_factoring_and_weakening(self):
        source = "".join("(declare-const %s Bool)" % atom for atom in "pqr")
        source += "(assert (or p q))(assert (not p))(assert (not q))(assert (not r))"
        for conclusion, units in [
            ("(or q p)", [1, 2]), ("(or p p q)", [1, 2]),
            ("(or false q p)", [1, 2]), ("(or p q false)", [1, 2]),
            ("(or r q p)", [1, 2, 3]),
        ]:
            with self.subTest(conclusion=conclusion):
                self.check(source, make_certificate(source, [
                    ("hypothesis", [], "(not p)"), ("hypothesis", [], "(not q)"),
                    ("unit-resolution", [0, 4, 5], "false"),
                    ("lemma", [6], conclusion),
                    ("unit-resolution", [7] + units, "false"),
                ]))

    def test_repeated_hypotheses_share_one_parameter(self):
        certificate = make_certificate(LITERAL, [
            ("hypothesis", [], "p"), ("hypothesis", [], "p"),
            ("unit-resolution", [1, 2, 3], "false"),
            ("lemma", [4], "(not p)"),
            ("unit-resolution", [5, 0], "false"),
        ])
        text = self.check(LITERAL, certificate)
        lemma = certificate["nodes"][certificate["proof"]]["arguments"][0]
        conflict = certificate["nodes"][lemma]["arguments"][0]
        header = next(line for line in text.splitlines() if line.startswith("  let _step_%d " % conflict))
        self.assertEqual(header.count("(_hyp"), 1)
        self.assertNotIn("Decidable", text)

    def test_lemma_with_mixed_polarities(self):
        source = "(declare-const p Bool)(declare-const q Bool)"
        source += "(assert (or (not p) q))(assert p)(assert (not q))"
        self.check(source, make_certificate(source, [
            ("hypothesis", [], "(not q)"), ("hypothesis", [], "p"),
            ("unit-resolution", [0, 3, 4], "false"),
            ("lemma", [5], "(or q (not p))"),
            ("unit-resolution", [6, 1, 2], "false"),
        ]))

    def test_nested_lemmas_and_shared_open_subproofs(self):
        source = "(declare-const p Bool)(declare-const q Bool)"
        source += "(assert (or (not p) (not q)))(assert p)(assert q)"
        certificate = make_certificate(source, [
            ("hypothesis", [], "p"), ("hypothesis", [], "q"),
            ("unit-resolution", [0, 3, 4], "false"),
            ("lemma", [5], "(or (not p) (not q))"),
            ("lemma", [5], "(or (not q) (not p))"),
            ("unit-resolution", [6, 3, 2], "false"),
            ("lemma", [8], "(not p)"),
            ("unit-resolution", [7, 1], "(not q)"),
            ("unit-resolution", [9, 1], "false"),
        ])
        text = self.check(source, certificate)
        self.assertEqual(sum(line.startswith("  let _step_") for line in text.splitlines()),
                         sum(certificate["rule_counts"].values()))
        self.assertNotIn("cases _d", text)

    def test_scoped_structural_proofs_and_double_negation(self):
        source = "".join("(declare-const %s Bool)" % atom for atom in "pqr")
        source += "(assert (= p q))(assert (and p r))(assert (not q))"
        self.check(source, make_certificate(source, [
            ("hypothesis", [], "(= p q)"),
            ("symm", [3], "(= q p)"), ("symm", [4], "(= p q)"),
            ("refl", [], "(= q q)"), ("trans", [5, 6], "(= p q)"),
            ("monotonicity", [7], "(= (and p r) (and q r))"),
            ("hypothesis", [], "(and p r)"), ("mp", [9, 8], "(and q r)"),
            ("and-elim", [10], "q"), ("unit-resolution", [2, 11], "false"),
            ("lemma", [12], "(or (not (= p q)) (not (and p r)))"),
            ("unit-resolution", [13, 0, 1], "false"),
        ]))
        source = "(declare-const p Bool)(declare-const q Bool)"
        source += "(assert (not p))(assert (not (or (not p) q)))"
        self.check(source, make_certificate(source, [
            ("hypothesis", [], "(not (or (not p) q))"),
            ("not-or-elim", [2], "p"), ("unit-resolution", [0, 3], "false"),
            ("lemma", [4], "(or (not p) q)"),
            ("unit-resolution", [1, 5], "false"),
        ]))

    def test_large_lemma_does_not_enumerate_truth_assignments(self):
        size = 24
        source = "".join("(declare-const p%d Bool)" % index for index in range(size))
        clause = "(or %s)" % " ".join("(not p%d)" % index for index in range(size))
        source += "(assert %s)" % clause
        source += "".join("(assert p%d)" % index for index in range(size))
        steps = [("hypothesis", [], "p%d" % index) for index in range(size)]
        first_hypothesis = size + 1
        conflict = first_hypothesis + size
        steps.extend([
            ("unit-resolution", [0] + list(range(first_hypothesis, conflict)), "false"),
            ("lemma", [conflict], clause),
            ("unit-resolution", [conflict + 1] + list(range(1, size + 1)), "false"),
        ])
        text = self.check(source, make_certificate(source, steps))
        self.assertNotIn("cases _d", text)
        self.assertLess(len(text), 50_000)

    def test_closed_lemma_and_unused_open_hypothesis(self):
        source = "(declare-const p Bool)(assert p)(assert false)"
        text = self.check(source, make_certificate(source, [
            ("hypothesis", [], "false"),
            ("lemma", [1], "(or p (not p))"),
            ("lemma", [1], "false"),
        ]))
        self.assertNotIn("Decidable", text)

    def test_reflexivity_symmetry_and_transitivity_chains(self):
        source = "".join("(declare-const %s Bool)" % atom for atom in "pqr")
        source += "(assert (= p q))(assert (= q r))(assert p)(assert (not r))"
        certificate = make_certificate(source, [
            ("refl", [], "(= p p)"),
            ("symm", [0], "(= q p)"),
            ("symm", [5], "(= p q)"),
            ("trans", [4, 6], "(= p q)"),
            ("trans", [7, 1], "(= p r)"),
            ("mp", [2, 8], "r"),
            ("unit-resolution", [9, 3], "false"),
        ])
        text = self.check(source, certificate)
        self.assertIn("Iff.refl", text)
        self.assertIn("Iff.symm", text)
        self.assertIn("Iff.trans", text)
        self.assertNotIn("cases _d", text)

    def test_transitivity_star_paths_and_redundant_edges(self):
        cases = [
            ([2, 0, 1], "p", "s"), ([1, 0, 2], "s", "p"),
            ([2, 0, 1, 0, 3, 6], "p", "s"), ([0, 1, 2, 4, 5], "p", "s"),
            ([6, 3, 0], "p", "q"), ([0], "q", "p"),
            ([], "p", "p"), ([6], "p", "p"), ([3], "p", "p"),
        ]
        for premises, left, right in cases:
            with self.subTest(premises=premises, left=left, right=right):
                source = "".join("(declare-const %s Bool)" % atom for atom in "pqrstu")
                source += """\
(assert (= p q))(assert (= r q))(assert (= r s))(assert (= p p))
(assert (= s t))(assert (= t q))(assert (= u u))
"""
                source += "(assert %s)(assert (not %s))" % (left, right)
                certificate = make_certificate(source, [
                    ("trans*", premises, "(= %s %s)" % (left, right)),
                    ("mp", [7, 9], right),
                    ("unit-resolution", [8, 10], "false"),
                ])
                with patch.object(z3.Solver, "check", side_effect=AssertionError("solver oracle invoked")):
                    text = self.check(source, certificate)
                self.assertNotIn("Decidable", text)
                self.assertNotIn("cases ", text)

    def test_transitivity_star_replays_a_condensed_native_chain(self):
        certificate = proof_certificate.export_certificate(STRUCTURAL)
        self.assertGreater(certificate["rule_counts"]["trans"], 0)
        for declaration in certificate["declarations"]:
            if declaration["kind"] == z3.Z3_OP_PR_TRANSITIVITY:
                declaration["kind"], declaration["name"] = z3.Z3_OP_PR_TRANSITIVITY_STAR, "trans*"
        certificate["rule_counts"]["trans*"] = certificate["rule_counts"].pop("trans")
        self.check(STRUCTURAL, certificate)

    def test_transitivity_star_native_iff_and_compound_endpoints(self):
        source = "(declare-const p Bool)(assert (not (not p)))(assert (not p))"
        certificate = make_certificate(source, [
            ("rewrite", [], "(= (not (not p)) p)"),
            ("refl", [], "(= p p)"),
            ("trans*", [3, 2], "(= (not (not p)) p)"),
            ("mp", [0, 4], "p"),
            ("unit-resolution", [1, 5], "false"),
        ])
        for declaration in certificate["declarations"]:
            if declaration["kind"] == z3.Z3_OP_EQ:
                declaration["kind"], declaration["name"] = z3.Z3_OP_IFF, "iff"
        self.check(source, certificate)

    def test_transitivity_star_shared_scoped_paths(self):
        source = "".join("(declare-const %s Bool)" % atom for atom in "pqr")
        source += "(assert (= p q))(assert (= r q))(assert p)(assert (not r))"
        certificate = make_certificate(source, [
            ("hypothesis", [], "(= p q)"),
            ("trans*", [1, 4], "(= p r)"),
            ("mp", [2, 5], "r"),
            ("unit-resolution", [3, 6], "false"),
            ("hypothesis", [], "p"),
            ("mp", [8, 5], "r"),
            ("unit-resolution", [3, 9], "false"),
            ("lemma", [10], "(or (not (= p q)) (not p))"),
            ("lemma", [7], "(not (= p q))"),
            ("unit-resolution", [11, 0, 2], "false"),
        ])
        text = self.check(source, certificate)
        proof_nodes = [node for node, raw in enumerate(certificate["nodes"])
                       if certificate["declarations"][raw["declaration"]]["range"] == "Proof"]
        header = next(line for line in text.splitlines() if line.startswith("  let _step_%d " % proof_nodes[5]))
        self.assertEqual(header.count("(_hyp"), 1)
        certificate["proof"] = proof_nodes[7]
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "undischarged hypotheses"):
            proof_to_lean.reconstruct(source, certificate)

    def test_transitivity_star_connects_structurally_identical_nodes(self):
        source = "".join("(declare-const %s Bool)" % atom for atom in "pqr")
        source += "(assert (= p q))(assert (= q r))(assert p)(assert (not r))"
        certificate = make_certificate(source, [
            ("trans*", [0, 1], "(= p r)"),
            ("mp", [2, 4], "r"),
            ("unit-resolution", [3, 5], "false"),
        ])
        middle = certificate["nodes"][certificate["assertions"][0]]["arguments"][1]
        duplicate = middle + 1
        for node in certificate["nodes"]:
            node["arguments"] = [arg + 1 if arg >= duplicate else arg for arg in node["arguments"]]
        certificate["nodes"].insert(duplicate, {
            "declaration": certificate["nodes"][middle]["declaration"], "arguments": [],
        })
        certificate["assertions"] = [arg + 1 if arg >= duplicate else arg for arg in certificate["assertions"]]
        certificate["proof"] += 1
        certificate["nodes"][certificate["assertions"][1]]["arguments"][0] = duplicate
        self.check(source, certificate)

    def test_long_transitivity_star_paths_do_not_enumerate_assignments(self):
        size = 128
        source = "".join("(declare-const p%d Bool)" % index for index in range(size + 1))
        for index in range(size):
            pair = (index, index + 1) if index % 2 == 0 else (index + 1, index)
            source += "(assert (= p%d p%d))" % pair
        source += "(assert p0)(assert (not p%d))" % size
        certificate = make_certificate(source, [
            ("trans*", list(reversed(range(size))), "(= p0 p%d)" % size),
            ("mp", [size, size + 2], "p%d" % size),
            ("unit-resolution", [size + 1, size + 3], "false"),
        ])
        text = self.check(source, certificate)
        self.assertEqual(text.count("Iff.trans"), size - 1)
        self.assertEqual(text.count("Iff.symm"), size // 2)
        self.assertNotIn("Decidable", text)
        self.assertNotIn("cases ", text)
        self.assertLess(len(text), 250_000)

    def test_monotonicity_for_all_boolean_operators(self):
        cases = [
            ("p", "p", []), ("true", "true", []), ("false", "false", []),
            ("(not p)", "(not s)", [0]),
            ("(and p)", "(and s)", [0]), ("(or p)", "(or s)", [0]),
            ("(and p q r)", "(and s t u)", [2, 0, 1]),
            ("(or p q r)", "(or s t u)", [2, 0, 1]),
            ("(and p q p r)", "(and s q s r)", [0, 0]),
            ("(=> p q)", "(=> s t)", [1, 0]),
            ("(= p q)", "(= s t)", [0, 1]),
            ("(xor p q)", "(xor s t)", [0, 1]),
            ("(ite p q r)", "(ite s t u)", [2, 0, 1]),
            ("(distinct p q)", "(distinct s t)", [0, 1]),
            ("(distinct p q r)", "(distinct s t u)", [0, 1, 2]),
        ]
        for left, right, premises in cases:
            with self.subTest(left=left, right=right):
                source = "".join("(declare-const %s Bool)" % atom for atom in "pqrstu")
                source += "(assert (= p s))(assert (= q t))(assert (= r u))"
                source += "(assert %s)(assert (not %s))" % (left, right)
                certificate = make_certificate(source, [
                    ("monotonicity", premises, "(= %s %s)" % (left, right)),
                    ("mp", [3, 5], right),
                    ("unit-resolution", [4, 6], "false"),
                ])
                text = self.check(source, certificate)
                self.assertNotIn("cases _d", text)
                self.assertNotIn("refute_with_decidable", text)

    def test_shared_nested_congruence_proofs(self):
        source = "(declare-const p Bool)(declare-const q Bool)(assert (= p q))"
        source += "(assert (and (not p) (not p)))(assert (not (and (not q) (not q))))"
        certificate = make_certificate(source, [
            ("monotonicity", [0], "(= (not p) (not q))"),
            ("monotonicity", [3], "(= (and (not p) (not p)) (and (not q) (not q)))"),
            ("mp", [1, 4], "(and (not q) (not q))"),
            ("unit-resolution", [5, 2], "false"),
        ])
        text = self.check(source, certificate)
        self.assertEqual(text.count("not_congr"), 1)
        self.assertEqual(text.count("and_congr"), 1)
        self.assertEqual(text.count("  let _step_"), 7)

    def test_large_congruence_does_not_enumerate_truth_assignments(self):
        size = 24
        source = "".join("(declare-const %s%d Bool)" % (prefix, index)
                         for prefix in ["p", "q"] for index in range(size))
        source += "".join("(assert (= p%d q%d))" % (index, index) for index in range(size))
        left = "(and %s)" % " ".join("p%d" % index for index in range(size))
        right = "(and %s)" % " ".join("q%d" % index for index in range(size))
        source += "(assert %s)(assert (not %s))" % (left, right)
        certificate = make_certificate(source, [
            ("monotonicity", list(reversed(range(size))), "(= %s %s)" % (left, right)),
            ("mp", [size, size + 2], right),
            ("unit-resolution", [size + 3, size + 1], "false"),
        ])
        text = self.check(source, certificate)
        self.assertEqual(text.count("and_congr"), size - 1)
        self.assertNotIn("cases _d", text)
        self.assertNotIn("Decidable", text)

    def test_conjunction_elimination_positions_and_nesting(self):
        for conjunction, target in [
            ("(and p q r)", "p"), ("(and p q r)", "q"), ("(and p q r)", "r"),
            ("(and p)", "p"), ("(and p p q)", "q"),
            ("(and (and p q) r)", "(and p q)"),
        ]:
            with self.subTest(conjunction=conjunction, target=target):
                source = "".join("(declare-const %s Bool)" % atom for atom in "pqr")
                source += "(assert %s)(assert (not %s))" % (conjunction, target)
                self.check(source, make_certificate(source, [
                    ("and-elim", [0], target),
                    ("unit-resolution", [2, 1], "false"),
                ]))
        source = "(declare-const p Bool)(declare-const q Bool)(declare-const r Bool)"
        source += "(assert (and (and p q) r))(assert (not q))"
        self.check(source, make_certificate(source, [
            ("and-elim", [0], "(and p q)"),
            ("and-elim", [2], "q"),
            ("unit-resolution", [3, 1], "false"),
        ]))

    def test_negated_disjunction_elimination_in_both_orientations(self):
        for disjunction, target, complement, decidable in [
            ("(or p q r)", "(not p)", "p", False),
            ("(or p q r)", "(not q)", "q", False),
            ("(or p q r)", "(not r)", "r", False),
            ("(or p)", "(not p)", "p", False),
            ("(or p p q)", "(not q)", "q", False),
            ("(or (not p) q)", "p", "(not p)", True),
            ("(or (not p) q)", "(not (not p))", "(not p)", False),
            ("(or (not p) (not (and q r)))", "(and q r)", "(not (and q r))", True),
            ("(or (not (not p)) q)", "(not p)", "p", True),
            ("(or (or p q) r)", "(not (or p q))", "(or p q)", False),
        ]:
            with self.subTest(disjunction=disjunction, target=target):
                source = "".join("(declare-const %s Bool)" % atom for atom in "pqr")
                source += "(assert (not %s))(assert %s)" % (disjunction, complement)
                text = self.check(source, make_certificate(source, [
                    ("not-or-elim", [0], target),
                    ("unit-resolution", [2, 1], "false"),
                ]))
                self.assertEqual("refute_with_decidable" in text, decidable)
                statement = text.split("theorem unsat", 1)[1].split(": False :=", 1)[0]
                self.assertNotIn("Decidable", statement)
                self.assertEqual(statement.count("    (_h"), 2)

    def test_mp_chains_implications_and_boolean_equalities(self):
        source = "".join("(declare-const %s Bool)" % atom for atom in "pqr")
        source += "(assert p)(assert (=> p q))(assert (= q r))(assert (not r))"
        self.check(source, make_certificate(source, [
            ("mp", [0, 1], "q"),
            ("mp", [4, 2], "r"),
            ("unit-resolution", [5, 3], "false"),
        ]))

    def test_shared_rewrite_proofs(self):
        source = "(declare-const p Bool)(declare-const q Bool)"
        source += "(assert p)(assert (=> p q))(assert (=> p q))(assert (not q))"
        certificate = make_certificate(source, [
            ("rewrite", [], "(= (=> p q) (or q (not p)))"),
            ("mp", [1, 4], "(or q (not p))"),
            ("mp", [2, 4], "(or q (not p))"),
            ("unit-resolution", [5, 0], "q"),
            ("unit-resolution", [6, 0], "q"),
            ("unit-resolution", [3, 7, 8], "false"),
        ])
        text = self.check(source, certificate)
        self.assertEqual(text.count("private theorem rewrite_"), 1)
        self.assertEqual(text.count("  let _step_"), 10)

    def test_native_iff_rewrite_and_structural_rules(self):
        source = "(declare-const p Bool)(assert (not (not p)))(assert (not p))"
        certificate = make_certificate(source, [
            ("rewrite", [], "(= (not (not p)) p)"),
            ("symm", [2], "(= p (not (not p)))"),
            ("symm", [3], "(= (not (not p)) p)"),
            ("refl", [], "(= p p)"),
            ("trans", [4, 5], "(= (not (not p)) p)"),
            ("mp", [0, 6], "p"),
            ("unit-resolution", [7, 1], "false"),
        ])
        for declaration in certificate["declarations"]:
            if declaration["kind"] == z3.Z3_OP_EQ:
                declaration["kind"], declaration["name"] = z3.Z3_OP_IFF, "iff"
        self.check(source, certificate)

    def test_boolean_rewrite_truth_tables(self):
        equivalences = [
            ("(not true)", "false"),
            ("(not false)", "true"),
            ("(not (not p))", "p"),
            ("(and p)", "p"),
            ("(or p)", "p"),
            ("(and p true)", "p"),
            ("(or p false)", "p"),
            ("(or p p)", "p"),
            ("(and p q r)", "(and r p q)"),
            ("(or p q r)", "(or r p q)"),
            ("(=> p q)", "(or (not p) q)"),
            ("(not (and p q))", "(or (not p) (not q))"),
            ("(not (or p q))", "(and (not p) (not q))"),
            ("(and p (or q r))", "(or (and p q) (and p r))"),
            ("(= p q)", "(and (=> p q) (=> q p))"),
            ("(xor p q)", "(not (= p q))"),
            ("(ite p q r)", "(or (and p q) (and (not p) r))"),
            ("(distinct p q)", "(xor p q)"),
            ("(distinct p q r)", "false"),
            ("(or p (not p))", "true"),
        ]
        source = "".join("(declare-const %s Bool)" % atom for atom in "pqr")
        source += "(assert (or p q r))(assert false)"
        steps = [("rewrite", [], "(= %s %s)" % pair) for pair in equivalences]
        steps.append(("asserted", [], "false"))
        self.check(source, make_certificate(source, steps))

    def test_lean_rejects_false_rewrites_without_publication(self):
        source = "(declare-const p Bool)(declare-const q Bool)(assert p)(assert (not q))"
        false_refutation = make_certificate(source, [
            ("rewrite", [], "(= p q)"),
            ("mp", [0, 2], "q"),
            ("unit-resolution", [3, 1], "false"),
        ])
        unused_source = "(declare-const p Bool)(assert p)(assert false)"
        unused_rewrite = make_certificate(unused_source, [
            ("rewrite", [], "(= p false)"), ("asserted", [], "false"),
        ])
        conditional_source = "".join("(declare-const %s Bool)" % atom for atom in "pqr")
        conditional_source += "(assert (or p q r))(assert false)"
        conditional_rewrite = make_certificate(conditional_source, [
            ("rewrite", [], "(= (or p q r) true)"), ("asserted", [], "false"),
        ])
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "proof.lean"
            output.write_text("previous artifact")
            for original, certificate in [
                (source, false_refutation), (unused_source, unused_rewrite),
                (conditional_source, conditional_rewrite),
            ]:
                with self.subTest(source=original):
                    with self.assertRaises(subprocess.CalledProcessError):
                        proof_to_lean.check_and_write(original, certificate, output)
                    self.assertEqual(output.read_text(), "previous artifact")
                    self.assertEqual(list(Path(directory).iterdir()), [output])

    def test_both_complement_orientations(self):
        source = "(declare-const p Bool)(declare-const q Bool)"
        source += "(assert (or (not p) q))(assert p)(assert (not q))"
        self.check(source, make_certificate(source, [
            ("unit-resolution", [0, 1, 2], "false"),
        ]))

    def test_shared_derived_proofs(self):
        source = "".join("(declare-const %s Bool)" % atom for atom in "pqrs")
        source += """\
(assert (or p q))(assert (not p))
(assert (or (not q) r))(assert (or (not q) s))
(assert (or (not r) (not s)))
"""
        certificate = make_certificate(source, [
            ("unit-resolution", [0, 1], "q"),
            ("unit-resolution", [2, 5], "r"),
            ("unit-resolution", [3, 5], "s"),
            ("unit-resolution", [4, 6, 7], "false"),
        ])
        text = self.check(source, certificate)
        self.assertEqual(text.count("  let _step_"), 9)

    def test_residual_clauses_reordering_and_factoring(self):
        source = "".join("(declare-const %s Bool)" % atom for atom in "pqr")
        source += "(assert (or p p q r))(assert (not p))(assert (not q))(assert (not r))"
        self.check(source, make_certificate(source, [
            ("unit-resolution", [0, 1], "(or r q)"),
            ("unit-resolution", [4, 2, 3], "false"),
        ]))

    def test_empty_singleton_and_false_containing_clauses(self):
        for clause in ["false", "(or p)", "(or false p)", "(or p false)"]:
            with self.subTest(clause=clause):
                source = "(declare-const p Bool)(assert %s)" % clause
                units = []
                if clause != "false":
                    source += "(assert (not p))"
                    units = [1]
                self.check(source, make_certificate(source, [
                    ("unit-resolution", [0] + units, "false"),
                ]))

    def test_unusual_symbol_names_are_only_escaped_metadata(self):
        name = "|p\naxiom injected : False\n|"
        source = "(declare-const %s Bool)(assert %s)(assert (not %s))" % (name, name, name)
        self.check(source, proof_certificate.export_certificate(source))

    def test_boolean_translation_truth_tables(self):
        cases = [
            ("true", lambda p, q, r: True),
            ("false", lambda p, q, r: False),
            ("(not p)", lambda p, q, r: not p),
            ("(and p q r)", lambda p, q, r: p and q and r),
            ("(or p q r)", lambda p, q, r: p or q or r),
            ("(=> p q)", lambda p, q, r: not p or q),
            ("(=> p q r)", lambda p, q, r: not p or not q or r),
            ("(= p q)", lambda p, q, r: p == q),
            ("(= p q r)", lambda p, q, r: p == q == r),
            ("(xor p q)", lambda p, q, r: p != q),
            ("(xor p q r)", lambda p, q, r: (p != q) != r),
            ("(ite p q r)", lambda p, q, r: q if p else r),
            ("(distinct p q)", lambda p, q, r: p != q),
            ("(distinct p q r)", lambda p, q, r: len({p, q, r}) == 3),
        ]
        files = ["import Init\n"]
        for expression, evaluate in cases:
            source = "".join("(declare-const %s Bool)" % atom for atom in "pqr")
            source += "(assert %s)(assert false)" % expression
            certificate = make_certificate(source, [])
            text = proof_to_lean.reconstruct(source, certificate)
            files.append(text[len("import Init\n"):])
            namespace = "Z3Proofs.NativeCertificate.p" + hashlib.sha256(source.encode()).hexdigest()
            reachable, pending = set(), [certificate["assertions"][0]]
            while pending:
                node = pending.pop()
                if node not in reachable:
                    reachable.add(node)
                    pending.extend(certificate["nodes"][node]["arguments"])
            definitions = [
                namespace + ".formula_%d" % node
                for node in sorted(reachable)
            ]
            atoms = [decl["name"] for decl in certificate["declarations"]
                     if decl["kind"] == z3.Z3_OP_UNINTERPRETED]
            for values in itertools.product([False, True], repeat=3):
                assignment = dict(zip("pqr", values))
                valuation = "False"
                for index, name in reversed(list(enumerate(atoms))):
                    valuation = "if _i = %d then %s else %s" % (
                        index, str(assignment[name]), valuation)
                formula = "%s.formula_%d (fun _i => %s)" % (
                    namespace, certificate["assertions"][0], valuation)
                files.append("example : (%s) <-> %s := by\n  unfold %s\n  decide\n" % (
                    formula, str(evaluate(*values)), " ".join(reversed(definitions))))
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "truth_tables.lean"
            path.write_text("\n".join(files))
            result = subprocess.run(
                [str(proof_to_lean._CHECK_LEAN), str(path)], capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_lean_rejects_bad_generated_terms_without_publication(self):
        certificate = proof_certificate.export_certificate(LITERAL)
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "proof.lean"
            output.write_text("previous artifact")
            for bad_term in ["theorem unsat : False := True.intro\n",
                             "theorem unsat : False := by sorry\n"]:
                with self.subTest(term=bad_term):
                    with patch.object(proof_to_lean, "reconstruct", return_value=bad_term):
                        with self.assertRaises(subprocess.CalledProcessError):
                            proof_to_lean.check_and_write(LITERAL, certificate, output)
                    self.assertEqual(output.read_text(), "previous artifact")
                    self.assertEqual(list(Path(directory).iterdir()), [output])

    def test_cli_publishes_only_supported_checked_proofs(self):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            original = directory / "input.smt2"
            certificate = directory / "proof.json"
            output = directory / "result.lean"
            original.write_text(CLAUSE)
            certificate.write_text(json.dumps(proof_certificate.export_certificate(CLAUSE)))
            command = [sys.executable, str(_EXAMPLES / "proof_to_lean.py"),
                       str(original), str(certificate), "-o", str(output)]
            result = subprocess.run(command, text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("Lean checked the refutation", result.stdout)
            original.write_text(REWRITE)
            certificate.write_text(json.dumps(proof_certificate.export_certificate(REWRITE)))
            result = subprocess.run(command, text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("Lean checked the refutation", result.stdout)
            original.write_text(STRUCTURAL)
            certificate.write_text(json.dumps(proof_certificate.export_certificate(STRUCTURAL)))
            result = subprocess.run(command, text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("Lean checked the refutation", result.stdout)
            original.write_text(BRANCHING)
            certificate.write_text(json.dumps(proof_certificate.export_certificate(BRANCHING)))
            result = subprocess.run(command, text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("Lean checked the refutation", result.stdout)
            original.write_text(XOR)
            certificate.write_text(json.dumps(proof_certificate.export_certificate(XOR)))
            result = subprocess.run(command, text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("Lean checked the refutation", result.stdout)
            previous = output.read_text()
            original.write_text(NESTED)
            unsupported = proof_certificate.export_certificate(NESTED)
            for declaration in unsupported["declarations"]:
                if declaration["kind"] == z3.Z3_OP_PR_ASSERTED:
                    declaration["kind"], declaration["name"] = z3.Z3_OP_PR_REWRITE_STAR, "rewrite*"
            unsupported["rule_counts"]["rewrite*"] = unsupported["rule_counts"].pop("asserted")
            certificate.write_text(json.dumps(unsupported))
            result = subprocess.run(command, text=True, capture_output=True)
            self.assertEqual(result.returncode, 2)
            self.assertIn("unsupported native proof rule", result.stderr)
            self.assertEqual(output.read_text(), previous)
            self.assertEqual(set(directory.iterdir()), {original, certificate, output})
            source = "(declare-const p Bool)(assert p)"
            original.write_text(source)
            certificate.write_text(json.dumps(make_certificate(source, [
                ("def-axiom", [], "(not p)"), ("unit-resolution", [0, 1], "false"),
            ])))
            result = subprocess.run(command, text=True, capture_output=True)
            self.assertEqual(result.returncode, 2)
            self.assertIn("invalid def-axiom clause", result.stderr)
            self.assertEqual(output.read_text(), previous)
            self.assertEqual(set(directory.iterdir()), {original, certificate, output})
            source = "(declare-const p Bool)(assert p)"
            original.write_text(source)
            certificate.write_text(json.dumps(make_certificate(source, [
                ("hypothesis", [], "(not p)"), ("unit-resolution", [0, 1], "false"),
            ])))
            result = subprocess.run(command, text=True, capture_output=True)
            self.assertEqual(result.returncode, 2)
            self.assertIn("undischarged hypotheses", result.stderr)
            self.assertEqual(output.read_text(), previous)
            self.assertEqual(set(directory.iterdir()), {original, certificate, output})

    def test_cli_rejects_tampering_and_input_overwrite(self):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            original = directory / "input.smt2"
            certificate_path = directory / "proof.json"
            output = directory / "result.lean"
            original.write_text(LITERAL)
            certificate = proof_certificate.export_certificate(LITERAL)
            certificate_path.write_text(json.dumps(certificate))
            command = [sys.executable, str(_EXAMPLES / "proof_to_lean.py"),
                       str(original), str(certificate_path), "-o"]
            for target in [original, certificate_path]:
                result = subprocess.run(command + [str(target)], text=True, capture_output=True)
                self.assertEqual(result.returncode, 2)
                self.assertIn("must not overwrite", result.stderr)
            alias = directory / "alias.lean"
            os.link(original, alias)
            result = subprocess.run(command + [str(alias)], text=True, capture_output=True)
            self.assertEqual(result.returncode, 2)
            self.assertIn("must not overwrite", result.stderr)
            self.assertEqual(original.read_text(), LITERAL)
            certificate["assertions"][1] = certificate["assertions"][0]
            certificate_path.write_text(json.dumps(certificate))
            result = subprocess.run(command + [str(output)], text=True, capture_output=True)
            self.assertEqual(result.returncode, 2)
            self.assertIn("assertions do not match", result.stderr)
            self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
