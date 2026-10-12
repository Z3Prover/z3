############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Tests for the QF_LRA slice of the Lean reconstruction: validation without
# Lean, and end-to-end checks that need the z3 executable and the pinned
# Lean toolchain.
############################################
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random
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
import proof_to_lean

# Verbatim copies of the QF_LRA inputs documented for Z3Prover/z3test under
# regressions/proofs/lean/, so the tests need no z3test checkout.
Z3TEST_LRA_INPUTS = {
    "lra_farkas": """\
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (>= (+ (* 2.0 x) y) 5.0))
(assert (<= (+ x (* 3.0 z)) 1.0))
(assert (<= (- y (* 6.0 z)) 2.0))
(assert (<= x 0.0))
(check-sat)
""",
    "lra_equality": """\
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(assert (= x (+ y 1.0)))
(assert (> x 5.0))
(assert (< y 2.0))
(check-sat)
""",
    "lra_fractions": """\
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(assert (>= (- x y) (/ 1.0 3.0)))
(assert (<= (- x y) (/ 1.0 4.0)))
(check-sat)
""",
    "lra_boolean_structure": """\
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(declare-const p Bool)
(assert (or p (<= x (- 6.0))))
(assert (=> p (>= (+ x y) 1.5)))
(assert (and (< y (/ 1.0 3.0)) (> x 0.0)))
(assert (not (= x 7.0)))
(assert (<= x 1.0))
(check-sat)
""",
    "lra_split_assertion": """\
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(assert (not (and (< x 1.0) (< y 1.0))))
(assert (xor (>= x 1.0) (>= y 1.0)))
(assert (= (>= x 1.0) (>= y 1.0)))
(check-sat)
""",
}

_STANDARD_AXIOMS = "[propext, Classical.choice, Quot.sound]"

# Real-valued ite terms: an opaque variable to Farkas reasoning, tied to its
# branches by gate clauses, and normalized by Z3 (abs/max shapes are rewritten).
ITE_INPUTS = {
    "ite_basic": """\
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(declare-const p Bool)
(assert (> (ite p x y) 3.0))
(assert (< x 1.0))
(assert (< y 2.0))
(check-sat)
""",
    "ite_abs_max": """\
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (> (+ (ite (< x 0.0) (- x) x) (ite (< y 0.0) (- y) y)) 3.0))
(assert (< x 1.0))
(assert (> x (- 1.0)))
(assert (< y 2.0))
(assert (> y (- 1.0)))
(assert (= z (ite (> x y) x y)))
(assert (> z 5.0))
(check-sat)
""",
    "ite_nested_fractions": """\
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(declare-const p Bool)
(declare-const q Bool)
(assert (>= (ite (and p q) (ite p x (/ 1.0 3.0)) (ite q (/ y 2.0) (- x))) (/ 7.0 2.0)))
(assert (<= x (/ 1.0 2.0)))
(assert (<= y (/ 2.0 3.0)))
(assert (>= x (- 1.0)))
(check-sat)
""",
    "ite_distinct": """\
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(declare-const p Bool)
(assert (distinct (ite p x y) x y))
(check-sat)
""",
}

# A comparison applied directly to an ite with a fractional branch: Z3's
# rewriter pushes the comparison through the ite, so the log never mentions
# the ite as a term and no gate clause is recorded; only the cnf lemmas that
# bridge the assertion to its rewritten form tie the ite to its branches.
ITE_REWRITTEN_INPUTS = {
    "ite_half_branch": """\
(set-logic QF_LRA)
(declare-const x Real)
(declare-const p Bool)
(assert (>= (ite p x (/ 1.0 2.0)) 1.0))
(assert (< x 1.0))
(check-sat)
""",
    "ite_divided_branches": """\
(set-logic QF_LRA)
(declare-const x Real)
(declare-const p Bool)
(assert (> (ite p (/ x 3.0) (/ 1.0 7.0)) 3.0))
(assert (< x 1.0))
(check-sat)
""",
    "ite_deep_fractions": """\
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(declare-const p Bool)
(declare-const q Bool)
(assert (>= (ite p (ite q (/ x 3.0) (/ 1.0 7.0)) (ite (< y (/ 1.0 2.0)) (/ y 5.0) (/ 2.0 3.0))) 1.0))
(assert (< x 1.0))
(assert (< y 1.0))
(check-sat)
""",
}


def random_instance(seed, variables, constraints, ite=False):
    """A random QF_LRA problem; callers filter for unsat ones."""
    generator = random.Random(seed)
    lines = ["(set-logic QF_LRA)"] + ["(declare-const x%d Real)" % i for i in range(variables)]

    def term(v):
        if ite and generator.random() < 0.3:
            other = generator.randrange(variables)
            return "(ite (%s x%d %d.0) x%d (* %d.0 x%d))" % (
                generator.choice(["<=", ">"]), other, generator.randint(-2, 2), v,
                generator.choice([-2, -1, 2]), other)
        return "x%d" % v

    def atom():
        chosen = generator.sample(range(variables), generator.randint(2, 3))
        terms = " ".join("(* %d.0 %s)" % (generator.choice([-3, -2, -1, 1, 2, 3]), term(v)) for v in chosen)
        constant = generator.choice(["%d.0" % generator.randint(-5, 5),
                                     "(/ %d.0 %d.0)" % (generator.randint(-9, 9), generator.randint(2, 4))])
        return "(%s (+ %s) %s)" % (generator.choice(["<=", ">=", "<", ">", "="]), terms, constant)

    for _ in range(constraints):
        roll = generator.random()
        if roll < 0.4:
            lines.append("(assert (or %s %s))" % (atom(), atom()))
        elif roll < 0.5:
            lines.append("(assert (not (and %s %s)))" % (atom(), atom()))
        else:
            lines.append("(assert %s)" % atom())
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


def _z3_available():
    try:
        return subprocess.run([proof_certificate.default_z3_executable(), "--version"],
                              capture_output=True).returncode == 0
    except OSError:
        return False


def _th_lemma_nodes(certificate):
    return [index for index, node in enumerate(certificate["nodes"])
            if certificate["declarations"][node["declaration"]]["name"] == "th-lemma"]


class TestArithmeticValidation(unittest.TestCase):
    """Certificate validation and Lean text generation, without running Lean."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")
        cls.source = Z3TEST_LRA_INPUTS["lra_farkas"]
        cls.certificate = proof_certificate.export_clause_log_certificate(cls.source)

    def test_generated_lean_quantifies_over_a_rational_valuation(self):
        text = proof_to_lean.reconstruct(self.source, self.certificate)
        self.assertIn("theorem unsat (_atoms : Nat -> Prop) (_vars : Nat -> Rat)", text)
        self.assertIn("-- Variable 0: \"x\"", text)
        self.assertIn("Real variables are encoded as Rat", text)
        self.assertIn("def term_", text)
        self.assertIn("private theorem th_lemma_", text)
        self.assertIn("set_option maxRecDepth", text)
        self.assertNotIn("sorry", text)
        self.assertNotIn("axiom ", text)

    def test_tampered_coefficients_are_rejected_before_lean(self):
        certificate = copy.deepcopy(self.certificate)
        for declaration in certificate["declarations"]:
            if declaration["name"] == "th-lemma":
                declaration["parameters"] = ["farkas", "1", "1", "1"]
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "do not refute"):
            proof_to_lean.reconstruct(self.source, certificate)
        certificate = copy.deepcopy(self.certificate)
        for declaration in certificate["declarations"]:
            if declaration["name"] == "th-lemma":
                declaration["parameters"] = ["farkas", "1", "2"]
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "coefficients for"):
            proof_to_lean.reconstruct(self.source, certificate)
        for parameters, message in [
            ([], "unsupported native proof rule"),
            (["nla"], "unsupported native proof rule"),
            (["farkas", "-1", "2", "1"], "nonnegative"),
            (["euf", "1"], "takes no coefficients"),
            ([1, 2], "must be strings"),
        ]:
            certificate = copy.deepcopy(self.certificate)
            for declaration in certificate["declarations"]:
                if declaration["name"] == "th-lemma":
                    declaration["parameters"] = parameters
            with self.subTest(parameters=parameters):
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, message):
                    proof_to_lean.reconstruct(self.source, certificate)

    def test_fragment_and_sort_consistency(self):
        certificate = copy.deepcopy(self.certificate)
        certificate["fragment"] = "propositional"
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "cannot contain arithmetic"):
            proof_to_lean.reconstruct(self.source, certificate)
        certificate = copy.deepcopy(self.certificate)
        certificate["fragment"] = "qf_lia"
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "unsupported certificate header"):
            proof_to_lean.reconstruct(self.source, certificate)
        # A Boolean certificate claiming the arithmetic fragment is rejected at binding.
        boolean = proof_certificate.export_certificate("(declare-const p Bool)(assert p)(assert (not p))")
        boolean["fragment"] = "qf_lra"
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "fragment propositional"):
            proof_to_lean.reconstruct("(declare-const p Bool)(assert p)(assert (not p))", boolean)
        # Renaming a variable breaks the binding to the input even when the text is updated.
        renamed = self.source.replace("(declare-const z Real)", "(declare-const w Real)").replace("z)", "w)")
        certificate = copy.deepcopy(self.certificate)
        certificate["source_smt2"] = renamed
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "do not match the original input"):
            proof_to_lean.reconstruct(renamed, certificate)

    def test_malformed_arithmetic_declarations_are_rejected(self):
        for mutate, message in [
            (lambda d: d["kind"] == z3.Z3_OP_ANUM and d.update(name="1/0"), "invalid numeral"),
            (lambda d: d["kind"] == z3.Z3_OP_ADD and d.update(domain=["Real", "Bool"]), "take Real arguments"),
            (lambda d: d["kind"] == z3.Z3_OP_LE and d.update(domain=["Bool", "Bool"]), "arithmetic predicate"),
            (lambda d: d["kind"] == z3.Z3_OP_MUL and d.update(name="x"), "unsupported arithmetic declaration"),
        ]:
            certificate = copy.deepcopy(self.certificate)
            for declaration in certificate["declarations"]:
                if declaration["range"] == "Real" or declaration["kind"] == z3.Z3_OP_LE:
                    mutate(declaration)
            with self.subTest(message=message):
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, message):
                    proof_to_lean.reconstruct(self.source, certificate)

    def test_linear_forms_handle_every_operator_shape(self):
        source = ("(declare-const x Real)(declare-const y Real)"
                  "(assert (> (- (* 2.0 (/ x 4.0)) y 1.0) (- (+ x (* (- 3.0) y)) (/ 1.0 2.0))))"
                  "(assert (<= (- x) (* 2.0 y)))(assert (>= (- x) (+ (* 2.0 y) 3.0)))")
        certificate = proof_certificate.export_clause_log_certificate(source)
        graph = proof_to_lean._validate_graph(source, certificate)
        for node in _th_lemma_nodes(certificate):
            proof_to_lean._check_th_lemma(graph, node)
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertIn("have _s", text)  # fractional atoms get scaling helpers

    def test_unary_minus_negates_variable_coefficients(self):
        source = "(declare-const x Real)(assert (> (- x) (/ 1.0 2.0)))(assert (>= x 0.0))"
        certificate = proof_certificate.export_clause_log_certificate(source)
        graph = proof_to_lean._validate_graph(source, certificate)
        node = next(i for i in range(len(graph.nodes))
                    if graph.kind(i) == z3.Z3_OP_UMINUS
                    and graph.kind(graph.arguments(i)[0]) == z3.Z3_OP_UNINTERPRETED)
        terms = {}
        self.assertEqual(proof_to_lean._linear_term(graph, node, Fraction(1), terms), 0)
        self.assertEqual(terms, {graph.arguments(node)[0]: Fraction(-1)})

    def test_implied_equality_requires_an_equality_conclusion(self):
        certificate = copy.deepcopy(self.certificate)
        for declaration in certificate["declarations"]:
            if declaration["name"] == "th-lemma":
                declaration["parameters"][0] = "implied-eq"
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "must end in a Real equality"):
            proof_to_lean.reconstruct(self.source, certificate)

    def test_real_ite_is_an_opaque_linear_atom_with_classical_terms(self):
        source = ITE_INPUTS["ite_basic"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        graph = proof_to_lean._validate_graph(source, certificate)
        ite = next(i for i in range(len(graph.nodes)) if graph.kind(i) == z3.Z3_OP_ITE)
        self.assertTrue(graph.is_real(ite))
        terms = {}
        self.assertEqual(proof_to_lean._linear_term(graph, ite, Fraction(2), terms), 0)
        self.assertEqual(terms, {ite: Fraction(2)})
        for node in _th_lemma_nodes(certificate):
            proof_to_lean._check_th_lemma(graph, node)
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertIn("noncomputable def term_%d (_atoms : Nat -> Prop) (_vars : Nat -> Rat) : Rat := (@ite Rat" % ite, text)
        self.assertIn("(Classical.propDecidable _)", text)
        self.assertIn("(ite_eq_left _hc)", text)
        self.assertIn("(ite_eq_right _hnc)", text)
        # Every grind lemma over the ite states its branch equalities first.
        self.assertIn("  have _g%d_0 : (_atoms 0) -> (" % ite, text)
        self.assertIn("  have _g%d_1 : (Not (_atoms 0)) -> (" % ite, text)
        self.assertNotIn("sorry", text)
        self.assertNotIn("axiom ", text)

    def test_fractional_ite_branches_get_scaled_gate_helpers(self):
        source = ITE_REWRITTEN_INPUTS["ite_divided_branches"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        self.assertNotIn("def-axiom", certificate["rule_counts"])  # the rewriter removed the ite term
        graph = proof_to_lean._validate_graph(source, certificate)
        ite = next(i for i in range(len(graph.nodes)) if graph.kind(i) == z3.Z3_OP_ITE)
        text = proof_to_lean.reconstruct(source, certificate)
        # x / 3 scales by 3 and 1 / 7 by 7; both helpers rewrite the ite and let grind close the scaled form.
        self.assertIn("  have _g%d_0 : (_atoms 0) -> ((3 : Rat)) * (" % ite, text)
        self.assertIn("= (((1 : Rat)) * _vars 0 + ((0 : Rat))) := fun _h => by rw [ite_eq_left _h]; grind", text)
        self.assertIn("  have _g%d_1 : (Not (_atoms 0)) -> ((7 : Rat)) * (" % ite, text)
        self.assertIn("= (((1 : Rat))) := fun _h => by rw [ite_eq_right _h]; grind", text)

    def test_tampered_ite_declarations_and_gate_clauses_are_rejected_before_lean(self):
        source = ITE_INPUTS["ite_basic"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        for domain, message in [
            (["Real", "Real", "Real"], "invalid arithmetic ite declaration"),
            (["Bool", "Real"], "invalid arithmetic ite declaration"),
        ]:
            tampered = copy.deepcopy(certificate)
            for declaration in tampered["declarations"]:
                if declaration["kind"] == z3.Z3_OP_ITE and declaration["range"] == "Real":
                    declaration["domain"] = domain
            with self.subTest(domain=domain):
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, message):
                    proof_to_lean.reconstruct(source, tampered)
        # Point the then-gate clause (not p) or (ite p x y) = x at the else branch.
        graph = proof_to_lean._validate_graph(source, certificate)
        ite = next(i for i in range(len(graph.nodes)) if graph.kind(i) == z3.Z3_OP_ITE)
        condition, then_branch, else_branch = graph.arguments(ite)
        equality = next(i for i in range(len(graph.nodes)) if graph.kind(i) == z3.Z3_OP_EQ
                        and graph.arguments(i) == (ite, then_branch))
        tampered = copy.deepcopy(certificate)
        tampered["nodes"][equality]["arguments"] = [ite, else_branch]
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "unsupported or invalid def-axiom clause"):
            proof_to_lean.reconstruct(source, tampered)


@unittest.skipUnless(_z3_available(), "the z3 executable is required for the clause log")
class TestArithmeticLeanIntegration(unittest.TestCase):
    """End-to-end: z3 clause log, certificate, Lean reconstruction, kernel check."""

    def check(self, source, core="clause-log"):
        if core == "clause-log":
            certificate = proof_certificate.export_clause_log_certificate(source)
        else:
            certificate = proof_certificate.export_certificate(source)
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "checked.lean"
            proof_to_lean.check_and_write(source, certificate, output)
            text = output.read_text()
            namespace = "Z3Proofs.NativeCertificate.p" + hashlib.sha256(source.encode()).hexdigest()
            statement = text.split("theorem unsat", 1)[1].split(": False :=", 1)[0]
            self.assertEqual(statement.count("    (_h"), len(certificate["assertions"]))
            self.assertNotIn("_hyp", statement)
            if certificate["fragment"] == "qf_lra":
                self.assertIn("(_vars : Nat -> Rat)", statement)
            output.write_text(text + "\n#print axioms %s.unsat\n" % namespace)
            result = subprocess.run([str(proof_to_lean._CHECK_LEAN), str(output)],
                                    text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            return certificate, " ".join(result.stdout.split())

    def test_documented_lra_inputs_verify_under_the_standard_axioms(self):
        for name, source in Z3TEST_LRA_INPUTS.items():
            with self.subTest(name=name):
                certificate, report = self.check(source)
                self.assertEqual(certificate["fragment"], "qf_lra")
                self.assertIn(_STANDARD_AXIOMS, report)
                self.assertIn("th-lemma", certificate["rule_counts"])

    def test_boolean_inputs_through_the_clause_log(self):
        from test_proof_to_lean import Z3TEST_LEAN_INPUTS
        for name, source in Z3TEST_LEAN_INPUTS.items():
            with self.subTest(name=name):
                source = "\n".join(line for line in source.splitlines() if "set-option" not in line) + "\n"
                certificate, _ = self.check(source)
                self.assertEqual(certificate["fragment"], "propositional")

    def test_implied_equality_distinct_and_unary_minus(self):
        for source in [
            "(declare-const x Real)(declare-const y Real)"
            "(assert (<= x y))(assert (>= x y))(assert (not (= x y)))",
            "(declare-const x Real)(declare-const y Real)(declare-const z Real)"
            "(assert (distinct x y z))(assert (= x y))",
            "(declare-const x Real)(assert (> (- x) (/ 1.0 2.0)))(assert (>= x 0.0))",
        ]:
            with self.subTest(source=source):
                self.check(source)

    def test_native_dependency_core_is_checked_in_lean(self):
        with patch.object(proof_clause_log, "_TRIM_THRESHOLD", 0):
            self.check(Z3TEST_LRA_INPUTS["lra_farkas"])

    def test_outlined_proofs_preserve_original_assertions_and_scopes(self):
        with patch.object(proof_to_lean, "_OUTLINE_PROOF_STEPS", 0):
            for name in ("lra_farkas", "lra_fractions", "lra_boolean_structure", "lra_split_assertion"):
                with self.subTest(input=name):
                    self.check(Z3TEST_LRA_INPUTS[name])

    def test_small_chunks_cut_arithmetic_lemmas_everywhere(self):
        # Force chunk boundaries inside Farkas, gate-clause, and Rat-valued ite
        # subproofs; every chunk must still be a closed lemma under the
        # standard axioms, with the classical witnesses local to each lemma.
        from test_proof_to_lean_uf import outlined_lemma_sizes, _proof_steps
        inputs = {name: Z3TEST_LRA_INPUTS[name] for name in ("lra_boolean_structure", "lra_split_assertion")}
        inputs.update(ITE_INPUTS)
        with patch.object(proof_to_lean, "_OUTLINE_PROOF_STEPS", 0), \
                patch.object(proof_to_lean, "_OUTLINE_CHUNK_STEPS", 3):
            for name, source in inputs.items():
                with self.subTest(input=name):
                    certificate, report = self.check(source)
                    self.assertIn(_STANDARD_AXIOMS, report)
                    text = proof_to_lean.reconstruct(source, certificate)
                    sizes = outlined_lemma_sizes(text)
                    self.assertLessEqual(max(sizes), 3)
                    self.assertEqual(sum(sizes), _proof_steps(certificate))
                    self.assertNotIn("refute_with_decidable", text)

    def test_normalized_rewrites_are_checked_atom_by_atom(self):
        with patch.object(proof_to_lean, "_NORMALIZED_REWRITE_ATOMS", 0):
            for name in ("lra_farkas", "lra_boolean_structure", "lra_split_assertion"):
                with self.subTest(input=name):
                    self.check(Z3TEST_LRA_INPUTS[name])

    def test_large_rewrite_is_structural_not_a_truth_table(self):
        context = z3.Context()
        variables = [z3.Real("x%d" % i, context) for i in range(24)]
        atoms = [z3.Not(var < 0) if i % 3 == 0 else var <= 0
                 for i, var in enumerate(variables)]
        original = z3.Or(z3.And(*atoms[:12]), z3.And(*atoms[12:]))
        rewritten = z3.Or(z3.And(*reversed(atoms[12:])), z3.And(*reversed(atoms[:12])))
        assertions = [original, z3.Not(rewritten)]
        solver = z3.Solver(ctx=context)
        solver.add(assertions)
        source = solver.to_smt2()
        dag = proof_certificate.DagBuilder()
        roots = [dag.expression(assertion) for assertion in assertions]
        asserted = dag.rule(z3.Z3_OP_PR_ASSERTED, "asserted", 0)
        first = dag.node(asserted, [roots[0]])
        rewrite = dag.node(dag.rule(z3.Z3_OP_PR_REWRITE, "rewrite", 0),
                           [dag.expression(original == rewritten)])
        mp = dag.node(dag.rule(z3.Z3_OP_PR_MODUS_PONENS, "mp", 2),
                      [first, rewrite, dag.expression(rewritten)])
        negated = dag.node(asserted, [roots[1]])
        root = dag.node(dag.rule(z3.Z3_OP_PR_UNIT_RESOLUTION, "unit-resolution", 2),
                        [mp, negated, dag.expression(z3.BoolVal(False, context))])
        certificate = dag.certificate(source, "qf_lra", roots, root)
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertIn("normalized_rewrite_", text)
        self.assertNotIn("of_decide_eq_true", text)
        with tempfile.TemporaryDirectory() as directory:
            proof_to_lean.check_and_write(source, certificate, Path(directory) / "checked.lean")

    def test_euf_congruence_annotation_cannot_supply_a_missing_equality(self):
        source = ("(declare-const x Real)(declare-const y Real)"
                  "(assert (<= x 0.0))(assert (not (<= y 0.0)))")
        log = """\
(declare-fun x () Real)
(declare-fun y () Real)
(define-const a Bool (<= x 0.0))
(define-const b Bool (<= y 0.0))
(define-const c Proof (cc (= a b)))
(assume a)
(assume (not b))
(define-const h Proof (euf a (not b) c))
(infer (not a) b h)
(infer rup)
"""
        context = z3.Context()
        assertions, fragment = proof_certificate.parse_assertions(source, context)
        certificate = proof_clause_log.build_certificate(source, fragment, assertions, log, context)
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "checked.lean"
            with self.assertRaises(subprocess.CalledProcessError):
                proof_to_lean.check_and_write(source, certificate, output)
            self.assertFalse(output.exists())

    def test_invalid_implied_equality_never_publishes_a_proof(self):
        source = ("(declare-const x Real)(declare-const y Real)"
                  "(assert (<= x y))(assert (>= x y))(assert (not (= x y)))")
        certificate = proof_certificate.export_clause_log_certificate(source)
        equality = next(index for index, raw in enumerate(certificate["nodes"])
                        if certificate["declarations"][raw["declaration"]]["kind"] == z3.Z3_OP_EQ
                        and all(certificate["declarations"][certificate["nodes"][arg]["declaration"]]["kind"]
                                == z3.Z3_OP_UNINTERPRETED for arg in raw["arguments"]))
        certificate["declarations"].append({
            "kind": z3.Z3_OP_PR_TH_LEMMA, "name": "th-lemma", "domain": ["Bool"],
            "range": "Proof", "parameters": ["implied-eq", "1"],
        })
        certificate["nodes"].append({"declaration": len(certificate["declarations"]) - 1,
                                     "arguments": [equality]})
        certificate["rule_counts"]["th-lemma"] += 1
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "checked.lean"
            with self.assertRaises(subprocess.CalledProcessError):
                proof_to_lean.check_and_write(source, certificate, output)
            self.assertFalse(output.exists())

    def test_random_instances_with_learned_clauses_and_deletions(self):
        self.check_random_unsat_instances(ite=False)

    def test_arithmetic_ite_terms_verify_under_the_standard_axioms(self):
        for name, source in ITE_INPUTS.items():
            with self.subTest(name=name):
                certificate, report = self.check(source)
                self.assertEqual(certificate["fragment"], "qf_lra")
                self.assertIn(_STANDARD_AXIOMS, report)
                self.assertIn("th-lemma", certificate["rule_counts"])
                self.assertIn("def-axiom", certificate["rule_counts"])  # the ite gate clauses

    def test_comparisons_pushed_through_an_ite_with_fractional_branches_verify(self):
        for name, source in ITE_REWRITTEN_INPUTS.items():
            with self.subTest(name=name):
                certificate, report = self.check(source)
                self.assertEqual(certificate["fragment"], "qf_lra")
                self.assertIn(_STANDARD_AXIOMS, report)
                self.assertIn("th-lemma", certificate["rule_counts"])
                self.assertNotIn("def-axiom", certificate["rule_counts"])

    def test_random_instances_with_ite_terms(self):
        self.check_random_unsat_instances(ite=True)

    def test_long_arithmetic_refutation_is_outlined_by_default(self):
        # The first random ite instance above the threshold is outlined without
        # any override: chunk cuts fall inside Farkas and Rat-valued ite
        # subproofs, and the classical witnesses stay local to each lemma.
        from test_proof_to_lean_uf import outlined_lemma_sizes, _proof_steps
        for seed in range(1, 200):
            source = random_instance(seed, 6, 14, ite=True)
            if "(ite " not in source:
                continue
            context = z3.Context()
            solver = z3.Solver(ctx=context)
            solver.add(z3.parse_smt2_string(source, ctx=context))
            if solver.check() != z3.unsat:
                continue
            certificate = proof_certificate.export_clause_log_certificate(source)
            steps = sum(1 for node in certificate["nodes"]
                        if certificate["declarations"][node["declaration"]]["range"] == "Proof")
            if steps > proof_to_lean._OUTLINE_PROOF_STEPS:
                break
        else:
            self.fail("no random ite instance exceeds the outlining threshold")
        certificate, report = self.check(source)
        self.assertIn(_STANDARD_AXIOMS, report)
        text = proof_to_lean.reconstruct(source, certificate)
        sizes = outlined_lemma_sizes(text)
        self.assertGreater(len(sizes), 1)
        self.assertLessEqual(max(sizes), proof_to_lean._OUTLINE_CHUNK_STEPS)
        self.assertEqual(sum(sizes), _proof_steps(certificate))
        self.assertIn("Classical.propDecidable", text)
        self.assertNotIn("refute_with_decidable", text)

    def check_random_unsat_instances(self, ite):
        checked = 0
        for seed in range(1, 200):
            source = random_instance(seed, 6, 14, ite)
            if ite and "(ite " not in source:
                continue
            context = z3.Context()
            solver = z3.Solver(ctx=context)
            solver.add(z3.parse_smt2_string(source, ctx=context))
            if solver.check() != z3.unsat:
                continue
            with self.subTest(seed=seed):
                certificate, _ = self.check(source)
                self.assertIn("th-lemma", certificate["rule_counts"])
            checked += 1
            if checked == 3:
                break
        self.assertEqual(checked, 3)

    def test_tampered_clauses_never_publish_a_proof(self):
        source = Z3TEST_LRA_INPUTS["lra_farkas"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        node = _th_lemma_nodes(certificate)[0]
        conclusion = certificate["nodes"][node]["arguments"][-1]
        # Weaken the theory lemma to a two-literal clause: the Farkas check fails first.
        tampered = copy.deepcopy(certificate)
        clause = tampered["nodes"][conclusion]
        clause["arguments"] = clause["arguments"][:2]
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "checked.lean"
            with self.assertRaises(proof_to_lean.ReconstructionError):
                proof_to_lean.check_and_write(source, tampered, output)
            self.assertFalse(output.exists())
        # Claim the empty clause directly as a euf lemma: only Lean can reject that.
        tampered = copy.deepcopy(certificate)
        false_node = next(index for index, raw in enumerate(tampered["nodes"])
                          if tampered["declarations"][raw["declaration"]]["kind"] == z3.Z3_OP_FALSE)
        tampered["declarations"].append({"kind": z3.Z3_OP_PR_TH_LEMMA, "name": "th-lemma",
                                         "domain": ["Bool"], "range": "Proof", "parameters": ["euf"]})
        tampered["nodes"].append({"declaration": len(tampered["declarations"]) - 1, "arguments": [false_node]})
        tampered["proof"] = len(tampered["nodes"]) - 1
        tampered["rule_counts"]["th-lemma"] += 1
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "checked.lean"
            with self.assertRaises(subprocess.CalledProcessError):
                proof_to_lean.check_and_write(source, tampered, output)
            self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
