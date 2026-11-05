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


# Difference-logic-shaped inputs. The frontend's tactic preamble used to
# route them to the older theory_arith, whose proof parameters
# (assign-bounds, signed coefficients, antecedent-only weights) the exporter
# normalizes; with the preamble bypassed the smt core's theory_lra proves
# them with bound propagations from premises.
LEGACY_THEORY_ARITH_INPUTS = {
    "dl_fixed_zero": """\
(declare-const x Real)
(declare-const y Real)
(assert (<= x 0.0))
(assert (>= x 0.0))
(assert (<= y 0.0))
(assert (>= y 0.0))
(assert (not (= x y)))
(check-sat)
""",
    "dl_cycle_bool": """\
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(declare-const p Bool)
(assert (or p (<= (- x y) 1.0)))
(assert (or (not p) (<= (- x y) 2.0)))
(assert (<= (- y z) 1.0))
(assert (< (- z x) (- 3.0)))
(check-sat)
""",
    "dl_fixed_value_var": """\
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (<= x 3.0))
(assert (>= x 3.0))
(assert (<= y 3.0))
(assert (>= y 3.0))
(assert (or (not (= x y)) (< z 0.0)))
(assert (> z 1.0))
(check-sat)
""",
}

# theory_lra bound propagations with premises, including fractional weights.
LEGACY_BOUND_INPUTS = {
    "bound_offset": """\
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (= (+ (* 2.0 x) z) 2.0))
(assert (= (+ (* 2.0 y) z) 2.0))
(assert (not (= x y)))
(check-sat)
""",
    "bound_search": """\
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(declare-const p Bool)
(assert (<= (+ x (* 2.0 z)) 6.0))
(assert (>= (+ x (* 2.0 z)) 6.0))
(assert (<= (+ y (* 2.0 z)) 6.0))
(assert (>= (+ y (* 2.0 z)) 6.0))
(assert (or p (not (= x y))))
(assert (or (not p) (> (* 3.0 z) 100.0)))
(assert (< z 1.0))
(check-sat)
""",
}


# A numeral quotient inside a ground atom next to a conflict at level zero:
# the sat.smt arithmetic solver logs its division axiom 2 * (1 / 2) = 1 under
# an arith hint whose first literal is the constant true (the exporter's
# _LRA_DIV_LOG pins the log); the clause log rejected the hint before.
REAL_DIVISION_AXIOM = """\
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (< x x))
(assert (or (< y z) (< (/ 1.0 2.0) 3.0)))
(check-sat)
"""

# Real input with integer numerals and no Real-only logic: Z3 reads each
# numeral where a Real is expected as an Int term under to_real (around the
# whole (- 5 1) and (+ 1 3)), which the exporter rejected as an unsupported
# operator before; it now reads them as QF_LRA does.
COERCED_NUMERAL_INPUTS = {
    "numerals_without_logic": """\
(declare-const x Real)
(declare-const y Real)
(assert (<= (* 2 x) 1))
(assert (> (+ x y) (/ 1 3)))
(assert (< y (- 2)))
(check-sat)
""",
    "real_ite_under_all": """\
(set-logic ALL)
(declare-const x Real)
(declare-const y Real)
(declare-const p Bool)
(assert (= y (ite (> x 1) (- 5 1) (ite p x 2))))
(assert (distinct y 2 (+ 1 3)))
(assert (< 3 (* 3 x) (/ 9 2)))
(check-sat)
""",
    "function_of_numerals_without_logic": """\
(declare-fun f (Real) Real)
(declare-const x Real)
(assert (= x 1))
(assert (= (f 1) 3))
(assert (< (f x) (- x 2)))
(check-sat)
""",
}

# abs over Real: SMT-LIB defines abs on Int only, Z3 accepts it over Real as
# (ite (>= t 0) t (- t)). Without a logic, (abs 3) in a Real position is
# (to_real (abs 3)), read as the Real abs of 3.0.
REAL_ABS_INPUTS = {
    "distance": """\
(declare-const x Real)
(declare-const y Real)
(assert (< (abs (- x y)) 1.0))
(assert (> x 3.0))
(assert (< y 1.0))
(check-sat)
""",
    "triangle_inequality": """\
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(assert (> (abs (+ x y)) (+ (abs x) (abs y))))
(check-sat)
""",
    "symmetry": """\
(set-logic QF_LRA)
(declare-const x Real)
(assert (not (= (abs x) (abs (- x)))))
(check-sat)
""",
    "nested_without_logic": """\
(declare-const x Real)
(declare-const p Bool)
(assert (< (* 2 (abs (ite p x (- x 1)))) (- (abs (abs x)) (abs 3))))
(check-sat)
""",
    "function": """\
(declare-fun f (Real) Real)
(declare-const x Real)
(assert (< (abs (f x)) (- (f (abs x)) (f (abs (- x))))))
(assert (= x (- 2.0)))
(check-sat)
""",
}


def random_abs_instance(seed, variables=3, constraints=8, functions=False):
    """A random problem over Real abs terms, without a logic; None unless unsat."""
    generator = random.Random(seed)
    lines = ["(declare-const x%d Real)" % i for i in range(variables)]
    if functions:
        lines.append("(declare-fun f (Real) Real)")

    def term(v):
        roll = generator.random()
        if roll < 0.25:
            return "(abs x%d)" % v
        if roll < 0.45:
            other = generator.randrange(variables)
            return "(abs (- x%d (* %d x%d) %d))" % (v, generator.choice([-2, 1, 3]), other, generator.randint(-3, 3))
        if functions and roll < 0.6:
            return "(f (abs x%d))" % v if generator.random() < 0.5 else "(abs (f x%d))" % v
        return "x%d" % v

    def atom():
        chosen = generator.sample(range(variables), generator.randint(1, 3))
        terms = " ".join("(* %d %s)" % (generator.choice([-3, -2, -1, 1, 2, 3]), term(v)) for v in chosen)
        relation = generator.choice(["<=", ">=", "<", ">", "="])
        constant = generator.choice(["%d" % generator.randint(-5, 5), "(/ %d 2)" % generator.randint(-5, 5)])
        return "(%s (+ %s 0) %s)" % (relation, terms, constant)

    for _ in range(constraints):
        roll = generator.random()
        if roll < 0.4:
            lines.append("(assert (or %s %s))" % (atom(), atom()))
        elif roll < 0.5:
            lines.append("(assert (not (and %s %s)))" % (atom(), atom()))
        else:
            lines.append("(assert %s)" % atom())
    lines.append("(check-sat)")
    source = "\n".join(lines) + "\n"
    solver = z3.Solver(ctx=z3.Context())
    solver.from_string(source)
    return source if solver.check() == z3.unsat else None


# Seeds of random_abs_instance with long refutations among the first sixty
# without functions and the first forty with (167 to 502 steps on either
# core); every unsat seed there verifies on both cores.
REAL_ABS_SEEDS = (17, 52)
REAL_ABS_FUNCTION_SEEDS = (9, 34)


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

    def test_coerced_numerals_are_bound_to_the_input_by_value(self):
        # The certificate of a script without a logic states the Real terms
        # QF_LRA reads: the certificate of the same assertions under QF_LRA
        # binds to it, and a numeral changed in the certificate does not.
        source = COERCED_NUMERAL_INPUTS["numerals_without_logic"]
        certificate = proof_certificate.export_clause_log_certificate("(set-logic QF_LRA)\n" + source)
        certificate["source_smt2"] = source
        self.assertNotIn("to_real", json.dumps(certificate))
        proof_to_lean.reconstruct(source, certificate)
        certificate = proof_certificate.export_clause_log_certificate(source)
        numerals = {d["name"] for d in certificate["declarations"] if d["kind"] == z3.Z3_OP_ANUM}
        self.assertTrue({"1", "2", "3"} <= numerals, numerals)
        for declaration in certificate["declarations"]:
            if declaration["kind"] == z3.Z3_OP_ANUM and declaration["name"] == "2":
                declaration["name"] = "5"
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "do not match the original input"):
            proof_to_lean.reconstruct(source, certificate)

    def test_real_abs_is_stated_as_its_ite_over_rat(self):
        source = REAL_ABS_INPUTS["distance"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertIn("-- Real abs, which Z3 accepts beyond SMT-LIB, is the ite", text)
        self.assertRegex(text, r"noncomputable def term_\d+ \(_atoms : Nat -> Prop\) \(_vars : Nat -> Rat\) : Rat := "
                               r"\(@ite Rat \(\(term_(\d+) _atoms _vars\) >= \(\(0 : Rat\)\)\) "
                               r"\(Classical.propDecidable _\) \(term_\1 _atoms _vars\) \(-\(term_\1 _atoms _vars\)\)\)")
        self.assertNotIn("Int", text.split("namespace", 1)[1])
        absolute = next(index for index, d in enumerate(certificate["declarations"]) if d["kind"] == z3.Z3_OP_ABS)
        self.assertEqual((certificate["declarations"][absolute]["name"], certificate["declarations"][absolute]["domain"],
                          certificate["declarations"][absolute]["range"]), ("abs", ["Real"], "Real"))
        # Of the integer operators only abs is a Real operator; abs keeps its
        # arity and sort, and a declaration renamed to another operator's
        # name, or replaced by negation, no longer states the input.
        for mutate, message in [
            (lambda d: d.update(kind=z3.Z3_OP_IDIV, name="div", domain=["Real", "Real"]),
             "unsupported arithmetic declaration: div"),
            (lambda d: d.update(kind=z3.Z3_OP_MOD, name="mod", domain=["Real", "Real"]),
             "unsupported arithmetic declaration: mod"),
            (lambda d: d.update(name="div"), "unsupported arithmetic declaration: div"),
            (lambda d: d.update(domain=["Int"]), "arithmetic declarations take Real arguments"),
            (lambda d: d.update(domain=["Real", "Real"]), "invalid arithmetic declaration arity"),
            (lambda d: d.update(kind=z3.Z3_OP_UMINUS, name="-"), "do not match the original input"),
        ]:
            tampered = copy.deepcopy(certificate)
            mutate(tampered["declarations"][absolute])
            with self.subTest(message=message):
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, message):
                    proof_to_lean.reconstruct(source, tampered)

    def test_fragment_and_sort_consistency(self):
        certificate = copy.deepcopy(self.certificate)
        certificate["fragment"] = "propositional"
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "cannot contain arithmetic"):
            proof_to_lean.reconstruct(self.source, certificate)
        certificate = copy.deepcopy(self.certificate)
        certificate["fragment"] = "qf_nia"
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "unsupported certificate header"):
            proof_to_lean.reconstruct(self.source, certificate)
        # The integer fragment is a valid label, but not for Real declarations.
        certificate["fragment"] = "qf_lia"
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "only qf_lia and qf_uflia certificates contain Int"):
            proof_to_lean.reconstruct(self.source, certificate)
        # A Boolean certificate claiming the arithmetic fragment declares no Real symbol.
        boolean = proof_certificate.export_certificate("(declare-const p Bool)(assert p)(assert (not p))")
        boolean["fragment"] = "qf_lra"
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "qf_lra certificates must contain arithmetic"):
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
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "must end in an arithmetic equality"):
            proof_to_lean.reconstruct(self.source, certificate)

    def test_real_ite_is_an_opaque_linear_atom_with_classical_terms(self):
        source = ITE_INPUTS["ite_basic"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        graph = proof_to_lean._validate_graph(source, certificate)
        ite = next(i for i in range(len(graph.nodes)) if graph.kind(i) == z3.Z3_OP_ITE)
        self.assertTrue(graph.is_arith(ite))
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


def flattening_rewrite_instance(variables=9):
    """One wide disjunction Z3's rewriter flattens, with every variable bounded so that it is refuted.

    The disjunction is left-nested over the lower bounds, repeats two of
    them, has a conjunct false by a constant atom ((<= 0 0) under a not)
    and a re-nested conjunction, then the upper bounds; with 2 * variables
    atoms (more than proof_to_lean._NORMALIZED_REWRITE_ATOMS for nine) the
    rewrite takes the normalized path, whose propositional lemma relates
    the two nestings with the duplicates and the false conjunct dropped.
    """
    names = ["x%d" % i for i in range(variables)]
    lows = ["(< %s 5)" % name for name in names]
    highs = ["(> %s 7)" % name for name in names]
    nested = lows[0]
    for low in lows[1:]:
        nested = "(or %s %s)" % (nested, low)
    disjuncts = [nested, lows[0], lows[1],
                 "(and %s (or (not (<= 0 0)) (not (<= 0 0))))" % highs[0],
                 "(and (and %s %s) %s)" % (highs[1], highs[2], highs[3])] + highs[4:]
    lines = ["(set-logic QF_LRA)"] + ["(declare-const %s Real)" % name for name in names]
    lines.append("(assert (or %s))" % " ".join(disjuncts))
    for name in names:
        lines.extend(["(assert (>= %s 5))" % name, "(assert (<= %s 7))" % name])
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


def clock_shaped_rewrite_instance(clocks=3):
    """A disjunction with the Boolean skeleton of the clocksynchro_3clocks rewrite over fresh bounds.

    z3test's smtlib-sample QF_LRA clock_synchro/clocksynchro_3clocks.main_
    invar.base.smt2 asserts a 74-way left-nested disjunction over 85
    distinct arithmetic atoms (three symmetric groups of conjunctions
    sharing atoms, 15 copies of one literal, three conjuncts false by a
    constant atom, a re-nested conjunction), which Z3's rewriter flattens
    to 48 disjuncts; grind failed on the propositional lemma relating the
    two. Here every atom is a bound on its own variable, asserted as a
    unit, so every disjunct is false and the input is unsat. More clocks
    widen the groups (and the copies of the repeated literals) as in the
    8-clock variant.
    """
    counter = [0]

    def atom():
        counter[0] += 1
        return "(<= x%d 5)" % counter[0]

    def neg(formula):
        return "(not %s)" % formula

    clocks = range(clocks)
    a = [atom() for _ in range(13)]
    g, s, h = [atom() for _ in clocks], [atom() for _ in clocks], [atom() for _ in clocks]
    a61, a62, a63, a64, a65, a66 = (atom() for _ in range(6))
    k67, k74, k75, k82, k83, k84 = (atom() for _ in range(6))
    disjuncts = [neg(x) for x in a[:10]] + [neg(a[6])] + [neg(x) for x in a[10:13]] + [neg(a[6])]
    disjuncts += ["(and (or %s %s) %s)" % (neg(g[c]), neg(atom()), neg(s[c])) for c in clocks]
    all_off = neg(g[0])
    for c in clocks[1:]:
        all_off = "(and %s %s)" % (all_off, neg(g[c]))
    disjuncts.append(all_off)
    disjuncts += ["(and %s (or %s %s))" % (g[c], neg(atom()), neg(atom())) for c in clocks]
    disjuncts += ["(and (and %s %s) (or (or %s %s) %s))" % (g[c], neg(h[c]), neg(atom()), neg(atom()), neg(atom()))
                  for c in clocks]
    for _ in range(2):
        disjuncts += ["(and (or %s %s) (or %s %s))" % (neg(h[c]), s[c], neg(atom()), neg(atom())) for c in clocks]
    disjuncts += ["(and %s %s)" % (s[c], neg(atom())) for c in clocks]
    disjuncts += ["(and %s (or %s %s))" % (s[c], neg(atom()), neg(atom())) for c in clocks]
    disjuncts += [neg(a61)] * 3 + [neg(a62)] * 3 + [neg(a[6])] * 9
    disjuncts += ["(and (or %s %s) %s)" % (neg(a63), neg(a64), neg(a65))] * 3
    disjuncts.append("(and (and %s %s) %s)" % (neg(a63), neg(a63), neg(a63)))
    disjuncts += ["(and %s (or (not (<= 0 0)) (not (<= 0 0))))" % a63] * 3
    disjuncts += ["(and (and %s %s) (or (or %s %s) %s))" % (a63, neg(a66), neg(k67), neg(atom()), neg(atom()))
                  for c in clocks]
    disjuncts += ["(and (or %s %s) (or %s %s))" % (neg(a66), a65, neg(k74), neg(k75))] * 3
    disjuncts += ["(and (or %s %s) (or %s %s))" % (neg(a66), a65, neg(atom()), neg(atom())) for c in clocks]
    disjuncts += ["(and %s %s)" % (a65, neg(k82))] * 3
    disjuncts += ["(and %s (or %s %s))" % (a65, neg(k83), neg(k84))] * 3
    assertion = disjuncts[0]
    for disjunct in disjuncts[1:]:
        assertion = "(or %s %s)" % (assertion, disjunct)
    lines = ["(set-logic QF_LRA)"] + ["(declare-const x%d Real)" % i for i in range(1, counter[0] + 1)]
    lines.append("(assert %s)" % assertion)
    lines += ["(assert (<= x%d 5))" % i for i in range(1, counter[0] + 1)]
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


def ite_reshaping_instance(groups=5, condition="and"):
    """A disjunction of conjunctions over Real ite terms that Z3's rewriter reshapes, refuted by unit bounds.

    The shape of the spider QF_LRA benchmarks (mode_cntrl, current_frame):
    per group, y is (ite (not b) (ite (and (< x 3) c) (+ x 1) x) x), which
    the rewriter merges into (ite (or b (not (and (not (<= 3 x)) c))) x
    (+ 1 x)), and w is (ite (not (< z 3)) 3 z), rewritten to (ite (<= 3 z)
    3 z), next to atoms the rewriter flattens and normalizes; with five
    groups the rewrite has 50 atoms. Each disjunct requires (not (< z 3))
    against the unit (< z 3). condition is the connective of the inner
    ite's condition (and, =, or xor).
    """
    names, disjuncts = [], []
    for group in range(groups):
        b, c, x, y, z, w = ("%s%d" % (name, group) for name in "bcxyzw")
        names += [(b, "Bool"), (c, "Bool"), (x, "Real"), (y, "Real"), (z, "Real"), (w, "Real")]
        disjuncts.append(
            "(and (and (and (= %s (ite (not %s) (ite (%s (< %s 3) %s) (+ %s 1) %s) %s))"
            " (not (< %s 3))) (= %s (ite (not (< %s 3)) 3 %s))) (or (or %s (= %s 3)) (= %s 0)))"
            % (y, b, condition, x, c, x, x, x, z, w, z, z, c, y, w))
    assertion = disjuncts[0]
    for disjunct in disjuncts[1:]:
        assertion = "(or %s %s)" % (assertion, disjunct)
    lines = ["(set-logic QF_LRA)"] + ["(declare-const %s %s)" % pair for pair in names]
    lines.append("(assert %s)" % assertion)
    lines += ["(assert (< z%d 3))" % group for group in range(groups)]
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


def selector_ite_instance(groups=3):
    """ite_reshaping_instance's skeleton over a rate selected by comparing a numeral-valued ite.

    The shape of the sal/carpark QF_LRA benchmarks (Carpark2-ausgabe-6): per
    group, a selector s is an ite chain over four flags valued 4 to 0, and
    the rate (ite (= s 4) 20 (ite (= s 3) 10 (ite (= s 2) 5 (ite (= s 1) 2
    1)))) compares it with numerals. Z3's rewriter decides those
    comparisons, turning the rate into an ite over disjunctions of the
    flags' conjunctions, so the two sides' rate ites share no condition.
    """
    names, disjuncts = [], []
    for group in range(groups):
        a, b, c, d, x, y, z, w = ("%s%d" % (name, group) for name in "abcdxyzw")
        names += [(name, "Bool") for name in (a, b, c, d)] + [(name, "Real") for name in (x, y, z, w)]
        cases = []
        for value, flags in zip((4, 3, 2, 1), ((False, False, True), (True, True, False),
                                               (False, True, False), (True, False, False))):
            for first in (True, False):
                literals = [name if flag else "(not %s)" % name
                            for name, flag in zip((a, b, c, d), (first,) + flags)]
                cases.append(("(and (and (and %s %s) %s) %s)" % tuple(literals), value))
        selector = "0"
        for condition, value in reversed(cases):
            selector = "(ite %s %d %s)" % (condition, value, selector)
        rate = "1"
        for value, amount in ((1, 2), (2, 5), (3, 10), (4, 20)):
            rate = "(ite (= %s %d) %d %s)" % (selector, value, amount, rate)
        disjuncts.append(
            "(and (and (and (= %s (+ %s (* %s 10))) (not (< %s 3))) (= %s (ite (not (< %s 3)) 3 %s)))"
            " (or (or %s (= %s 3)) (= %s 0)))" % (y, x, rate, z, w, z, z, a, y, w))
    assertion = disjuncts[0]
    for disjunct in disjuncts[1:]:
        assertion = "(or %s %s)" % (assertion, disjunct)
    lines = ["(set-logic QF_LRA)"] + ["(declare-const %s %s)" % pair for pair in names]
    lines.append("(assert %s)" % assertion)
    lines += ["(assert (< z%d 3))" % group for group in range(groups)]
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


class TestNormalizedRewriteLinks(unittest.TestCase):
    """The prover of a normalized rewrite links the sides' structures equal up to flattening."""

    def test_links_cover_swapped_iffs_double_negation_and_constants(self):
        leaf = [("leaf", index, "_atom%d" % index) for index in range(6)]
        left = ("and", ("iff", leaf[0], ("or", ("or", leaf[1], leaf[2]), leaf[3])),
                ("not", ("not", leaf[4])), ("or", leaf[5], ("false",)))
        right = ("and", leaf[5], leaf[4], ("iff", ("or", leaf[3], leaf[1], leaf[2]), leaf[0]))
        prover = proof_to_lean._PropositionalProver(left, right, classical=True, links=True)
        self.assertEqual(prover.representatives[left], prover.representatives[right])
        lines = prover.equivalence(left, right)
        self.assertIsNotNone(lines)
        text = "\n".join(lines)
        self.assertIn("(Iff.trans (iff_congr ", text)  # the iff with its sides swapped
        self.assertIn(") iff_comm)", text)
        self.assertIn("refine Classical.byContradiction (fun (_f", text)
        source = ["theorem linked (_atoms : Nat -> Prop)%s" % "".join(" (%s : Prop)" % name for _, _, name in leaf),
                  "    : %s := by" % proof_to_lean._render_structure(("iff", left, right))]
        source += ["  " + line for line in lines]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "linked.lean"
            path.write_text("\n".join(source) + "\n\n#print axioms linked\n")
            result = subprocess.run([str(proof_to_lean._CHECK_LEAN), str(path)], text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, (result.stdout + result.stderr)[-3000:])

    def test_disjuncts_of_a_wide_false_disjunction_are_refuted_from_tails(self):
        # Refuting disjunct i from the disjunction itself took i steps of
        # mt Or.inr; from the tail bound a stride before it, at most a stride.
        width = 4 * proof_to_lean._AND_ELIM_STRIDE + 3
        leaves = [("leaf", index, "_atom%d" % index) for index in range(width)]
        # The last two disjuncts, assumed, are refuted from the negated disjunction.
        negation, last = ("not", ("or",) + tuple(leaves)), ("or", leaves[-1], leaves[-2])
        prover = proof_to_lean._PropositionalProver(last, negation, classical=True)
        lines = prover.refutation(last, [(negation, "_h")])
        self.assertIsNotNone(lines)
        depths = [line.count("(mt (@Or.inr _ _)") for line in lines]
        self.assertEqual(depths.count(proof_to_lean._AND_ELIM_STRIDE), 4)  # the tails
        self.assertLessEqual(max(depths), proof_to_lean._AND_ELIM_STRIDE)
        source = ["theorem refuted (_atoms : Nat -> Prop)%s" % "".join(" (%s : Prop)" % name for _, _, name in leaves),
                  "    (_h : %s) : Not %s := by" % tuple(proof_to_lean._render_structure(structure)
                                                      for structure in (negation, last))]
        source += ["  " + line for line in lines]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "refuted.lean"
            path.write_text("\n".join(source) + "\n")
            result = subprocess.run([str(proof_to_lean._CHECK_LEAN), str(path)], text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, (result.stdout + result.stderr)[-3000:])


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

    def test_the_real_division_axiom_verifies(self):
        certificate, report = self.check(REAL_DIVISION_AXIOM)
        self.assertEqual(certificate["fragment"], "qf_lra")
        self.assertIn(["arith"], [d["parameters"] for d in certificate["declarations"] if d["name"] == "th-lemma"])
        self.assertIn(_STANDARD_AXIOMS, report)

    def test_real_abs_verifies(self):
        # Rejected as "abs over Real" before; the clause log has the
        # rewriter's ite, the statement the input's abs as the ite over Rat.
        sources = list(REAL_ABS_INPUTS.items())
        sources += [("seed%d" % seed, random_abs_instance(seed)) for seed in REAL_ABS_SEEDS]
        sources += [("function_seed%d" % seed, random_abs_instance(seed, functions=True))
                    for seed in REAL_ABS_FUNCTION_SEEDS]
        for name, source in sources:
            with self.subTest(name=name):
                certificate, report = self.check(source)
                self.assertEqual(certificate["fragment"], "qf_uflra" if "function" in name else "qf_lra")
                self.assertIn(_STANDARD_AXIOMS, report)
                self.assertIn("th-lemma", certificate["rule_counts"])

    def test_untrimmed_real_abs_axioms_verify(self):
        # Seed 59's log keeps (abs x1) and an arith lemma of its two case
        # axioms, which trimming drops; replaying it untrimmed checks that
        # lemma, over the logged abs rather than z3py's (ite (> t 0) t (- t)).
        # QF_LRA reads the numerals as Real ones; without a logic the
        # untrimmed log has to_real numerals, which the replay rejects.
        source = "(set-logic QF_LRA)\n" + random_abs_instance(59)
        with patch.object(proof_clause_log, "_TRIM_THRESHOLD", float("inf")):
            certificate, report = self.check(source)
        declarations = certificate["declarations"]
        used = {node["declaration"] for node in certificate["nodes"]}
        self.assertIn(("abs", ["Real"]), [(declarations[i]["name"], declarations[i]["domain"]) for i in used])
        self.assertIn(["arith"], [declarations[i]["parameters"] for i in used if declarations[i]["name"] == "th-lemma"])
        self.assertNotIn(z3.Z3_OP_GT, [declarations[i]["kind"] for i in used])
        self.assertIn(_STANDARD_AXIOMS, report)

    def test_integer_numerals_in_real_terms_verify(self):
        for name, source in COERCED_NUMERAL_INPUTS.items():
            with self.subTest(name=name):
                certificate, report = self.check(source)
                self.assertEqual(certificate["fragment"], "qf_uflra" if "function" in name else "qf_lra")
                self.assertIn(_STANDARD_AXIOMS, report)
                self.assertIn("th-lemma", certificate["rule_counts"])

    def test_boolean_inputs_through_the_clause_log(self):
        from test_proof_to_lean import Z3TEST_LEAN_INPUTS
        for name, source in Z3TEST_LEAN_INPUTS.items():
            with self.subTest(name=name):
                source = "\n".join(line for line in source.splitlines() if "set-option" not in line) + "\n"
                certificate, _ = self.check(source)
                self.assertEqual(certificate["fragment"], "propositional")

    def test_inputs_with_ignored_options_through_the_clause_log(self):
        # z3test regressions kept verbatim: output, model, and search options,
        # a named assertion with get-unsat-core, and a par-or tactic in
        # check-sat-using are ignored; the executable sees the assertions only.
        from test_proof_to_lean import CONFIGURED_INPUTS
        fragments = {"3220": "propositional", "3434": "propositional", "z3.4": "propositional",
                     "z3.5": "propositional", "core": "qf_lra", "strategy-par-or-2": "qf_lia"}
        for name, source in CONFIGURED_INPUTS.items():
            with self.subTest(name=name):
                certificate, report = self.check(source)
                self.assertEqual(certificate["fragment"], fragments[name])
                self.assertEqual(certificate["source_smt2"], source)
                if fragments[name] != "propositional":
                    self.assertIn(_STANDARD_AXIOMS, report)
        # The named (= 1 0) folds to false in the rewriter; the abs conflict
        # needs the arithmetic solver.
        self.assertIn("th-lemma", proof_certificate.export_clause_log_certificate(
            CONFIGURED_INPUTS["strategy-par-or-2"])["rule_counts"])

    def test_boolean_input_with_a_query_inside_a_scope_through_the_clause_log(self):
        # z3test 3632.smt2 kept verbatim: the only check-sat sits inside
        # (push 1), so no index is needed; the unused BitVec constant does
        # not affect the fragment. The clause log proves it with a def-axiom
        # and a distinct conflict (the legacy core's proof, wide rewrites, is
        # checked in test_proof_to_lean_integration.py).
        from test_proof_to_lean import INCREMENTAL_INPUTS
        source, query = INCREMENTAL_INPUTS["3632"]
        certificate, _ = self.check(source)
        self.assertEqual((certificate["fragment"], certificate["query"], query), ("propositional", 0, 0))
        self.assertEqual(len(certificate["assertions"]), 2)

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

    def _normalized_lemma(self, source):
        certificate = proof_certificate.export_clause_log_certificate(source)
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertEqual(text.count("private theorem normalized_rewrite_"), 1)
        return text.split("private theorem normalized_rewrite_", 1)[1].split("\n\n", 1)[0]

    def test_normalized_rewrites_are_proved_by_propagation_with_grind_as_the_fallback(self):
        # The propositional lemma of a normalized rewrite is a direct term
        # over the let-named structures (case analysis on the assumed
        # disjunction, propagation, the constant atoms' values: here a
        # conjunct under (Not True) is dropped, duplicates and the nesting
        # of or and and change), with grind as the `first` fallback; with
        # the prover disabled the lemma is grind alone, and Lean proves this
        # small instance either way.
        source = flattening_rewrite_instance()
        lemma = self._normalized_lemma(source)
        self.assertIn("(Not True)", lemma)
        self.assertIn("  by first\n    | (let _s0 : Prop := ", lemma)
        # The sides' structures equal up to flattening are linked first,
        # each link proved by contradiction (see _equivalent_structures).
        self.assertRegex(lemma, r"\n       have _f\d+ : _s\d+ := by\n         refine Iff.intro ")
        self.assertIn("refine Classical.byContradiction (fun (_f", lemma)
        self.assertRegex(lemma, r"\n       refine Iff.intro \(fun \(_f\d+ : _s")
        self.assertTrue(lemma.endswith(")\n    | grind (splits := 64)"), lemma[-200:])
        self.assertNotIn("Classical.em", lemma)
        self.check(source)
        with patch.object(proof_to_lean._PropositionalProver, "equivalence", lambda self, left, right: None):
            lemma = self._normalized_lemma(source)
            self.assertIn("  by grind (splits := 64)", lemma)
            self.assertNotIn("Iff.intro", lemma)
            self.check(source)

    def test_clock_shaped_flattening_rewrite_verifies(self):
        # The skeleton of the clocksynchro_3clocks rewrite (see
        # clock_shaped_rewrite_instance): the direct term proves it where
        # `grind (splits := 64)` failed on the same lemma, and the whole
        # certificate verifies; the term stays far below the character
        # budget with the structures let-named (it exhausted the budget
        # after a thousand steps with every step stating its proposition,
        # and the step budget when splitting on atoms instead of the
        # disjunction's cases).
        source = clock_shaped_rewrite_instance()
        lemma = self._normalized_lemma(source)
        self.assertIn("  by first\n    | (let _s0 : Prop := ", lemma)
        self.assertGreaterEqual(lemma.count("(_atom84 : Prop)"), 1)
        self.assertNotIn("Classical.em", lemma)
        self.assertLess(len(lemma), proof_to_lean._STRUCTURAL_REWRITE_CHARS // 2)
        self.check(source)

    def test_wide_clock_shaped_flattening_rewrite_verifies(self):
        # The same skeleton with 16 clocks (a 165-way flattened disjunction):
        # the search alone exhausted its character budget (each case of one
        # side's disjunction walked the other side's left-nested chain, and
        # refuting disjunct i of a false disjunction took i steps), so the
        # lemma was grind's, which failed after 106 s, as on the 250-way
        # rewrite of clocksynchro_8clocks.main_invar. With the sides' equal
        # structures linked and the false disjunction's tails bound, the
        # proof is linear and checks in seconds.
        source = clock_shaped_rewrite_instance(clocks=16)
        lemma = self._normalized_lemma(source)
        self.assertIn("  by first\n    | (let _s0 : Prop := ", lemma)
        # Every disjunct is refuted from a tail at most a stride before it.
        self.assertLessEqual(max(line.count("(mt (@Or.inr _ _)") for line in lemma.splitlines()),
                             2 * proof_to_lean._AND_ELIM_STRIDE)
        self.assertLess(len(lemma), proof_to_lean._STRUCTURAL_REWRITE_CHARS)
        certificate, report = self.check(source)
        self.assertIn(_STANDARD_AXIOMS, report)

    def test_rewrite_reshaping_ite_terms_verifies(self):
        # Z3's rewriter reshapes the ite terms of an assertion (see
        # ite_reshaping_instance), so the two sides' ites differ and
        # generalizing them apart fails; grind over the unfolded rewrite
        # exhausted its heartbeats (as on the spider QF_LRA benchmarks
        # mode_cntrl and current_frame). Keyed by their value tables, the
        # ites of both sides are one opaque term per pair, each atom's lemma
        # proves its ite equal to the representative, and the propositional
        # lemma links the flattened structures.
        source = ite_reshaping_instance()
        for core in ("clause-log", "legacy"):
            with self.subTest(core=core):
                certificate = (proof_certificate.export_clause_log_certificate(source) if core == "clause-log"
                               else proof_certificate.export_certificate(source))
                text = proof_to_lean.reconstruct(source, certificate)
                self.assertIn("private theorem normalized_rewrite_", text)
                atom_lemmas = text.split("private theorem normalized_atom_")[1:]
                self.assertTrue(any("(@ite Rat" in lemma.split(":= by", 1)[0] for lemma in atom_lemmas))
                certificate, report = self.check(source, core)
                self.assertIn(_STANDARD_AXIOMS, report)

    def test_rewrite_reshaping_ites_with_iff_and_xor_conditions_verifies(self):
        # With an iff or xor inner condition, the value tables still match
        # the two sides' ites, but grind alone cannot prove the atom over
        # the merged ite equal to its normalized form; the atom lemma falls
        # back to splitting every ite of its goal. Before that fallback the
        # clause-log export failed in normalized_atom (and at the base
        # commit, grind over the whole rewrite timed out).
        for condition in ("=", "xor"):
            with self.subTest(condition=condition):
                source = ite_reshaping_instance(condition=condition)
                certificate = proof_certificate.export_clause_log_certificate(source)
                text = proof_to_lean.reconstruct(source, certificate)
                self.assertIn("private theorem normalized_rewrite_", text)
                self.assertIn("    | ((repeat' split) <;> grind)", text)
                certificate, report = self.check(source)
                self.assertIn(_STANDARD_AXIOMS, report)

    def test_rewrite_over_numeral_comparisons_of_selector_ites_verifies(self):
        # Z3's rewriter decides the rate's (= selector k) conditions (see
        # selector_ite_instance), so the left's rate ite is over comparisons
        # of the selector ite and the right's over the flags alone. With the
        # comparisons as independent leaves the tables differed, and grind
        # over the unfolded rewrite timed out after 60 s, as on
        # Carpark2-ausgabe-6. Evaluated in the table, they key the two rate
        # ites alike, and the atom lemmas relating them are proved by cases
        # on the four flags (grind and splitting every ite both fail there).
        source = selector_ite_instance()
        for core in ("clause-log", "legacy"):
            with self.subTest(core=core):
                certificate = (proof_certificate.export_clause_log_certificate(source) if core == "clause-log"
                               else proof_certificate.export_certificate(source))
                text = proof_to_lean.reconstruct(source, certificate)
                if core == "clause-log":
                    self.assertIn("private theorem normalized_rewrite_", text)
                    self.assertIn("    | (by_cases _c", text)
                    # The linter is relaxed only for the lemmas with the split.
                    self.assertEqual(text.count("set_option linter.unusedSimpArgs false in"),
                                     text.count("    | (by_cases _c"))
                certificate, report = self.check(source, core)
                self.assertIn(_STANDARD_AXIOMS, report)

    def test_ite_value_tables_evaluate_comparisons_of_numeral_ites(self):
        # Each rate ite over (= selector k) conditions shares its table with
        # the rewritten rate ite, whose conditions are over the flags alone;
        # the selectors are keyed among themselves.
        groups = 3
        source = selector_ite_instance(groups)
        certificate = proof_certificate.export_clause_log_certificate(source)
        graph = proof_to_lean._validate_graph(source, certificate)
        rewrite = max((node for node in range(len(graph.nodes)) if graph.decl(node).name == "rewrite"),
                      key=lambda node: len(proof_to_lean._reachable(graph, graph.conclusion(node))[0]))
        conclusion = graph.conclusion(rewrite)
        ites = proof_to_lean._arith_ites(graph, proof_to_lean._reachable(graph, conclusion)[0])
        atoms = [formula for formula in proof_to_lean._reachable_outside(graph, conclusion, ites)
                 if graph.kind(formula) == z3.Z3_OP_EQ and graph.is_arith(graph.arguments(formula)[0])]
        representatives = proof_to_lean._ite_representatives(graph, atoms)
        self.assertEqual(set(representatives), ites)

        def compares_selector(ite):
            nodes = proof_to_lean._reachable(graph, graph.arguments(ite)[0])[0]
            return any(graph.kind(node) == z3.Z3_OP_EQ and proof_to_lean._numeral_ite(graph, graph.arguments(node)[0])
                       for node in nodes)

        chains = [ite for ite in ites if compares_selector(ite)]
        self.assertEqual(len(chains), 4 * groups)
        rates = [ite for ite in chains if not any(ite in graph.arguments(other) for other in chains)]
        self.assertEqual(len(rates), groups)
        for rate in rates:
            partners = [ite for ite in ites if ite != rate and representatives[ite] == representatives[rate]]
            self.assertTrue(partners)
            for partner in partners:
                condition = proof_to_lean._reachable(graph, graph.arguments(partner)[0])[0]
                self.assertFalse(proof_to_lean._arith_ites(graph, condition))
        # An ite with a variable branch (the w ites) is no numeral ite, so a
        # comparison of it would stay a leaf.
        variable_branch = [ite for ite in ites if graph.kind(graph.arguments(ite)[2]) == z3.Z3_OP_UNINTERPRETED]
        self.assertTrue(variable_branch)
        self.assertFalse(any(proof_to_lean._numeral_ite(graph, ite) for ite in variable_branch))

    def test_ite_value_tables_key_reshaped_ites_alike(self):
        # Per group, the y ite (nested on the left, merged on the right)
        # and the w ite (its condition negated on the left) each have one
        # table for both shapes; the left's inner ite has a table of its own.
        groups = 3
        source = ite_reshaping_instance(groups)
        certificate = proof_certificate.export_clause_log_certificate(source)
        graph = proof_to_lean._validate_graph(source, certificate)
        rewrite = max((node for node in range(len(graph.nodes)) if graph.decl(node).name == "rewrite"),
                      key=lambda node: len(proof_to_lean._reachable(graph, graph.conclusion(node))[0]))
        conclusion = graph.conclusion(rewrite)
        ites = proof_to_lean._arith_ites(graph, proof_to_lean._reachable(graph, conclusion)[0])
        atoms = [formula for formula in proof_to_lean._reachable_outside(graph, conclusion, ites)
                 if graph.kind(formula) == z3.Z3_OP_EQ and graph.is_arith(graph.arguments(formula)[0])]
        representatives = proof_to_lean._ite_representatives(graph, atoms)
        self.assertEqual(set(representatives), ites)
        classes = {}
        for ite, representative in representatives.items():
            classes.setdefault(representative, []).append(ite)
        self.assertEqual(sorted(len(members) for members in classes.values()), [1] * groups + [2] * 2 * groups)
        for members in classes.values():  # one table, but the conditions differ
            self.assertEqual(len({graph.arguments(ite)[0] for ite in members}), len(members))

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
        # Trimmed logs of the 6-variable instances stay below the threshold.
        from test_proof_to_lean_uf import outlined_lemma_sizes, _proof_steps
        for seed in range(1, 200):
            source = random_instance(seed, 10, 30, ite=True)
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

    def check_random_unsat_instances(self, ite, core="clause-log", count=3, variables=6, constraints=14):
        checked = 0
        for seed in range(1, 200):
            source = random_instance(seed, variables, constraints, ite)
            if ite and "(ite " not in source:
                continue
            context = z3.Context()
            solver = z3.Solver(ctx=context)
            solver.add(z3.parse_smt2_string(source, ctx=context))
            if solver.check() != z3.unsat:
                continue
            with self.subTest(seed=seed):
                certificate, _ = self.check(source, core)
                self.assertIn("th-lemma", certificate["rule_counts"])
            checked += 1
            if checked == count:
                break
        self.assertEqual(checked, count)

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


def _th_lemma_parameters(certificate, node):
    return certificate["declarations"][certificate["nodes"][node]["declaration"]]["parameters"]


class TestLegacyArithmeticValidation(unittest.TestCase):
    """Certificates from the smt core's proof object: th-lemma steps with premises, checked before Lean."""

    @classmethod
    def setUpClass(cls):
        cls.source = Z3TEST_LRA_INPUTS["lra_farkas"]
        cls.certificate = proof_certificate.export_certificate(cls.source)
        cls.text = proof_to_lean.reconstruct(cls.source, cls.certificate)

    def test_th_lemmas_with_premises_are_implications_applied_to_their_steps(self):
        certificate = self.certificate
        self.assertEqual(certificate["fragment"], "qf_lra")
        conflicts = [node for node in _th_lemma_nodes(certificate)
                     if _th_lemma_parameters(certificate, node)[0] == "farkas"
                     and certificate["nodes"][node]["arguments"][:-1]]
        self.assertTrue(conflicts)
        for node in conflicts:
            premises = certificate["nodes"][node]["arguments"][:-1]
            parameters = _th_lemma_parameters(certificate, node)
            self.assertEqual(parameters[0], "farkas")
            self.assertEqual(len(parameters) - 1, len(premises))  # a conflict concludes false: no clause literals
            self.assertRegex(self.text, (
                r"private theorem th_lemma_%d \(_atoms : Nat -> Prop\) \(_vars : Nat -> Rat\)\n"
                r"    : (\(formula_\d+ _atoms _vars\) -> ){%d}\(formula_\d+ _atoms _vars\) := by\n"
                r"  unfold [^\n]*\n  grind") % (node, len(premises)))
            self.assertIn("(th_lemma_%d _atoms _vars%s)" % (node, "".join(" _step_%d" % p for p in premises)), self.text)
        # Congruence through an arithmetic operator or comparison is a grind
        # lemma taking the argument equalities as premises; Boolean congruence
        # keeps its explicit terms.
        self.assertRegex(self.text, r"private theorem monotonicity_\d+ \(_atoms : Nat -> Prop\) \(_vars : Nat -> Rat\)\n"
                                    r"    : \(formula_\d+ _atoms _vars\) -> \(formula_\d+ _atoms _vars\) := by")
        self.assertRegex(self.text, r"\(monotonicity_\d+ _atoms _vars _step_\d+\)")
        self.assertIn("theorem unsat (_atoms : Nat -> Prop) (_vars : Nat -> Rat)", self.text)
        self.assertNotIn("sorry", self.text)
        self.assertNotIn("axiom ", self.text)

    def test_tampered_legacy_coefficients_are_rejected_before_lean(self):
        node = next(n for n in _th_lemma_nodes(self.certificate)
                    if _th_lemma_parameters(self.certificate, n)[0] == "farkas"
                    and self.certificate["nodes"][n]["arguments"][:-1])
        declaration = self.certificate["nodes"][node]["declaration"]
        parameters = _th_lemma_parameters(self.certificate, node)
        for mutate, message in [
            (lambda p: p[:1] + [str(Fraction(p[1]) * 2)] + p[2:], "do not refute"),
            (lambda p: p[:-1], "coefficients for"),
            (lambda p: p + ["1"], "coefficients for"),
            (lambda p: ["bound"] + p[1:-1] + [str(Fraction(p[-1]) * 3)], "do not refute"),
            (lambda p: ["triangle-eq"], "without premises"),
            (lambda p: ["implied-eq"], "must end in an arithmetic equality"),
        ]:
            tampered = copy.deepcopy(self.certificate)
            tampered["declarations"][declaration]["parameters"] = mutate(list(parameters))
            with self.subTest(parameters=tampered["declarations"][declaration]["parameters"]):
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, message):
                    proof_to_lean.reconstruct(self.source, tampered)
        # Dropping a premise leaves the declaration's arity unsatisfied.
        tampered = copy.deepcopy(self.certificate)
        tampered["nodes"][node]["arguments"] = tampered["nodes"][node]["arguments"][1:]
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "wrong number of arguments"):
            proof_to_lean.reconstruct(self.source, tampered)
        # A premise that is not an arithmetic atom (a step concluding a Boolean
        # equivalence) cannot enter the combination.
        tampered = copy.deepcopy(self.certificate)
        declarations, nodes = tampered["declarations"], tampered["nodes"]
        arguments = list(nodes[node]["arguments"])
        equivalence = next(
            index for index, raw in enumerate(nodes[:node])
            if declarations[raw["declaration"]]["range"] == "Proof"
            and declarations[nodes[raw["arguments"][-1]]["declaration"]]["kind"] == z3.Z3_OP_EQ
            and declarations[nodes[nodes[raw["arguments"][-1]]["arguments"][0]]["declaration"]]["range"] == "Bool")
        arguments[0] = equivalence
        nodes[node]["arguments"] = arguments
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "not a linear arithmetic atom"):
            proof_to_lean.reconstruct(self.source, tampered)

    def test_bound_propagations_weight_premises_then_the_consequent(self):
        for name, source in LEGACY_BOUND_INPUTS.items():
            with self.subTest(name=name):
                certificate = proof_certificate.export_certificate(source)
                bounds = [node for node in _th_lemma_nodes(certificate)
                          if _th_lemma_parameters(certificate, node)[0] == "bound"]
                self.assertTrue(bounds)
                for node in bounds:
                    premises = certificate["nodes"][node]["arguments"][:-1]
                    self.assertTrue(premises)
                    parameters = _th_lemma_parameters(certificate, node)
                    self.assertEqual(len(parameters) - 1, len(premises) + 1)
                    self.assertEqual(parameters[-1], "1")
                    self.assertTrue(all(Fraction(c) > 0 for c in parameters[1:]))
                text = proof_to_lean.reconstruct(source, certificate)
                self.assertIn("private theorem th_lemma_", text)
                node = bounds[0]
                tampered = copy.deepcopy(certificate)
                parameters = list(_th_lemma_parameters(certificate, node))
                parameters[1] = str(Fraction(parameters[1]) / 7)
                tampered["declarations"][tampered["nodes"][node]["declaration"]]["parameters"] = parameters
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "do not refute"):
                    proof_to_lean.reconstruct(source, tampered)

    def test_refined_bounds_carry_coefficients(self):
        # smt.arith.propagation_mode=2 lets theory_lra assert fresh bound
        # literals (refine_bound), which are justified like every other LP
        # bound propagation: no bare (_ th-lemma arith) reaches the proof.
        z3.set_param("smt.arith.propagation_mode", 2)
        try:
            sources = {**Z3TEST_LRA_INPUTS, **LEGACY_BOUND_INPUTS}
            sources.update(("random%d" % seed, random_instance(seed, 6, 14)) for seed in range(40))
            for name, source in sources.items():
                context = z3.Context()
                solver = z3.Solver(ctx=context)
                solver.add(z3.parse_smt2_string(source, ctx=context))
                if solver.check() != z3.unsat:
                    continue
                with self.subTest(name=name):
                    certificate = proof_certificate.export_certificate(source)
                    for node in _th_lemma_nodes(certificate):
                        parameters = _th_lemma_parameters(certificate, node)
                        self.assertIn(parameters[0], ("farkas", "bound", "triangle-eq", "smt", "implied-eq"))
                        if parameters[0] == "bound":
                            self.assertEqual(parameters[-1], "1")
                    proof_to_lean.reconstruct(source, certificate)
        finally:
            z3.set_param("smt.arith.propagation_mode", 1)

    def test_difference_logic_inputs_use_bound_propagations_from_premises(self):
        # theory_arith's assign-bounds and eq-propagate conventions are
        # exercised on constructed declarations in test_proof_certificate.py;
        # the direct smt core path proves these inputs with theory_lra.
        source = LEGACY_THEORY_ARITH_INPUTS["dl_fixed_zero"]
        certificate = proof_certificate.export_certificate(source)
        graph = proof_to_lean._validate_graph(source, certificate)
        hints = {_th_lemma_parameters(certificate, node)[0] for node in _th_lemma_nodes(certificate)}
        self.assertIn("bound", hints)
        self.assertLessEqual(hints, {"bound", "farkas", "triangle-eq"})
        propagations = 0
        for node in _th_lemma_nodes(certificate):
            parameters = _th_lemma_parameters(certificate, node)
            if parameters[0] == "triangle-eq":
                continue
            premises = certificate["nodes"][node]["arguments"][:-1]
            literals = list(graph.clause(graph.conclusion(node)))
            self.assertEqual(len(parameters) - 1, len(premises) + len(literals))
            self.assertTrue(all(Fraction(c) > 0 for c in parameters[1:]))
            if parameters[0] == "bound":
                # The propagated bound is a unit clause with the weight 1 for
                # the consequent after one weight per premise.
                self.assertTrue(premises)
                self.assertEqual(len(literals), 1)
                self.assertEqual(parameters[-1], "1")
                propagations += 1
        self.assertTrue(propagations)
        proof_to_lean.reconstruct(source, certificate)

    def test_triangle_eq_shape_is_checked(self):
        source = "(declare-const x Real)(declare-const y Real)(declare-const z Real)(assert (distinct x y z))(assert (<= x y))(assert (<= y x))"
        certificate = proof_certificate.export_certificate(source)
        nodes = [node for node in _th_lemma_nodes(certificate) if _th_lemma_parameters(certificate, node) == ["triangle-eq"]]
        self.assertTrue(nodes)
        proof_to_lean.reconstruct(source, certificate)
        node = nodes[0]
        clause = certificate["nodes"][node]["arguments"][-1]
        equality_literals = [arg for arg in certificate["nodes"][clause]["arguments"]
                             if certificate["declarations"][certificate["nodes"][arg]["declaration"]]["kind"] == z3.Z3_OP_EQ]
        self.assertEqual(len(equality_literals), 1)
        tampered = copy.deepcopy(certificate)
        tampered["nodes"][clause]["arguments"] = [arg for arg in tampered["nodes"][clause]["arguments"]
                                                  if arg not in equality_literals]
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "exactly one Real equality"):
            proof_to_lean.reconstruct(source, tampered)
        tampered = copy.deepcopy(certificate)
        tampered["declarations"][tampered["nodes"][node]["declaration"]]["parameters"] = ["triangle-eq", "1"]
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "takes no coefficients"):
            proof_to_lean.reconstruct(source, tampered)

    def test_ite_terms_are_certified_without_definitions(self):
        # The frontend's tactic preamble used to name ite terms by intro-def,
        # a definition the certificate cannot tie to the input; the smt core
        # reached directly keeps the ite terms and proves their gate clauses
        # as def-axioms.
        for name, source in ITE_INPUTS.items():
            with self.subTest(name=name):
                certificate = proof_certificate.export_certificate(source)
                self.assertNotIn("intro-def", certificate["rule_counts"])
                self.assertIn("def-axiom", certificate["rule_counts"])
                self.assertNotIn("!", json.dumps(certificate["declarations"]))
                proof_to_lean.reconstruct(source, certificate)


class TestLegacyArithmeticLeanIntegration(unittest.TestCase):
    """End-to-end through the smt core's proof object: certificate, Lean reconstruction, kernel check."""

    check = TestArithmeticLeanIntegration.check
    check_random_unsat_instances = TestArithmeticLeanIntegration.check_random_unsat_instances

    def test_lp_input_without_its_logical_premise_never_publishes_a_proof(self):
        source = Z3TEST_LRA_INPUTS["lra_farkas"]
        certificate = proof_certificate.export_certificate(source)
        node = next(node for node in _th_lemma_nodes(certificate)
                    if _th_lemma_parameters(certificate, node) == ["smt"]
                    and len(certificate["nodes"][node]["arguments"]) == 2)
        raw = certificate["nodes"][node]
        raw["arguments"] = raw["arguments"][-1:]
        certificate["declarations"][raw["declaration"]]["domain"] = ["Bool"]
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "checked.lean"
            with self.assertRaises(subprocess.CalledProcessError) as error:
                proof_to_lean.check_and_write(source, certificate, output)
            self.assertIn("`grind` failed", error.exception.stdout)
            self.assertFalse(output.exists())

    def test_documented_lra_inputs_verify_through_the_legacy_core(self):
        # Real ite terms included: the smt core reached directly keeps them
        # (no intro-def) and proves their gate clauses as def-axioms.
        inputs = {**Z3TEST_LRA_INPUTS, **ITE_INPUTS, **ITE_REWRITTEN_INPUTS}
        for name, source in inputs.items():
            with self.subTest(name=name):
                certificate, report = self.check(source, core="legacy")
                self.assertEqual(certificate["fragment"], "qf_lra")
                self.assertIn(_STANDARD_AXIOMS, report)
                if name in Z3TEST_LRA_INPUTS:
                    self.assertIn("rewrite", certificate["rule_counts"])  # the preprocessing the clause log never sees

    def test_the_real_division_axiom_input_verifies_through_the_legacy_core(self):
        certificate, report = self.check(REAL_DIVISION_AXIOM, core="legacy")
        self.assertEqual(certificate["fragment"], "qf_lra")
        self.assertIn(_STANDARD_AXIOMS, report)

    def test_real_abs_verifies_through_the_legacy_core(self):
        sources = list(REAL_ABS_INPUTS.items())
        sources += [("seed%d" % seed, random_abs_instance(seed)) for seed in REAL_ABS_SEEDS]
        sources += [("function_seed%d" % seed, random_abs_instance(seed, functions=True))
                    for seed in REAL_ABS_FUNCTION_SEEDS]
        for name, source in sources:
            with self.subTest(name=name):
                certificate, report = self.check(source, core="legacy")
                self.assertEqual(certificate["fragment"], "qf_uflra" if "function" in name else "qf_lra")
                self.assertIn(_STANDARD_AXIOMS, report)

    def test_integer_numerals_in_real_terms_verify_through_the_legacy_core(self):
        for name, source in COERCED_NUMERAL_INPUTS.items():
            with self.subTest(name=name):
                certificate, report = self.check(source, core="legacy")
                self.assertIn(certificate["fragment"], ("qf_lra", "qf_uflra"))
                self.assertIn(_STANDARD_AXIOMS, report)

    def test_bound_propagations_and_theory_arith_inputs_verify(self):
        for name, source in {**LEGACY_BOUND_INPUTS, **LEGACY_THEORY_ARITH_INPUTS}.items():
            with self.subTest(name=name):
                certificate, report = self.check(source, core="legacy")
                self.assertIn(_STANDARD_AXIOMS, report)
                self.assertIn("th-lemma", certificate["rule_counts"])

    def test_random_instances_through_the_legacy_core(self):
        self.check_random_unsat_instances(ite=False, core="legacy", count=4, variables=10, constraints=30)

    def test_small_chunks_cut_every_legacy_lemma_shape(self):
        from test_proof_to_lean_uf import outlined_lemma_sizes, _proof_steps
        with patch.object(proof_to_lean, "_OUTLINE_PROOF_STEPS", 0), \
                patch.object(proof_to_lean, "_OUTLINE_CHUNK_STEPS", 3):
            for name in ("lra_boolean_structure", "lra_equality", "bound_offset", "dl_cycle_bool"):
                source = {**Z3TEST_LRA_INPUTS, **LEGACY_BOUND_INPUTS, **LEGACY_THEORY_ARITH_INPUTS}[name]
                with self.subTest(input=name):
                    certificate, report = self.check(source, core="legacy")
                    self.assertIn(_STANDARD_AXIOMS, report)
                    sizes = outlined_lemma_sizes(proof_to_lean.reconstruct(source, certificate))
                    self.assertLessEqual(max(sizes), 3)
                    self.assertEqual(sum(sizes), _proof_steps(certificate))


if __name__ == "__main__":
    unittest.main()
