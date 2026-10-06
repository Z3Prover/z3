############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Tests for the QF_LRA slice of the Lean reconstruction: validation without
# Lean, and end-to-end checks that need the z3 executable and the pinned
# Lean toolchain.
############################################
import copy
import hashlib
import json
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import unittest

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


def random_instance(seed, variables, constraints):
    """A random QF_LRA problem; callers filter for unsat ones."""
    generator = random.Random(seed)
    lines = ["(set-logic QF_LRA)"] + ["(declare-const x%d Real)" % i for i in range(variables)]

    def atom():
        chosen = generator.sample(range(variables), generator.randint(2, 3))
        terms = " ".join("(* %d.0 x%d)" % (generator.choice([-3, -2, -1, 1, 2, 3]), v) for v in chosen)
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

    def test_random_instances_with_learned_clauses_and_deletions(self):
        checked = 0
        for seed in range(1, 200):
            source = random_instance(seed, 6, 14)
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
