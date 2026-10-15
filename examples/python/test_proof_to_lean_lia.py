############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Tests for the QF_LIA slice of the Lean reconstruction (linear integer
# arithmetic through the clause log): validation without Lean, and
# end-to-end checks that need the z3 executable and the pinned Lean toolchain.
############################################
import copy
import hashlib
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

# Documented QF_LIA inputs. Each exercises one integer-specific step of the
# sat.smt core's arithmetic solver, as named in the comments: the clause log
# labels gcd conflicts and Gomory cuts "cut" (no coefficients certify the
# rounding; Lean's grind proves the clause), tightens strict bounds to the
# integer lattice, and otherwise emits the same farkas, bound, implied-eq,
# and euf hints as for Real input.
LIA_INPUTS = {
    # A gcd conflict: 2x = 2y + 1 has no integer solution (one cut hint).
    "lia_gcd": """\
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (= (* 2 x) (+ (* 2 y) 1)))
(check-sat)
""",
    # Z3's rewriter rounds the bounds (1 <= 3x is x >= 1), so the assumptions
    # are bridged by rewrites that grind proves over Int.
    "lia_rounding": """\
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (<= 1 (* 3 x)))
(assert (<= (* 3 x) 2))
(check-sat)
""",
    # Strict bounds tightened to x <= 2 and x >= 2, an implied equality, and a
    # disequality.
    "lia_strict": """\
(set-logic QF_LIA)
(declare-const x Int)
(assert (< x 3))
(assert (> x 1))
(assert (not (= x 2)))
(check-sat)
""",
    # Rationally feasible (x = 2/3, y = 1); refuted by bound propagation and
    # Farkas steps over the rounded bounds.
    "lia_branching": """\
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (= (+ (* 3 x) (* 5 y)) 7))
(assert (<= 0 x))
(assert (<= x 1))
(assert (<= 0 y))
(assert (<= y 1))
(check-sat)
""",
    # A Gomory cut over four bounds, logged as one cut hint with four literals.
    "lia_gomory": """\
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (<= (+ (* 2 x) (* 2 y)) 3))
(assert (>= (+ (* 2 x) (* 2 y)) 1))
(assert (>= (- (* 4 x) (* 2 y)) 1))
(assert (<= (- (* 4 x) (* 2 y)) 3))
(check-sat)
""",
    "lia_boolean_structure": """\
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(declare-const p Bool)
(assert (or p (<= x (- 6))))
(assert (=> p (>= (+ x y) 2)))
(assert (and (< y 1) (> x 0)))
(assert (not (= x 7)))
(assert (<= x 1))
(check-sat)
""",
    # An Int-valued ite: an opaque atom of the linear forms, tied to its
    # branches by gate clauses, rendered as Lean's ite over Int.
    "lia_ite": """\
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(declare-const p Bool)
(assert (> (ite p x y) 3))
(assert (< x 2))
(assert (< y 3))
(check-sat)
""",
    # Three distinct integers in {0, 1}: alldiff clauses, implied equalities,
    # and bound propagations over the unit interval.
    "lia_distinct": """\
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (distinct x y z))
(assert (<= 0 x))
(assert (<= x 1))
(assert (<= 0 y))
(assert (<= y 1))
(assert (<= 0 z))
(assert (<= z 1))
(check-sat)
""",
    # Equalities substituted into a parity conflict: 2z = 2y + 1.
    "lia_equality_elimination": """\
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (= x (+ y 1)))
(assert (= (* 2 z) (+ x y)))
(assert (>= z 0))
(assert (<= z 0))
(check-sat)
""",
}

_STANDARD_AXIOMS = "[propext, Classical.choice, Quot.sound]"


def random_instance(seed, variables=4, constraints=10, ite=False):
    """A random QF_LIA problem over small integer coefficients, or None when it is satisfiable."""
    generator = random.Random(seed)
    lines = ["(set-logic QF_LIA)"] + ["(declare-const x%d Int)" % i for i in range(variables)]

    def term(v):
        if ite and generator.random() < 0.3:
            other = generator.randrange(variables)
            return "(ite (%s x%d %d) x%d (* %d x%d))" % (
                generator.choice(["<=", ">"]), other, generator.randint(-2, 2), v,
                generator.choice([-2, -1, 2]), other)
        return "x%d" % v

    def atom():
        chosen = generator.sample(range(variables), generator.randint(2, 3))
        terms = " ".join("(* %d %s)" % (generator.choice([-3, -2, -1, 1, 2, 3]), term(v)) for v in chosen)
        return "(%s (+ %s) %d)" % (generator.choice(["<=", ">=", "<", ">", "="]), terms,
                                   generator.randint(-5, 5))

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
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.from_string(source)
    return source if solver.check() == z3.unsat else None


def wide_rewrite_instance(variables=9):
    """Every variable in [5, 7] and one clause asking for one of them outside.

    The clause is a single rewrite over 2 * variables linear atoms, more than
    proof_to_lean._NORMALIZED_REWRITE_ATOMS for nine variables, so it takes the
    normalized-rewrite path, where every strict atom must be keyed as the
    complement of the bound it contradicts.
    """
    names = ["x%d" % i for i in range(variables)]
    lines = ["(set-logic QF_LIA)"] + ["(declare-const %s Int)" % name for name in names]
    lines.append("(assert (or %s %s))" % (" ".join("(< %s 5)" % name for name in names),
                                          " ".join("(> %s 7)" % name for name in names)))
    for name in names:
        lines.extend(["(assert (>= %s 5))" % name, "(assert (<= %s 7))" % name])
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


# Random seeds whose refutations use cut hints and bound propagations next
# to the Farkas steps (seed 97 also an implied equality), with 17 to 25
# theory lemmas each when they were pinned.
PINNED_SEEDS = (9, 78, 97)


def _z3_available():
    try:
        return subprocess.run([proof_certificate.default_z3_executable(), "--version"],
                              capture_output=True).returncode == 0
    except OSError:
        return False


def _th_lemma_nodes(certificate):
    return [index for index, node in enumerate(certificate["nodes"])
            if certificate["declarations"][node["declaration"]]["name"] == "th-lemma"]


def _hints(certificate):
    return {d["parameters"][0] for d in certificate["declarations"] if d["name"] == "th-lemma"}


def _parameters(certificate, node):
    return certificate["declarations"][certificate["nodes"][node]["declaration"]]["parameters"]


class TestIntegerValidation(unittest.TestCase):
    """Certificate validation and Lean text generation, without running Lean."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")
        cls.gomory = proof_certificate.export_clause_log_certificate(LIA_INPUTS["lia_gomory"])
        cls.branching = proof_certificate.export_clause_log_certificate(LIA_INPUTS["lia_branching"])

    def test_generated_lean_values_the_variables_in_int(self):
        text = proof_to_lean.reconstruct(LIA_INPUTS["lia_gomory"], self.gomory)
        self.assertIn("theorem unsat (_atoms : Nat -> Prop) (_vars : Nat -> Int)", text)
        self.assertIn("-- Int variables are encoded as Int", text)
        self.assertIn("-- Variable 0: \"x\"", text)
        self.assertIn("((2 : Int))", text)
        self.assertIn(": Int := (-(term_", text)  # (- 2) is unary minus applied to the numeral
        self.assertIn(": Int := ", text)
        self.assertNotIn("Rat", text)
        self.assertIn("private theorem th_lemma_", text)
        self.assertNotIn("sorry", text)
        ite_source = LIA_INPUTS["lia_ite"]
        ite_text = proof_to_lean.reconstruct(ite_source, proof_certificate.export_clause_log_certificate(ite_source))
        self.assertIn("noncomputable def term_", ite_text)
        self.assertIn("(@ite Int (formula_", ite_text)
        self.assertIn("ite_eq_left", ite_text)

    def test_cut_hints_are_shape_checked_and_left_to_lean(self):
        self.assertEqual(self.gomory["fragment"], "qf_lia")
        self.assertEqual(_hints(self.gomory), {"cut"})
        node = _th_lemma_nodes(self.gomory)[0]
        self.assertEqual(_parameters(self.gomory, node), ["cut"])  # no coefficients certify a cut
        clause = self.gomory["nodes"][self.gomory["nodes"][node]["arguments"][-1]]
        self.assertEqual(len(clause["arguments"]), 4)
        # The same clause with unit Farkas coefficients is not a rational
        # contradiction: the exact re-derivation rejects it before Lean, while
        # an Int farkas without coefficients is Lean's alone, like the cut.
        tampered = copy.deepcopy(self.gomory)
        tampered["declarations"][tampered["nodes"][node]["declaration"]]["parameters"] = ["farkas", "1", "1", "1", "1"]
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "do not refute"):
            proof_to_lean.reconstruct(LIA_INPUTS["lia_gomory"], tampered)
        tampered["declarations"][tampered["nodes"][node]["declaration"]]["parameters"] = ["farkas"]
        self.assertIn("first | omega | grind", proof_to_lean.reconstruct(LIA_INPUTS["lia_gomory"], tampered))
        # A cut, and a coefficient-free farkas, need an Int certificate: the
        # Real slice rejects both.
        from test_proof_to_lean_arith import Z3TEST_LRA_INPUTS
        real_source = Z3TEST_LRA_INPUTS["lra_farkas"]
        real = proof_certificate.export_clause_log_certificate(real_source)
        real_node = _th_lemma_nodes(real)[0]
        for parameters, message in [(["cut"], "requires an Int certificate"),
                                    (["cut", "1", "2", "1"], "requires an Int certificate"),
                                    (["farkas"], "has 0 coefficients for 0 premises and 3 clause literals")]:
            real["declarations"][real["nodes"][real_node]["declaration"]]["parameters"] = parameters
            with self.subTest(parameters=parameters):
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, message):
                    proof_to_lean.reconstruct(real_source, real)
        # Coefficients next to a cut are rejected too.
        tampered = copy.deepcopy(self.gomory)
        tampered["declarations"][tampered["nodes"][node]["declaration"]]["parameters"] = ["cut", "1", "1", "1", "1"]
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "no coefficients"):
            proof_to_lean.reconstruct(LIA_INPUTS["lia_gomory"], tampered)
        # A cut literal must be a linear integer atom: an earlier Boolean
        # equivalence (a rewrite's conclusion) in its place is rejected.
        tampered = copy.deepcopy(self.gomory)
        clause_node = tampered["nodes"][node]["arguments"][-1]
        equivalence = next(index for index, raw in enumerate(tampered["nodes"][:clause_node])
                           if tampered["declarations"][raw["declaration"]]["kind"] == z3.Z3_OP_EQ
                           and tampered["declarations"][raw["declaration"]]["domain"] == ["Bool", "Bool"])
        tampered["nodes"][clause_node]["arguments"][0] = equivalence
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "not a linear arithmetic atom"):
            proof_to_lean.reconstruct(LIA_INPUTS["lia_gomory"], tampered)

    def test_tampered_farkas_coefficients_are_rejected_before_lean(self):
        self.assertIn("farkas", _hints(self.branching))
        node = next(n for n in _th_lemma_nodes(self.branching) if _parameters(self.branching, n)[0] == "farkas")
        parameters = _parameters(self.branching, node)
        self.assertEqual(parameters[1:], ["1", "5", "3"])
        # The first literal is the equality 3x + 5y = 7, whose multiplier is
        # solved for (its coefficient is a placeholder); the inequality
        # weights must be right.
        for position in (2, 3):
            tampered = copy.deepcopy(self.branching)
            tampered["declarations"][tampered["nodes"][node]["declaration"]]["parameters"][position] = "7"
            with self.subTest(position=position):
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "do not refute"):
                    proof_to_lean.reconstruct(LIA_INPUTS["lia_branching"], tampered)

    def test_fragment_and_sort_consistency(self):
        source = LIA_INPUTS["lia_gomory"]
        for fragment in ("qf_lra", "qf_uflra"):
            relabelled = copy.deepcopy(self.gomory)
            relabelled["fragment"] = fragment
            with self.subTest(fragment=fragment):
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "Int arithmetic|uninterpreted"):
                    proof_to_lean.reconstruct(source, relabelled)
        relabelled = copy.deepcopy(self.gomory)
        relabelled["fragment"] = "propositional"
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "cannot contain arithmetic"):
            proof_to_lean.reconstruct(source, relabelled)
        # A Real declaration next to the Int ones, a fractional Int numeral, a
        # mixed predicate, Int division, and an Int-valued function.
        numeral = next(index for index, d in enumerate(self.gomory["declarations"]) if d["kind"] == z3.Z3_OP_ANUM)
        predicate = next(index for index, d in enumerate(self.gomory["declarations"]) if d["kind"] == z3.Z3_OP_LE)
        variable = next(index for index, d in enumerate(self.gomory["declarations"])
                        if d["kind"] == z3.Z3_OP_UNINTERPRETED and d["range"] == "Int")
        addition = next(index for index, d in enumerate(self.gomory["declarations"]) if d["kind"] == z3.Z3_OP_ADD)
        for mutate, message in [
            (lambda d: d.append({"kind": z3.Z3_OP_UNINTERPRETED, "name": "r", "domain": [], "range": "Real",
                                 "parameters": []}), "cannot mix Int and Real arithmetic"),
            (lambda d: d[numeral].update(name="1/2"), "invalid Int numeral declaration"),
            (lambda d: d[predicate].update(domain=["Int", "Real"]), "invalid arithmetic predicate declaration"),
            (lambda d: d[addition].update(kind=z3.Z3_OP_DIV, name="/"), "unsupported arithmetic declaration"),
            # An Int-valued function is a valid declaration since qf_uflia; the
            # variable's nodes no longer fit it.
            (lambda d: d[variable].update(domain=["Int"]), "wrong number of arguments"),
            (lambda d: d[variable].update(domain=["Proof"]), "unsupported arithmetic function declaration"),
        ]:
            tampered = copy.deepcopy(self.gomory)
            mutate(tampered["declarations"])
            with self.subTest(message=message):
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, message):
                    proof_to_lean.reconstruct(source, tampered)
        # The Real twin of the input (same text with Real sorts and numerals)
        # does not bind to the Int certificate.
        twin = source.replace(" Int)", " Real)")
        for digit in "1234":
            twin = twin.replace(" %s " % digit, " %s.0 " % digit).replace(" %s)" % digit, " %s.0)" % digit)
        twin_certificate = copy.deepcopy(self.gomory)
        twin_certificate["source_smt2"] = twin
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "in fragment qf_lra, not qf_lia"):
            proof_to_lean.reconstruct(twin, twin_certificate)

    def test_integer_atoms_are_tightened_in_the_replay_and_the_reconstructor(self):
        context = z3.Context()
        x = z3.Int("x", context)
        relation, terms, constant = proof_clause_log._constraint(x < 3)
        self.assertEqual((relation, constant), ("<=", -2))
        relation, terms, constant = proof_clause_log._constraint(z3.Not(z3.IntVal(5, context) <= x))
        self.assertEqual((relation, constant), ("<=", -4))
        # The canonical keys identify the three spellings of x <= 4.
        normalizer = proof_clause_log._Normalizer()
        keys = {normalizer.key(formula) for formula in (x < 5, x <= 4, z3.Not(z3.IntVal(5, context) <= x))}
        self.assertEqual(len(keys), 1)
        # Real atoms keep their strictness.
        r = z3.Real("r", context)
        self.assertEqual(proof_clause_log._constraint(r < 3)[0], "<")
        # The reconstructor tightens the same way: a strict Int literal of a
        # certificate becomes a non-strict constraint.
        strict = proof_certificate.export_clause_log_certificate(LIA_INPUTS["lia_strict"])
        graph = proof_to_lean._validate_graph(LIA_INPUTS["lia_strict"], strict)
        self.assertEqual(graph.numeric, "Int")
        self.assertEqual(graph.fragment, "qf_lia")
        atoms = [node for node in range(len(graph.nodes)) if graph.kind(node) == z3.Z3_OP_LE]
        self.assertTrue(atoms)
        for atom in atoms:
            relation, _, constant = proof_to_lean._polarity_constraint(graph, atom, False)
            self.assertEqual(relation, "<=")
            self.assertEqual(constant.denominator, 1)

    def test_wide_rewrite_keys_strict_integer_atoms_as_complements(self):
        # A rewrite over more than _NORMALIZED_REWRITE_ATOMS atoms names each
        # linear atom once and treats the names as opaque: a tightened strict
        # atom (x < 5 is x - 4 <= 0) must get the name of the bound it
        # contradicts (x >= 5 is Not (x - 4 <= 0)), as over Real, or the
        # propositional lemma cannot see that they are complementary.
        source = wide_rewrite_instance()
        text = proof_to_lean.reconstruct(source, proof_certificate.export_clause_log_certificate(source))
        self.assertIn("private theorem normalized_rewrite_", text)
        self.assertEqual(text.count("  let _atom"), 18)
        self.assertEqual(text.count("<-> (Not _atom"), 18)
        self.assertIn("(Not _atom0)", text)
        # The empty cut hint names its own defect, not the sort.
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "cut hint without literals"):
            proof_clause_log.check_linear_hint("cut", [])


class TestIntegerLeanIntegration(unittest.TestCase):
    """End-to-end: z3 clause log, certificate, Lean reconstruction, kernel check."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")

    def check(self, source):
        certificate = proof_certificate.export_clause_log_certificate(source)
        self.assertEqual(certificate["fragment"], "qf_lia")
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "checked.lean"
            proof_to_lean.check_and_write(source, certificate, output)
            text = output.read_text()
            namespace = "Z3Proofs.NativeCertificate.p" + hashlib.sha256(source.encode()).hexdigest()
            statement = text.split("theorem unsat", 1)[1].split(": False :=", 1)[0]
            self.assertEqual(statement.count("    (_h"), len(certificate["assertions"]))
            self.assertIn("(_vars : Nat -> Int)", statement)
            self.assertNotIn("Rat", text)
            output.write_text(text + "\n#print axioms %s.unsat\n" % namespace)
            result = subprocess.run([str(proof_to_lean._CHECK_LEAN), str(output)],
                                    text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            report = " ".join(result.stdout.split())
            self.assertIn(_STANDARD_AXIOMS, report)
            return certificate

    def test_documented_lia_inputs_verify_under_the_standard_axioms(self):
        hints = set()
        for name, source in LIA_INPUTS.items():
            with self.subTest(name=name):
                certificate = self.check(source)
                self.assertIn("th-lemma", certificate["rule_counts"])
                hints |= _hints(certificate)
        self.assertLessEqual({"cut", "farkas", "bound", "implied-eq", "euf"}, hints)

    def test_pinned_random_instances_verify(self):
        for seed in PINNED_SEEDS:
            source = random_instance(seed)
            self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % seed)
            with self.subTest(seed=seed):
                self.check(source)

    def test_random_instances_with_ite_terms_verify(self):
        checked = 0
        for seed in range(40):
            source = random_instance(seed, constraints=12, ite=True)
            if source is None:
                continue
            with self.subTest(seed=seed):
                self.check(source)
            checked += 1
            if checked == 3:
                break
        self.assertEqual(checked, 3)

    def test_wide_rewrite_verifies_through_the_normalized_path(self):
        source = wide_rewrite_instance()
        certificate = self.check(source)
        self.assertIn("private theorem normalized_rewrite_", proof_to_lean.reconstruct(source, certificate))

    def test_outlined_integer_proofs_preserve_the_statement(self):
        with patch.object(proof_to_lean, "_OUTLINE_PROOF_STEPS", 0):
            for name in ("lia_gomory", "lia_distinct"):
                with self.subTest(input=name):
                    self.check(LIA_INPUTS[name])

    def test_false_integer_lemmas_without_coefficients_never_publish_a_proof(self):
        # A cut, and an Int farkas or bound without coefficients, certify
        # nothing in Python, so one claiming the empty clause passes every
        # shape check; only Lean can reject it.
        source = LIA_INPUTS["lia_gomory"]
        exported = proof_certificate.export_clause_log_certificate(source)
        false_node = next(index for index, raw in enumerate(exported["nodes"])
                          if exported["declarations"][raw["declaration"]]["kind"] == z3.Z3_OP_FALSE)
        for hint in ("cut", "farkas", "bound"):
            certificate = copy.deepcopy(exported)
            certificate["declarations"].append({"kind": z3.Z3_OP_PR_TH_LEMMA, "name": "th-lemma",
                                                "domain": ["Bool"], "range": "Proof", "parameters": [hint]})
            certificate["nodes"].append({"declaration": len(certificate["declarations"]) - 1,
                                         "arguments": [false_node]})
            certificate["proof"] = len(certificate["nodes"]) - 1
            certificate["rule_counts"]["th-lemma"] += 1
            with self.subTest(hint=hint), tempfile.TemporaryDirectory() as directory:
                output = Path(directory) / "checked.lean"
                with self.assertRaises(subprocess.CalledProcessError):
                    proof_to_lean.check_and_write(source, certificate, output)
                self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
