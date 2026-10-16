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
    # Integer division by a numeral: the arithmetic solver adds the defining
    # clauses of (div x 3) and (mod x 3) itself (3 (div x 3) + (mod x 3) = x,
    # 0 <= (mod x 3) <= 2) under the hint arith, with the two terms opaque
    # atoms of the Farkas steps; Lean renders them as Int / and %.
    "lia_div": """\
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (= y (div x 3)))
(assert (>= x 7))
(assert (<= x 8))
(assert (not (= y 2)))
(check-sat)
""",
    # Remainders of a sum: a gcd conflict (cut) through mod atoms.
    "lia_mod_sum": """\
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (= (mod x 4) 3))
(assert (= (mod y 4) 2))
(assert (= (+ x y) (* 4 (div (+ x y) 4))))
(check-sat)
""",
    # Z3's rewriter knows 0 <= (mod x 5) < 5 and folds the assertion to
    # false, so the log assumes the empty clause and the exporter's cnf
    # bridge asks Lean (omega) for the whole fact.
    "lia_mod_folded": """\
(set-logic QF_LIA)
(declare-const x Int)
(assert (>= (mod x 5) 5))
(check-sat)
""",
    # A negative divisor: SMT-LIB and Lean both take the Euclidean
    # convention, 0 <= (mod x -3) <= 2 and x = -3 (div x -3) + (mod x -3).
    "lia_negative_divisor": """\
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (> (div x -3) 0))
(assert (< (mod x -3) 0))
(check-sat)
""",
    # abs is the ite SMT-LIB defines it as; Z3's rewriter logs the ite.
    "lia_abs": """\
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (>= (abs x) 3))
(assert (<= x 2))
(assert (>= x -2))
(check-sat)
""",
    # Division of a sum, with the remainder fixed, inside a bound conflict.
    "lia_div_sum": """\
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (= z (div (+ x y) 2)))
(assert (= (mod (+ x y) 2) 0))
(assert (>= x 3))
(assert (>= y 3))
(assert (<= (* 2 z) 5))
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


def random_division_instance(seed, variables=4, constraints=10, functions=False):
    """A random QF_LIA problem over div, mod, and abs atoms, or None when it is satisfiable.

    Divisors are the numerals -3, -2, 2, 3, and 4; with functions a unary
    Int function is applied to variables and remainders (QF_UFLIA).
    """
    generator = random.Random(seed)
    lines = ["(set-logic %s)" % ("QF_UFLIA" if functions else "QF_LIA")]
    lines += ["(declare-const x%d Int)" % i for i in range(variables)]
    if functions:
        lines.append("(declare-fun f (Int) Int)")

    def term(v):
        roll = generator.random()
        k = generator.choice([-3, -2, 2, 3, 4])
        if roll < 0.2:
            return "(div x%d %d)" % (v, k)
        if roll < 0.4:
            return "(mod x%d %d)" % (v, k)
        if roll < 0.5:
            other = generator.randrange(variables)
            return "(div (+ x%d x%d) %d)" % (v, other, k)
        if roll < 0.55:
            return "(abs x%d)" % v
        if functions and roll < 0.7:
            return "(f %s)" % ("x%d" % v if generator.random() < 0.5 else "(mod x%d %d)" % (v, abs(k)))
        return "x%d" % v

    def atom():
        chosen = generator.sample(range(variables), generator.randint(1, 3))
        terms = " ".join("(* %d %s)" % (generator.choice([-3, -2, -1, 1, 2, 3]), term(v)) for v in chosen)
        return "(%s (+ %s 0) %d)" % (generator.choice(["<=", ">=", "<", ">", "="]), terms,
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
# Seeds of random_division_instance whose refutations use cut and bound
# hints (seed 23 also an implied equality) next to the arith axioms and the
# Farkas steps; 250 to 400 proof steps each when they were pinned.
DIVISION_SEEDS = (19, 23, 27)


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

    def test_div_mod_and_abs_render_as_lean_integer_operators(self):
        source = LIA_INPUTS["lia_div"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        self.assertIn("arith", _hints(certificate))
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertIn("-- Int div and mod by a numeral are Lean's Euclidean / and %", text)
        self.assertRegex(text, r"def term_\d+ \(_atoms : Nat -> Prop\) \(_vars : Nat -> Int\) : Int := "
                               r"\(\(term_\d+ _atoms _vars\) / \(term_\d+ _atoms _vars\)\)")
        self.assertRegex(text, r": Int := \(\(term_\d+ _atoms _vars\) % \(term_\d+ _atoms _vars\)\)")
        self.assertNotIn("noncomputable", text)
        self.assertNotIn("Rat", text)
        # The three axioms are th-lemmas without coefficients, proved by the
        # integer tactic.
        arith_nodes = [node for node in _th_lemma_nodes(certificate) if _parameters(certificate, node) == ["arith"]]
        self.assertEqual(len(arith_nodes), 3)
        self.assertIn("first | omega | grind", text)
        # abs is Lean's ite with the classical instance, so its definitions
        # are noncomputable like an ite's; the negative divisor is a negated
        # numeral under / and %.
        abs_source = LIA_INPUTS["lia_abs"]
        abs_text = proof_to_lean.reconstruct(abs_source, proof_certificate.export_clause_log_certificate(abs_source))
        self.assertRegex(abs_text, r"noncomputable def term_\d+ \(_atoms : Nat -> Prop\) \(_vars : Nat -> Int\) : Int := "
                                   r"\(@ite Int \(\(term_(\d+) _atoms _vars\) >= \(\(0 : Int\)\)\) "
                                   r"\(Classical.propDecidable _\) \(term_\1 _atoms _vars\) \(-\(term_\1 _atoms _vars\)\)\)")
        negative_source = LIA_INPUTS["lia_negative_divisor"]
        negative_text = proof_to_lean.reconstruct(
            negative_source, proof_certificate.export_clause_log_certificate(negative_source))
        self.assertRegex(negative_text, r": Int := \(-\(term_\d+ _atoms _vars\)\)")
        self.assertRegex(negative_text, r": Int := \(\(term_\d+ _atoms _vars\) % \(term_\d+ _atoms _vars\)\)")

    def test_legacy_axioms_resolve_with_true_and_dead_branches_may_divide_by_zero(self):
        # The legacy core states the div and mod axioms as (or false l) and
        # resolves false away with the unit true (a true-axiom step).
        source = LIA_INPUTS["lia_div"]
        certificate = proof_certificate.export_certificate(source)
        declarations, nodes = certificate["declarations"], certificate["nodes"]
        self.assertIn("True.intro", proof_to_lean.reconstruct(source, certificate))
        true_axiom = next(index for index, raw in enumerate(nodes)
                          if declarations[raw["declaration"]]["kind"] == z3.Z3_OP_PR_TRUE)
        false_node = next(index for index, raw in enumerate(nodes)
                          if declarations[raw["declaration"]]["kind"] == z3.Z3_OP_FALSE)
        tampered = copy.deepcopy(certificate)
        tampered["nodes"][true_axiom]["arguments"] = [false_node]
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "true-axiom must conclude true"):
            proof_to_lean.reconstruct(source, tampered)
        # The unit true matches false literals only: resolving it against a
        # clause without one (a triangle-eq axiom) is rejected.
        resolution = next(index for index, raw in enumerate(nodes)
                          if declarations[raw["declaration"]]["kind"] == z3.Z3_OP_PR_UNIT_RESOLUTION
                          and true_axiom in raw["arguments"])
        triangle = next(n for n in _th_lemma_nodes(certificate) if _parameters(certificate, n) == ["triangle-eq"])
        tampered = copy.deepcopy(certificate)
        tampered["nodes"][resolution]["arguments"][0] = triangle
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "unit-resolution"):
            proof_to_lean.reconstruct(source, tampered)
        # Z3's rewriter cancels the common factor of (div (* 2 x3) (- 2))
        # through an ite whose dead branch is (div (* 2 x3) 0): such a term
        # may appear in a proof step, never in the assertions the theorem
        # states (test_integer_division_declarations_and_divisors_are_checked).
        source = random_division_instance(LEGACY_DIVISION_SEEDS[0])
        certificate = proof_certificate.export_certificate(source)
        declarations, nodes = certificate["declarations"], certificate["nodes"]
        zero = next(index for index, d in enumerate(declarations) if d["kind"] == z3.Z3_OP_ANUM and d["name"] == "0")
        by_zero = [index for index, raw in enumerate(nodes) if declarations[raw["declaration"]]["kind"] == z3.Z3_OP_IDIV
                   and nodes[raw["arguments"][1]]["declaration"] == zero]
        self.assertTrue(by_zero, "the dead branch dividing by zero is no longer in the proof")
        graph = proof_to_lean._validate_graph(source, certificate)
        stated = set()
        for assertion in certificate["assertions"]:
            stated |= proof_to_lean._reachable(graph, assertion)[0]
        self.assertFalse(stated & set(by_zero))
        self.assertIn("theorem unsat", proof_to_lean.reconstruct(source, certificate))

    def test_arith_th_lemmas_are_shape_checked_and_left_to_lean(self):
        source = LIA_INPUTS["lia_div"]
        exported = proof_certificate.export_clause_log_certificate(source)
        node = next(n for n in _th_lemma_nodes(exported) if _parameters(exported, n) == ["arith"])
        declaration = exported["nodes"][node]["declaration"]
        # An arith lemma takes no coefficients, concludes a clause, and each
        # of its literals, under any negations, is a linear arithmetic atom;
        # so is each premise (the legacy core's cuts list theirs).
        tampered = copy.deepcopy(exported)
        tampered["declarations"][declaration]["parameters"] = ["arith", "1"]
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "arith th-lemma takes no coefficients"):
            proof_to_lean.reconstruct(source, tampered)
        tampered = copy.deepcopy(exported)
        false_node = next(index for index, raw in enumerate(tampered["nodes"])
                          if tampered["declarations"][raw["declaration"]]["kind"] == z3.Z3_OP_FALSE)
        tampered["nodes"].append({"declaration": declaration, "arguments": [false_node]})
        tampered["rule_counts"]["th-lemma"] += 1
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "arith th-lemma must conclude a clause"):
            proof_to_lean.reconstruct(source, tampered)
        tampered = copy.deepcopy(exported)
        equivalence = next(index for index, raw in enumerate(tampered["nodes"])
                           if tampered["declarations"][raw["declaration"]]["kind"] == z3.Z3_OP_EQ
                           and tampered["declarations"][raw["declaration"]]["domain"] == ["Bool", "Bool"])
        tampered["nodes"].append({"declaration": declaration, "arguments": [equivalence]})
        tampered["rule_counts"]["th-lemma"] += 1
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "not a linear arithmetic atom"):
            proof_to_lean.reconstruct(source, tampered)
        tampered = copy.deepcopy(exported)
        clause_step = next(index for index, raw in enumerate(tampered["nodes"])
                           if tampered["declarations"][raw["declaration"]]["range"] == "Proof"
                           and tampered["declarations"][tampered["nodes"][raw["arguments"][-1]]["declaration"]]["kind"]
                           == z3.Z3_OP_OR)
        with_premise = len(tampered["declarations"])
        tampered["declarations"].append({"kind": z3.Z3_OP_PR_TH_LEMMA, "name": "th-lemma",
                                         "domain": ["Proof", "Bool"], "range": "Proof", "parameters": ["arith"]})
        tampered["nodes"].append({"declaration": with_premise,
                                  "arguments": [clause_step, tampered["nodes"][node]["arguments"][-1]]})
        tampered["rule_counts"]["th-lemma"] += 1
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "not a linear arithmetic atom"):
            proof_to_lean.reconstruct(source, tampered)  # a premise proving a clause is no held atom
        # Over Real atoms the shape check passes too (grind proves the
        # clause): a farkas lemma relabelled arith loses its coefficients but
        # stays a theory tautology.
        from test_proof_to_lean_arith import Z3TEST_LRA_INPUTS
        real_source = Z3TEST_LRA_INPUTS["lra_farkas"]
        real = proof_certificate.export_clause_log_certificate(real_source)
        real["declarations"][real["nodes"][_th_lemma_nodes(real)[0]]["declaration"]]["parameters"] = ["arith"]
        self.assertIn("grind", proof_to_lean.reconstruct(real_source, real))

    def test_integer_division_declarations_and_divisors_are_checked(self):
        source = LIA_INPUTS["lia_div"]
        exported = proof_certificate.export_clause_log_certificate(source)
        declarations = exported["declarations"]
        div = next(index for index, d in enumerate(declarations) if d["kind"] == z3.Z3_OP_IDIV)
        mod = next(index for index, d in enumerate(declarations) if d["kind"] == z3.Z3_OP_MOD)
        self.assertEqual((declarations[div]["name"], declarations[div]["domain"], declarations[div]["range"]),
                         ("div", ["Int", "Int"], "Int"))
        self.assertEqual(declarations[mod]["name"], "mod")
        div_node = next(index for index, raw in enumerate(exported["nodes"]) if raw["declaration"] == div)
        three = next(index for index, d in enumerate(declarations) if d["kind"] == z3.Z3_OP_ANUM and d["name"] == "3")
        self.assertEqual(exported["nodes"][exported["nodes"][div_node]["arguments"][1]]["declaration"], three)
        # Lean's / and % are total where SMT-LIB's div and mod by zero are
        # uninterpreted: a zero or nonconstant divisor is rejected on every
        # node the theorem states (the assertions and their subterms),
        # whether or not a theory lemma mentions it.
        for mutate, message in [
            (lambda c: c["declarations"][three].update(name="0"), "integer div by a nonconstant or zero"),
            (lambda c: c["nodes"][div_node]["arguments"].__setitem__(1, c["nodes"][div_node]["arguments"][0]),
             "integer div by a nonconstant or zero"),
            (lambda c: c["declarations"][div].update(kind=z3.Z3_OP_DIV, name="/"), "unsupported arithmetic declaration"),
            (lambda c: c["declarations"][div].update(kind=z3.Z3_OP_REM, name="rem"), "unsupported arithmetic declaration"),
            (lambda c: c["declarations"][mod].update(name="div"), "unsupported arithmetic declaration"),
            (lambda c: c["declarations"][div].update(domain=["Int"]), "invalid arithmetic declaration arity"),
            (lambda c: c["declarations"][div].update(domain=["Int", "Real"]), "arithmetic declarations take Int"),
        ]:
            tampered = copy.deepcopy(exported)
            mutate(tampered)
            with self.subTest(message=message):
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, message):
                    proof_to_lean.reconstruct(source, tampered)
        # The input is bound structurally: the same text with mod for div
        # does not match the certificate.
        swapped = source.replace("(div x 3)", "(mod x 3)")
        tampered = copy.deepcopy(exported)
        tampered["source_smt2"] = swapped
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "do not match the original input"):
            proof_to_lean.reconstruct(swapped, tampered)
        # A Real certificate never declares the integer operators.
        from test_proof_to_lean_arith import Z3TEST_LRA_INPUTS
        real_source = Z3TEST_LRA_INPUTS["lra_farkas"]
        real = proof_certificate.export_clause_log_certificate(real_source)
        addition = next(index for index, d in enumerate(real["declarations"]) if d["kind"] == z3.Z3_OP_ADD)
        real["declarations"][addition].update(kind=z3.Z3_OP_IDIV, name="div")
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "unsupported arithmetic declaration: div"):
            proof_to_lean.reconstruct(real_source, real)
        # The replay keys div and mod atoms by identity, so the arith axioms'
        # literals are linear constraints over them.
        context = z3.Context()
        x = z3.Int("x", context)
        relation, terms, constant = proof_clause_log._constraint(3 * (x / 3) + x % 3 == x)
        self.assertEqual((relation, constant, sorted(terms.values())), ("=", 0, [-1, 1, 3]))
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "nonzero constant"):
            proof_clause_log._constraint(x / 0 == x)
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "nonzero constant"):
            proof_clause_log._constraint(x % z3.Int("y", context) == x)

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

    def check(self, source, core="clause-log"):
        if core == "clause-log":
            certificate = proof_certificate.export_clause_log_certificate(source)
        else:
            certificate = proof_certificate.export_certificate(source)
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
            if core == "clause-log":
                self.assertIn(_STANDARD_AXIOMS, report)
            else:
                # A legacy refutation by rewriting and resolution alone may
                # need no axiom; otherwise the standard ones.
                self.assertTrue(_STANDARD_AXIOMS in report or "does not depend on any axioms" in report, report)
            return certificate

    def test_documented_lia_inputs_verify_under_the_standard_axioms(self):
        hints = set()
        for name, source in LIA_INPUTS.items():
            with self.subTest(name=name):
                certificate = self.check(source)
                if name == "lia_mod_folded":
                    # The rewriter folded the assertion to false: no theory
                    # lemma, one rewrite of the assertion (proved by omega).
                    self.assertNotIn("th-lemma", certificate["rule_counts"])
                    self.assertEqual(certificate["rule_counts"]["rewrite"], 1)
                else:
                    self.assertIn("th-lemma", certificate["rule_counts"])
                if name in ("lia_div", "lia_mod_sum", "lia_negative_divisor", "lia_div_sum"):
                    self.assertIn("arith", _hints(certificate))
                if name == "lia_mod_sum":
                    self.assertIn("cut", _hints(certificate))
                hints |= _hints(certificate)
        self.assertLessEqual({"cut", "farkas", "bound", "implied-eq", "euf", "arith"}, hints)

    def test_pinned_random_instances_verify(self):
        for seed in PINNED_SEEDS:
            source = random_instance(seed)
            self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % seed)
            with self.subTest(seed=seed):
                self.check(source)

    def test_pinned_division_instances_verify(self):
        hints = set()
        for seed in DIVISION_SEEDS:
            source = random_division_instance(seed)
            self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % seed)
            with self.subTest(seed=seed):
                hints |= _hints(self.check(source))
        self.assertLessEqual({"arith", "farkas", "bound", "cut", "euf"}, hints)

    def test_arith_lemmas_over_real_atoms_verify(self):
        # The arith hint is accepted in Real certificates too, where grind
        # proves the clause; live Real division axioms have separate tests.
        from test_proof_to_lean_arith import Z3TEST_LRA_INPUTS
        source = Z3TEST_LRA_INPUTS["lra_farkas"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        certificate["declarations"][certificate["nodes"][_th_lemma_nodes(certificate)[0]]["declaration"]]["parameters"] = ["arith"]
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "checked.lean"
            proof_to_lean.check_and_write(source, certificate, output)
            self.assertIn("private theorem th_lemma_", output.read_text())

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
        # An arith lemma must have literals, so a false one is a unit clause:
        # the negation of the axiom (mod x 3) <= 2 (logged as 2 >= mod x 3),
        # which passes the shape check and fails in Lean.
        source = LIA_INPUTS["lia_div"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        declarations = certificate["declarations"]
        bound = next(index for index, raw in enumerate(certificate["nodes"])
                     if declarations[raw["declaration"]]["kind"] in (z3.Z3_OP_LE, z3.Z3_OP_GE)
                     and {declarations[certificate["nodes"][arg]["declaration"]]["name"] for arg in raw["arguments"]}
                     == {"mod", "2"})
        negation = next(index for index, d in enumerate(declarations) if d["kind"] == z3.Z3_OP_NOT)
        arith = next(index for index, d in enumerate(declarations) if d["parameters"] == ["arith"])
        certificate["nodes"].append({"declaration": negation, "arguments": [bound]})
        certificate["nodes"].append({"declaration": arith, "arguments": [len(certificate["nodes"]) - 1]})
        certificate["rule_counts"]["th-lemma"] += 1
        self.assertIn("th_lemma_%d" % (len(certificate["nodes"]) - 1), proof_to_lean.reconstruct(source, certificate))
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "checked.lean"
            with self.assertRaises(subprocess.CalledProcessError):
                proof_to_lean.check_and_write(source, certificate, output)
            self.assertFalse(output.exists())


# Seeds of random_division_instance whose legacy proofs exercise what the
# clause log never shows: seed 77 rewrites (div (+ x3 x3) -2) through an ite
# whose dead branch is (div (* 2 x3) 0), the rewriter's factor cancellation,
# and seed 85 has bound propagations and 255 steps.
LEGACY_DIVISION_SEEDS = (77, 85)


class TestLegacyIntegerLeanIntegration(unittest.TestCase):
    """End-to-end through the smt core's proof object: certificate, Lean reconstruction, kernel check."""

    check = TestIntegerLeanIntegration.check

    def test_documented_lia_inputs_verify_through_the_legacy_core(self):
        hints = set()
        for name, source in LIA_INPUTS.items():
            with self.subTest(name=name):
                certificate = self.check(source, core="legacy")
                hints |= _hints(certificate)
                parameters = [_parameters(certificate, node) for node in _th_lemma_nodes(certificate)]
                if name == "lia_gomory":
                    # The lattice conflict: theory_lra labels it farkas with
                    # coefficients that do not refute the premises rationally,
                    # so the exporter keeps none and Lean proves it alone.
                    self.assertEqual(parameters, [["farkas"]] * len(parameters))
                    self.assertTrue(parameters)
                if name == "lia_equality_elimination":
                    # A cut: a bare arith step deriving its bound from the premises it lists.
                    self.assertTrue(any(p == ["arith"] and len(certificate["nodes"][node]["arguments"]) > 1
                                        for node, p in zip(_th_lemma_nodes(certificate), parameters)), parameters)
                if name in ("lia_div", "lia_mod_sum", "lia_div_sum"):
                    # The div and mod axioms, stated (or false l) and resolved with the unit true.
                    self.assertIn("arith", _hints(certificate))
                    self.assertEqual(certificate["rule_counts"]["true-axiom"], 1)
        # The legacy core's hints: no cut or euf (its congruences are
        # monotonicity steps), plus the bare arith of its axioms and cuts.
        self.assertEqual(hints, {"farkas", "bound", "triangle-eq", "arith"})

    def test_pinned_division_instances_verify_through_the_legacy_core(self):
        for seed in LEGACY_DIVISION_SEEDS:
            source = random_division_instance(seed)
            self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % seed)
            with self.subTest(seed=seed):
                certificate = self.check(source, core="legacy")
                self.assertIn("th-lemma", certificate["rule_counts"])
                declarations, nodes = certificate["declarations"], certificate["nodes"]
                # Both seeds pin the congruence through div (a monotonicity
                # step equating two div terms, a grind lemma in Lean).
                congruences = [declarations[nodes[nodes[raw["arguments"][-1]]["arguments"][0]]["declaration"]]["kind"]
                               for raw in nodes if declarations[raw["declaration"]]["kind"] == z3.Z3_OP_PR_MONOTONICITY
                               and declarations[nodes[raw["arguments"][-1]]["declaration"]]["kind"] == z3.Z3_OP_EQ]
                self.assertIn(z3.Z3_OP_IDIV, congruences, "no monotonicity step over div is left in the proof")
                if seed == 77:
                    zero = next(index for index, d in enumerate(declarations)
                                if d["kind"] == z3.Z3_OP_ANUM and d["name"] == "0")
                    self.assertTrue(any(declarations[raw["declaration"]]["kind"] == z3.Z3_OP_IDIV
                                        and nodes[raw["arguments"][1]]["declaration"] == zero for raw in nodes),
                                    "the dead branch dividing by zero is no longer in the proof")

    def test_false_legacy_lemmas_without_coefficients_are_rejected_by_lean(self):
        # The coefficient-free farkas of the lattice conflict, cut down to two
        # of its four premises (x + y <= 1 and x + y >= 1 are satisfiable):
        # the shape check passes, Lean fails, no proof is published.
        source = LIA_INPUTS["lia_gomory"]
        certificate = proof_certificate.export_certificate(source)
        node = next(n for n in _th_lemma_nodes(certificate) if _parameters(certificate, n) == ["farkas"])
        arguments = certificate["nodes"][node]["arguments"]
        self.assertEqual(len(arguments), 5)
        certificate["declarations"].append({"kind": z3.Z3_OP_PR_TH_LEMMA, "name": "th-lemma",
                                            "domain": ["Proof", "Proof", "Bool"], "range": "Proof",
                                            "parameters": ["farkas"]})
        certificate["nodes"][node] = {"declaration": len(certificate["declarations"]) - 1,
                                      "arguments": arguments[:2] + arguments[-1:]}
        graph = proof_to_lean._validate_graph(source, certificate)
        proof_to_lean._check_th_lemma(graph, node)
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "checked.lean"
            with self.assertRaises(subprocess.CalledProcessError):
                proof_to_lean.check_and_write(source, certificate, output)
            self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
