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
import proof_to_lean
from test_proof_certificate import _proof_nodes

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
    # A lattice conflict over equalities: eliminating x leaves
    # 2 (z - w + 3 y) = -17. The clause log labels it cut; the legacy core's
    # own Farkas check fails on it, so it labels the conflict
    # (_ th-lemma arith unsupported), kept as a coefficient-free farkas.
    "lia_lattice_conflict": """\
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const w Int)
(assert (= (+ y z) 3))
(assert (= (+ (* 3 x) (* 2 z)) (- (* 2 w) 5)))
(assert (= (* 2 y) (- x 4)))
(check-sat)
""",
    # The same label on a conflict over bounds, next to a cut (a bare arith
    # step with premises) through the legacy core.
    "lia_lattice_bounds": """\
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const w Int)
(assert (= (+ y (* 3 z)) -5))
(assert (> (- z y (* 2 w)) -5))
(assert (>= (+ (* 2 y) w) 2))
(assert (>= (+ (* 2 z) (* 3 w) y) -2))
(check-sat)
""",
}

# The documented inputs whose legacy proofs carry (_ th-lemma arith
# unsupported), theory_lra's label for a conflict it could not certify.
LEGACY_UNSUPPORTED_INPUTS = ("lia_lattice_conflict", "lia_lattice_bounds")

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


def wide_rewrite_instance(variables=9, term="{0}", logic="QF_LIA", declarations=()):
    """Every variable in [5, 7] and one clause asking for one of them outside.

    The clause is a single rewrite over 2 * variables linear atoms, more than
    proof_to_lean._NORMALIZED_REWRITE_ATOMS for nine variables, so it takes the
    normalized-rewrite path, where every strict atom must be keyed as the
    complement of the bound it contradicts. With term the bounds are on an
    opaque term of each variable, (mod {0} 10) or (f {0}) say, instead of
    the variable itself.
    """
    names = ["x%d" % i for i in range(variables)]
    terms = [term.format(name) for name in names]
    lines = ["(set-logic %s)" % logic] + list(declarations) + ["(declare-const %s Int)" % name for name in names]
    lines.append("(assert (or %s %s))" % (" ".join("(< %s 5)" % name for name in terms),
                                          " ".join("(> %s 7)" % name for name in terms)))
    for name in terms:
        lines.extend(["(assert (>= %s 5))" % name, "(assert (<= %s 7))" % name])
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


def wide_abs_instance(variables=12, ite=False, strict=False, scale=1):
    """Every |x_i| at least one and their sum at most variables - 1.

    Z3's rewriter logs (abs x) as (ite (<= 0 x) x (* -1 x)), so the rewrite
    of the sum relates 2 * variables ite terms (the abs renderings against
    the rewriter's form); splitting them is exponential, bridging each pair
    is not. With ite the input writes the SMT-LIB definition of abs itself,
    (ite (>= x 0) x (- x)), which the rewriter normalizes the same way, with
    strict as (ite (> x 0) x (- x)), whose condition the rewriter negates
    (swapping the branches) and the reconstructor tightens; with scale the
    magnitude is of (* scale x), whose condition the rewriter divides by
    the coefficient.
    """
    names = ["x%d" % i for i in range(variables)]
    argument = "{0}" if scale == 1 else "(* %d {0})" % scale
    if ite:
        magnitude = "(ite (%s %s 0) %s (- %s))" % (">" if strict else ">=", argument, argument, argument)
    else:
        magnitude = "(abs %s)" % argument
    lines = ["(set-logic QF_LIA)"] + ["(declare-const %s Int)" % name for name in names]
    lines += ["(assert (>= %s 1))" % magnitude.format(name) for name in names]
    lines.append("(assert (<= (+ %s) %d))" % (" ".join(magnitude.format(name) for name in names), variables - 1))
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
# Seed of random_division_instance(variables=6, constraints=18) from the
# iter-027 stress run: 547 theory lemmas over div, mod, and abs atoms by
# negative numerals, among them a Farkas step and four cuts over a dozen
# such atoms that exhausted maxHeartbeats when unfolded (omega leaves
# t % -3 as an atom and grind splits every abs); proved over the atoms
# generalized to integers since 2026-10-21.
WIDE_DIVISION_SEED = 67


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

    def test_integer_theory_lemmas_generalize_their_opaque_atoms(self):
        # A farkas or bound with coefficients over div, mod, abs, ite, or
        # application atoms is a combination over the atoms, so Lean proves
        # it with the atoms generalized to integers (omega on the linear
        # goal, no Euclidean unfolding, no ite splits, and no mod bounds:
        # the re-derived combination holds without them, and they made
        # omega take minutes on a wide lemma); a cut the same way with
        # grind, after the mod bounds Z3 omits from its lemmas are stated
        # and reverted; the unfolded proof stays as the fallback. Lemmas
        # without such atoms, and the arith axioms, are unchanged.
        def lemma(text, node):
            return text.split("private theorem th_lemma_%d " % node, 1)[1].split("\n\n", 1)[0]

        generalized = {}
        for name, source in [(name, LIA_INPUTS[name]) for name in ("lia_div", "lia_mod_sum", "lia_abs", "lia_gcd")] + [
                ("wide", random_division_instance(WIDE_DIVISION_SEED, variables=6, constraints=18))]:
            certificate = proof_certificate.export_clause_log_certificate(source)
            graph = proof_to_lean._validate_graph(source, certificate)
            text = proof_to_lean.reconstruct(source, certificate)
            generalized[name] = set()
            for node in _th_lemma_nodes(certificate):
                parameters = _parameters(certificate, node)
                block = lemma(text, node)
                atoms = proof_to_lean._opaque_int_atoms(graph, [graph.conclusion(node)])
                tactic = proof_to_lean._opaque_tactic(graph, node)
                with self.subTest(name=name, node=node, hint=parameters):
                    if parameters[0] in ("farkas", "bound", "cut"):
                        self.assertEqual(tactic, "omega" if len(parameters) > 1 else "grind (splits := 64)")
                    else:
                        self.assertIsNone(tactic)
                    if not (tactic and atoms):
                        self.assertNotIn("generalize", block)
                        self.assertNotIn("first\n", block)
                        self.assertTrue(block.endswith("first | omega | grind (splits := 64)"), block[-200:])
                        continue
                    generalized[name].add(parameters[0])
                    self.assertIn("  first\n    | (", block)
                    for position, atom in enumerate(atoms):
                        self.assertIn("generalize (term_%d _atoms _vars) = _o%d\n" % (atom, position), block)
                        self.assertTrue(graph.is_arith(atom) and graph.arguments(atom))
                    self.assertIn("\n       %s)\n    | (unfold " % tactic, block)
                    self.assertTrue(block.endswith("first | omega | grind (splits := 64))"), block[-200:])
                    mods = [atom for atom in atoms if graph.kind(atom) == z3.Z3_OP_MOD]
                    if tactic == "omega":
                        mods = []  # The coefficients certify the combination over the atoms alone.
                    self.assertEqual(block.count("exact Int.emod_nonneg _ (by decide)"), len(mods))
                    self.assertEqual(block.count("exact Int.emod_lt_of_pos _ (by decide)"), len(mods))
                    self.assertEqual(block.count("rw [Int.emod_neg]; "),
                                     sum(1 for atom in mods if proof_to_lean._integer_divisor(graph, atom) < 0))
                    self.assertEqual("revert _m" in block, bool(mods))
                    self.assertEqual("have _m" in block, bool(mods))
                    # The fallback unfolds the atoms and everything under them.
                    fallback = block.split("    | (unfold ", 1)[1].split("\n", 1)[0].split()
                    for atom in atoms:
                        self.assertIn("term_%d" % atom, fallback)
            self.assertNotIn("sorry", text)
        self.assertEqual(generalized["lia_div"], {"farkas"})
        self.assertEqual(generalized["lia_mod_sum"], {"cut"})
        self.assertEqual(generalized["lia_abs"], {"farkas"})
        self.assertEqual(generalized["lia_gcd"], set())
        self.assertLessEqual({"farkas", "bound", "cut"}, generalized["wide"])
        # Real certificates are untouched.
        from test_proof_to_lean_arith import Z3TEST_LRA_INPUTS
        real_source = Z3TEST_LRA_INPUTS["lra_farkas"]
        self.assertNotIn("generalize", proof_to_lean.reconstruct(
            real_source, proof_certificate.export_clause_log_certificate(real_source)))

    def test_rewrites_bridge_atoms_with_one_key_before_generalizing(self):
        # Z3's rewriter logs (abs x) as (ite (<= 0 x) x (* -1 x)); the
        # rewrite relating an assertion over twelve abs terms to its normal
        # form is a tautology over 24 ite atoms, exponential for omega and
        # grind, which split them. abs is keyed as its defining ite, so
        # every pair with one key is bridged by an equality (a two-way
        # split) reverted into the goal, the atoms are generalized, and omega
        # proves the linear rest; the unfolded proof stays as the fallback.
        for ite in (False, True):
            source = wide_abs_instance(ite=ite)
            certificate = proof_certificate.export_clause_log_certificate(source)
            graph = proof_to_lean._validate_graph(source, certificate)
            text = proof_to_lean.reconstruct(source, certificate)
            magnitudes = [node for node in range(len(graph.nodes))
                          if graph.kind(node) == (z3.Z3_OP_ITE if ite else z3.Z3_OP_ABS) and graph.is_arith(node)
                          and graph.kind(graph.arguments(node)[-1]) == (z3.Z3_OP_UMINUS if ite else z3.Z3_OP_UNINTERPRETED)]
            normalized = [node for node in range(len(graph.nodes))
                          if graph.kind(node) == z3.Z3_OP_ITE and graph.is_arith(node)
                          and graph.kind(graph.arguments(node)[-1]) == z3.Z3_OP_MUL]
            self.assertEqual((len(magnitudes), len(normalized)), (12, 12))
            keys = {}
            for node in sorted(magnitudes + normalized, reverse=True):  # the order of _opaque_int_atoms
                keys.setdefault(proof_to_lean._real_atom_key(graph, node), []).append(node)
            self.assertEqual(len(keys), 12)
            for (kind, condition, then_key, else_key), members in keys.items():
                # The condition 0 <= x is keyed as the complement of its
                # canonical atom x + 1 <= 0 (leading coefficient positive),
                # so the branches are swapped: -x, then x.
                self.assertEqual((kind, condition[0], condition[2]), ("ite", "<=", 1))
                self.assertEqual(len(members), 2)
                variable = condition[1][0][0]
                self.assertEqual(condition[1], ((variable, 1),))
                self.assertEqual((then_key, else_key), ((((variable, -1),), 0), (((variable, 1),), 0)))
            wide = next(node for node in range(len(graph.nodes)) if graph.kind(node) == z3.Z3_OP_PR_REWRITE
                        and len(proof_to_lean._opaque_int_atoms(graph, [graph.conclusion(node)])) == 24)
            lemma = text.split("private theorem rewrite_%d " % wide, 1)[1].split("\n\n", 1)[0]
            atoms = proof_to_lean._opaque_int_atoms(graph, [graph.conclusion(wide)])
            bridges = [(first, second) for members in keys.values() for first, second in zip(members, members[1:])]
            self.assertEqual(len(bridges), 12)
            for first, second in bridges:
                self.assertIn("have _e%d_%d : (term_%d _atoms _vars) = (term_%d _atoms _vars) := by unfold "
                              % (first, second, first, second), lemma)
            self.assertEqual(lemma.count("; first | omega | grind (splits := 64)\n"), 12)
            self.assertIn("\n       revert " + " ".join("_e%d_%d" % pair for pair in bridges) + "\n", lemma)
            for position, atom in enumerate(atoms):
                self.assertIn("generalize (term_%d _atoms _vars) = _o%d\n" % (atom, position), lemma)
            self.assertIn("\n       omega)\n    | (unfold ", lemma)
            self.assertTrue(lemma.endswith("first | omega | grind (splits := 64))"), lemma[-200:])
            # A rewrite of one assertion bridges its one pair.
            self.assertEqual(text.count("revert _e"), 13)
            self.assertNotIn("sorry", text)
        # The condition of an ite is keyed up to Z3's normalization over
        # Int too: the strict (ite (> x 0) x (- x)), whose condition the
        # reconstructor tightens to x - 1 >= 0 and the rewriter writes as
        # (ite (<= x 0) (* -1 x) x), and (abs (* 2 x)), whose condition
        # 0 <= 2x the rewriter divides to 0 <= x, each bridge with their
        # rewriter's form (the canonical atom x <= 0 without a swap, and
        # the complement of x + 1 <= 0 with one).
        for source, constant in ((wide_abs_instance(variables=2, ite=True, strict=True), 0),
                                 (wide_abs_instance(variables=2, scale=2), 1)):
            certificate = proof_certificate.export_clause_log_certificate(source)
            graph = proof_to_lean._validate_graph(source, certificate)
            keys = {}
            for node in range(len(graph.nodes)):
                if graph.kind(node) in (z3.Z3_OP_ITE, z3.Z3_OP_ABS) and graph.is_arith(node):
                    keys.setdefault(proof_to_lean._real_atom_key(graph, node), []).append(node)
            self.assertEqual(sorted(len(members) for members in keys.values()), [2, 2])
            self.assertEqual({(key[1][0], key[1][1][0][1], key[1][2]) for key in keys}, {("<=", 1, constant)})
            self.assertEqual(proof_to_lean.reconstruct(source, certificate).count("revert _e"), 3)
        # Over Int the complement of x <= 0 is x >= 1, so (ite (<= x 0) a b)
        # and (ite (>= x 1) b a) have one key, and (ite (>= x 0) b a) another.
        source = "(set-logic QF_LIA)\n(declare-const x Int)\n(declare-const y Int)\n"
        source += "".join("(assert (>= (+ (ite %s) y) 1))\n" % ite for ite in (
            "(<= x 0) x y", "(>= x 1) y x", "(>= x 0) y x"))
        source += "(assert (<= y 0))\n(assert (<= (- x) 0))\n(check-sat)\n"
        graph = proof_to_lean._validate_graph(source, proof_certificate.export_clause_log_certificate(source))
        ites = [node for node in range(len(graph.nodes)) if graph.kind(node) == z3.Z3_OP_ITE and graph.is_arith(node)]
        keys = [proof_to_lean._real_atom_key(graph, node) for node in ites]
        self.assertEqual(len(ites), 6)  # the three of the input and the rewriter's form of each
        self.assertEqual(sorted(keys.count(key) for key in set(keys)), [2, 4])
        self.assertEqual(keys[0], keys[1])  # the input's ites come first (ids are topological)
        self.assertNotEqual(keys[1], keys[2])
        self.assertEqual(sorted(key[1][2] for key in set(keys)), [0, 1])

    def test_legacy_unsupported_label_is_a_coefficient_free_farkas(self):
        # theory_lra labels a conflict (_ th-lemma arith unsupported) when
        # its own Farkas check fails (a lattice conflict); the exporter keeps
        # it as a farkas step without coefficients, which the reconstructor
        # shape-checks (held integer linear premises, false conclusion) and
        # states for first | omega | grind, like a stripped Farkas step.
        for name in LEGACY_UNSUPPORTED_INPUTS:
            source = LIA_INPUTS[name]
            with self.subTest(name=name):
                context = z3.Context(proof=True)
                solver = z3.Solver(ctx=context)
                solver.set("combined_solver.ignore_solver1", True)
                solver.add(z3.parse_smt2_string(proof_certificate._assertion_commands(source), ctx=context))
                self.assertEqual(solver.check(), z3.unsat)
                labels = [node for node in _proof_nodes(solver.proof())
                          if node.decl().name() == "th-lemma"
                          and [str(p) for p in node.decl().params()] == ["arith", "unsupported"]]
                self.assertTrue(labels, "theory_lra no longer labels the conflict unsupported: if it now "
                                "emits farkas or lp-integer-lattice, drop the label assertions here and in "
                                "test_proof_certificate.py and keep the certificate checks (the exporter "
                                "mapping stays covered by its _FakeDecl cases)")
                self.assertTrue(all(z3.is_false(node.arg(node.num_args() - 1)) and node.num_args() > 1
                                    for node in labels))
                certificate = proof_certificate.export_certificate(source)
                self.assertEqual(certificate["fragment"], "qf_lia")
                nodes = [node for node in _th_lemma_nodes(certificate) if _parameters(certificate, node) == ["farkas"]]
                self.assertEqual(len(nodes), len(labels))
                graph = proof_to_lean._validate_graph(source, certificate)
                for node in nodes:
                    arguments = certificate["nodes"][node]["arguments"]
                    self.assertGreater(len(arguments), 1)
                    self.assertEqual(graph.kind(arguments[-1]), z3.Z3_OP_FALSE)
                    proof_to_lean._check_th_lemma(graph, node)
                text = proof_to_lean.reconstruct(source, certificate)
                self.assertIn("first | omega | grind", text)
                self.assertNotIn("sorry", text)
                # The region is rationally feasible, so no coefficients refute
                # the premises: a farkas with coefficients is rejected before Lean.
                tampered = copy.deepcopy(certificate)
                node = nodes[0]
                premises = len(tampered["nodes"][node]["arguments"]) - 1
                tampered["declarations"][tampered["nodes"][node]["declaration"]]["parameters"] = ["farkas"] + ["1"] * premises
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "do not refute"):
                    proof_to_lean.reconstruct(source, tampered)

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

    def test_wide_division_instance_verifies_over_generalized_atoms(self):
        source = random_division_instance(WIDE_DIVISION_SEED, variables=6, constraints=18)
        self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % WIDE_DIVISION_SEED)
        self.assertIn("(mod x4 -3)", source)
        certificate = self.check(source)
        self.assertLessEqual({"farkas", "bound", "cut"}, _hints(certificate))
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertIn("rw [Int.emod_neg]; exact Int.emod_lt_of_pos _ (by decide)", text)
        self.assertIn("\n       omega)\n    | (unfold ", text)
        self.assertIn("\n       grind (splits := 64))\n    | (unfold ", text)

    def test_wide_abs_sum_verifies_over_bridged_atoms(self):
        # Twelve abs terms in one assertion: the rewrite to the rewriter's
        # ite form exhausted maxHeartbeats (30 s) before the atoms of one
        # key were bridged and generalized; the whole file checks in
        # seconds now, through both cores and with the SMT-LIB definition
        # of abs written out as an ite.
        for ite in (False, True):
            source = wide_abs_instance(ite=ite)
            with self.subTest(ite=ite):
                certificate = self.check(source)
                self.assertEqual(_hints(certificate), {"farkas"})
                text = proof_to_lean.reconstruct(source, certificate)
                self.assertEqual(text.count("revert _e"), 13)
                # The 13 rewrites and the Farkas lemma over the 12 atoms.
                self.assertEqual(len(re.findall(r"\n       omega\)\n    \| \(unfold ", text)), 14)
        # The strict (ite (> x 0) x (- x)) and (abs (* 2 x)) bridge with the
        # rewriter's forms of their conditions (negated with the branches
        # swapped, divided by the coefficient); each timed out unbridged.
        for variant in (dict(ite=True, strict=True), dict(scale=2)):
            source = wide_abs_instance(**variant)
            with self.subTest(**variant):
                certificate = self.check(source)
                self.assertEqual(proof_to_lean.reconstruct(source, certificate).count("revert _e"), 13)
        source = wide_abs_instance()
        certificate = self.check(source, core="legacy")
        text = proof_to_lean.reconstruct(source, certificate)
        # The legacy core rewrites each abs term to its ite on its own.
        self.assertEqual(text.count("revert _e"), 12)
        self.assertRegex(text, r"private theorem rewrite_\d+ .*\n.*\n.*\n  first\n    \| \(have _e")

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

    def test_wide_rewrites_over_mod_atoms_take_the_normalized_path(self):
        # The linear forms may range over opaque terms without a formula
        # inside, keyed by node: here (mod x 10) in every atom. The ite
        # Z3 logs for abs is excluded (test_wide_abs_sum_verifies_over_bridged_atoms).
        source = wide_rewrite_instance(term="(mod {0} 10)")
        certificate = self.check(source)
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertIn("private theorem normalized_rewrite_", text)
        atoms = [line for line in text.splitlines() if line.startswith("  let _atom")]
        self.assertEqual(len(atoms), 18)
        self.assertTrue(all("(_vars " in line and " % (((10 : Int)))" in line for line in atoms), atoms[0])

    def test_wide_rewrites_deciding_a_mod_bound_stay_with_grind(self):
        # Z3's rewriter decides (< (mod x0 10) 0) and (>= (mod x0 10) 10)
        # from the bounds of mod, so the clause-log core's one rewrite step
        # drops the literal while every mod term stays in the other atoms.
        # The propositional lemma over abstract atoms cannot prove that, so
        # an atom whose key occurs on one side only and ranges over an
        # opaque term sends the rewrite to grind, which knows the bounds.
        for extra in ("(< (mod x0 10) 0)", "(>= (mod x0 10) 10)"):
            with self.subTest(extra=extra):
                source = wide_rewrite_instance(term="(mod {0} 10)")
                source = source.replace("(assert (or ", "(assert (or %s " % extra, 1)
                self.assertIn(extra, source)
                certificate = self.check(source)
                text = proof_to_lean.reconstruct(source, certificate)
                self.assertNotIn("normalized_rewrite_", text)
                self.assertIn("private theorem rewrite_", text)

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
        certificate["nodes"].append({"declaration": negation, "arguments": [bound]})
        exported = certificate
        # The same false unit under the cut hint is proved over the mod atom
        # generalized (with its bounds 0 <= m < 3 stated) before the unfolded
        # fallback: both must fail.
        for hint in ("arith", "cut"):
            certificate = copy.deepcopy(exported)
            declarations = certificate["declarations"]
            if hint == "arith":
                declaration = next(index for index, d in enumerate(declarations) if d["parameters"] == ["arith"])
            else:
                declarations.append({"kind": z3.Z3_OP_PR_TH_LEMMA, "name": "th-lemma", "domain": ["Bool"],
                                     "range": "Proof", "parameters": ["cut"]})
                declaration = len(declarations) - 1
            certificate["nodes"].append({"declaration": declaration, "arguments": [len(certificate["nodes"]) - 1]})
            certificate["rule_counts"]["th-lemma"] += 1
            text = proof_to_lean.reconstruct(source, certificate)
            lemma = text.split("private theorem th_lemma_%d " % (len(certificate["nodes"]) - 1), 1)[1].split("\n\n", 1)[0]
            self.assertEqual("generalize" in lemma, hint == "cut")
            self.assertEqual("exact Int.emod_nonneg _ (by decide)" in lemma, hint == "cut")
            with self.subTest(hint=hint), tempfile.TemporaryDirectory() as directory:
                output = Path(directory) / "checked.lean"
                with self.assertRaises(subprocess.CalledProcessError):
                    proof_to_lean.check_and_write(source, certificate, output)
                self.assertFalse(output.exists())

    def test_false_bridged_rewrites_are_rejected_by_lean(self):
        # The bridged attempt proves only what holds over the generalized
        # atoms: a rewrite claiming |x| >= 3 is 2 <= (ite (<= 0 x) x (-x))
        # passes every shape check (the node is a Boolean equivalence of
        # two linear atoms) and must fail both attempts in Lean.
        source = LIA_INPUTS["lia_abs"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        declarations, nodes = certificate["declarations"], certificate["nodes"]

        def kind(index):
            return declarations[nodes[index]["declaration"]]["kind"]

        rewrite = next(index for index in range(len(nodes)) if kind(index) == z3.Z3_OP_PR_REWRITE
                       and any(kind(sub) == z3.Z3_OP_ITE
                               for sub in nodes[nodes[nodes[index]["arguments"][-1]]["arguments"][1]]["arguments"]))
        equivalence = nodes[rewrite]["arguments"][-1]
        left, right = nodes[equivalence]["arguments"]
        bound, ite = nodes[right]["arguments"]
        self.assertEqual((kind(right), kind(ite)), (z3.Z3_OP_LE, z3.Z3_OP_ITE))
        self.assertEqual(declarations[nodes[bound]["declaration"]]["name"], "3")
        # A second rewrite with the forged conclusion (a fresh numeral 2,
        # 2 <= ite, the equivalence), unused by the refutation: every
        # rewrite is a lemma Lean checks, and the consumers of the genuine
        # one keep their shapes.
        declarations.append(dict(declarations[nodes[bound]["declaration"]], name="2"))
        nodes.append({"declaration": len(declarations) - 1, "arguments": []})
        nodes.append({"declaration": nodes[right]["declaration"], "arguments": [len(nodes) - 1, ite]})
        nodes.append({"declaration": nodes[equivalence]["declaration"], "arguments": [left, len(nodes) - 1]})
        nodes.append({"declaration": nodes[rewrite]["declaration"], "arguments": [len(nodes) - 1]})
        certificate["rule_counts"]["rewrite"] += 1
        rewrite = len(nodes) - 1
        text = proof_to_lean.reconstruct(source, certificate)
        lemma = text.split("private theorem rewrite_%d " % rewrite, 1)[1].split("\n\n", 1)[0]
        self.assertIn("have _e", lemma)
        self.assertIn("\n       omega)\n    | (unfold ", lemma)
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "checked.lean"
            with self.assertRaises(subprocess.CalledProcessError):
                proof_to_lean.check_and_write(source, certificate, output)
            self.assertFalse(output.exists())

    def test_generalized_attempt_falls_through_to_the_unfolded_proof(self):
        # The unit x >= 3 * (div x 3) holds by the Euclidean definition and
        # passes the cut's shape check, but not over the div atom generalized
        # to an integer (the mod axioms relabelled as cuts would not do: the
        # stated mod bounds prove them generalized). The first attempt fails,
        # the unfolded fallback under first proves it, and Lean accepts the
        # certificate; without the fallback it is rejected (checked when the
        # test was written).
        source = LIA_INPUTS["lia_div"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        declarations, nodes = certificate["declarations"], certificate["nodes"]

        def name(index):
            return declarations[nodes[index]["declaration"]]["name"]

        x = next(index for index, raw in enumerate(nodes) if name(index) == "x" and not raw["arguments"])
        product = next(index for index, raw in enumerate(nodes)
                       if name(index) == "*" and {name(arg) for arg in raw["arguments"]} == {"3", "div"})
        division = next(arg for arg in nodes[product]["arguments"] if name(arg) == "div")
        at_least = next(index for index, d in enumerate(declarations)
                        if d["kind"] == z3.Z3_OP_GE and d["domain"] == ["Int", "Int"])
        declarations.append({"kind": z3.Z3_OP_PR_TH_LEMMA, "name": "th-lemma", "domain": ["Bool"],
                             "range": "Proof", "parameters": ["cut"]})
        nodes.append({"declaration": at_least, "arguments": [x, product]})
        nodes.append({"declaration": len(declarations) - 1, "arguments": [len(nodes) - 1]})
        certificate["rule_counts"]["th-lemma"] += 1
        text = proof_to_lean.reconstruct(source, certificate)
        lemma = text.split("private theorem th_lemma_%d " % (len(nodes) - 1), 1)[1].split("\n\n", 1)[0]
        self.assertIn("generalize (term_%d _atoms _vars) = _o0\n" % division, lemma)
        self.assertNotIn("revert", lemma)
        self.assertIn("\n       grind (splits := 64))\n    | (unfold ", lemma)
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "checked.lean"
            proof_to_lean.check_and_write(source, certificate, output)
            self.assertTrue(output.exists())


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
                    # Integer rounding is proved separately from the final
                    # linear combination of the rounded bounds.
                    self.assertIn(["arith"], parameters)
                    self.assertTrue(any(p[0] == "farkas" and len(p) > 1 for p in parameters), parameters)
                if name == "lia_equality_elimination":
                    # A cut: a bare arith step deriving its bound from the premises it lists.
                    self.assertTrue(any(p == ["arith"] and len(certificate["nodes"][node]["arguments"]) > 1
                                        for node, p in zip(_th_lemma_nodes(certificate), parameters)), parameters)
                if name in ("lia_div", "lia_mod_sum", "lia_div_sum"):
                    # The div and mod axioms, stated (or false l) and resolved with the unit true.
                    self.assertIn("arith", _hints(certificate))
                    self.assertEqual(certificate["rule_counts"]["true-axiom"], 1)
                if name in LEGACY_UNSUPPORTED_INPUTS:
                    # theory_lra's unsupported label became a coefficient-free
                    # farkas refuting its premises (the label itself is pinned
                    # in test_legacy_unsupported_label_is_a_coefficient_free_farkas).
                    self.assertTrue(any(p == ["farkas"] and len(certificate["nodes"][node]["arguments"]) > 1
                                        for node, p in zip(_th_lemma_nodes(certificate), parameters)), parameters)
                if name == "lia_lattice_bounds":
                    self.assertTrue(any(p == ["arith"] and len(certificate["nodes"][node]["arguments"]) > 1
                                        for node, p in zip(_th_lemma_nodes(certificate), parameters)), parameters)
        # The legacy core's hints: no cut or euf (its congruences are
        # monotonicity steps), plus the bare arith of its axioms and cuts.
        self.assertEqual(hints, {"farkas", "bound", "triangle-eq", "arith", "smt"})

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
        # Keep one satisfiable bound premise and drop the final conflict's
        # coefficients: the shape check passes, but Lean must reject it.
        source = LIA_INPUTS["lia_gomory"]
        certificate = proof_certificate.export_certificate(source)
        node = next(n for n in _th_lemma_nodes(certificate) if _parameters(certificate, n)[0] == "farkas")
        arguments = certificate["nodes"][node]["arguments"]
        certificate["declarations"].append({"kind": z3.Z3_OP_PR_TH_LEMMA, "name": "th-lemma",
                                            "domain": ["Proof", "Bool"], "range": "Proof",
                                            "parameters": ["farkas"]})
        certificate["nodes"][node] = {"declaration": len(certificate["declarations"]) - 1,
                                      "arguments": arguments[:1] + arguments[-1:]}
        graph = proof_to_lean._validate_graph(source, certificate)
        proof_to_lean._check_th_lemma(graph, node)
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "checked.lean"
            with self.assertRaises(subprocess.CalledProcessError):
                proof_to_lean.check_and_write(source, certificate, output)
            self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
