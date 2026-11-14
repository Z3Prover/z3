############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Tests for the sign split of products of Int terms in the Lean
# reconstruction. Z3's rewriter decides a comparison of a polynomial with
# zero by the signs of its factors (arith_rewriter.cpp, factor_le_ge_eq):
# (>= (+ (* -2 m) (* -3 (* n m))) 0) becomes (or (= 0 m) (= (<= 0 m) (<= n
# -1))). The step reaches the certificate as a rewrite of the assertion, as
# a cnf lemma tying a clause Z3 logged in the rewritten form to the
# assertion, or as a theory clause between the leaves of such a lemma.
# omega, to which a product is an opaque atom, and grind do not prove it;
# the reconstructor factors the polynomial again, splits on the signs of the
# factors, and derives the sign of the product in every case
# (proof_to_lean._sign_split). Nothing about it is trusted: an input that
# needs more than the signs fails in Lean as before.
# Validation without Lean, and end-to-end checks that need the z3 executable
# and the pinned Lean toolchain.
############################################
from fractions import Fraction
import functools
from pathlib import Path
import re
import sys
import tempfile
import unittest
import warnings

import z3

_EXAMPLES = Path(__file__).resolve().parent
sys.path.insert(0, str(_EXAMPLES))
import proof_certificate
import proof_clause_log
import lean_test_support
import proof_to_lean
from test_proof_to_lean_array import _export
from test_proof_to_lean_lia import _STANDARD_AXIOMS, _z3_available
from test_proof_to_lean_nonlinear import PRODUCT_INPUTS, random_product_instance

_INTS = "(declare-const m Int)\n(declare-const n Int)\n(declare-const k Int)\n"
_CHECK = "(check-sat)\n"

# Documented inputs whose refutations rest on the signs of the factors of a
# product: the fragment, the input, and the kinds of steps proved by a sign
# split (rewrite steps, cnf lemmas). All of them failed in Lean before.
SIGN_INPUTS = {
    # (>= p 0): m (-2 - 3 n) >= 0 with m positive bounds n by -1, the quotient's sign rounded over Int.
    "nonnegative_product": ("qf_lia", _INTS + """(assert (>= (+ (* (- 2) m) (* (- 3) (* n m))) 0))
(assert (>= m 1))
(assert (>= n 0))
""", {"rewrite"}),
    # (<= p 0).
    "nonpositive_product": ("qf_lia", _INTS + """(assert (<= (* m n) 0))
(assert (>= m 1))
(assert (>= n 1))
""", {"rewrite"}),
    # (= p 0): m (3 n - 2) = 0 leaves m = 0, the quotient having no integer root.
    "zero_product_without_a_root": ("qf_lia", _INTS + """(assert (= (+ (* (- 2) m) (* 3 (* m n))) 0))
(assert (not (= m 0)))
""", {"rewrite", "th_lemma"}),
    # Three factors: m n (2 n - 1), the quotient's sign following that of n.
    "factors_of_the_quotient": ("qf_lia", _INTS + """(assert (< (- (* 2 (* n m n)) (* n m)) 0))
(assert (>= m 1))
(assert (>= n 1))
""", {"th_lemma"}),
    # The quotient m m - 2 k n is no linear term: its sign is that of a comparison of products.
    "quotient_over_products": ("qf_lia", _INTS + """(assert (<= (+ (* m m k) (* (- 2) (* k k n))) 0))
(assert (>= k 1))
(assert (> (* m m) (* 2 (* k n))))
""", {"rewrite"}),
    "five_factors": ("qf_lia", _INTS + """(declare-const j Int)
(declare-const i Int)
(assert (< (* m n k j i) 0))
(assert (> m 0))
(assert (> n 0))
(assert (> k 0))
(assert (> j 0))
(assert (> i 0))
""", {"th_lemma"}),
    # Z3 logs the conjuncts in the rewriter's form: the cnf lemmas tie them to the conjunction.
    "conjunction": ("qf_lia", _INTS + "(assert (and (< 0 (* m n)) (>= m 0) (< n 0)))\n", {"th_lemma"}),
    "negated_disjunction": ("qf_lia", _INTS + "(assert (not (or (<= (* m n) 0) (< m 0) (> n 0))))\n",
                            {"th_lemma"}),
    # z3test regressions/smt2/nl38.smt2: the sign of b d from those of a b, c d, and a c.
    "chain_of_signs": ("qf_lia", """(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)
(assert (and (< 0 (* a b)) (< 0 (* c d)) (< 0 (* a c)) (not (< 0 (* b d)))))
""", {"rewrite", "th_lemma"}),
    # m (2 - 3 m) > 1 is false by the signs of the factors; nlsat's empty clause is tied to it by a rewrite.
    "square_against_its_root": ("qf_lia", _INTS + "(assert (> (+ (* (- 3) (* m m)) (* 2 m)) 1))\n", {"rewrite"}),
    # An application as a factor: an opaque atom of the linear forms, whose sign is split like a variable's.
    "function_factor": ("qf_uflia", "(declare-fun g (Int) Int)\n" + _INTS + """(assert (<= (* (g m) n) 0))
(assert (> (g m) 0))
(assert (> n 0))
""", {"rewrite"}),
    # The rewriter splits (<= (* m n) 0) and keeps (>= (* m n) 7), a comparison of the same monomials.
    "split_next_to_a_kept_comparison": ("qf_lia", _INTS + """(assert (or (<= (* m n) 0) (>= (* m n) 7)))
(assert (> m 0))
(assert (> n 0))
(assert (< (* m n) 7))
""", {"rewrite"}),
    # A predicate application next to the product: an atom of the step's propositional structure.
    "predicate_next_to_the_product": ("qf_uflia", "(declare-fun q (Int) Bool)\n" + _INTS + """\
(assert (or (q m) (<= (* m n) 0)))
(assert (not (q m)))
(assert (> m 0))
(assert (> n 0))
""", {"rewrite"}),
    # An ite of formulas, its branches normalized by the same rewrite: a connective of the step.
    "ite_of_formulas": ("qf_lia", "(declare-const p Bool)\n" + _INTS + """\
(assert (or (ite p (> k 0) (< k 0)) (<= (* m n) 0)))
(assert (= k 0))
(assert (> m 0))
(assert (> n 0))
""", {"rewrite"}),
    # A monomial equated with zero is left to Int.mul_eq_zero only where nothing else is split.
    "zero_product_next_to_a_split": ("qf_lia", _INTS + """(assert (or (= (* m n) 0) (<= (* m k) 0)))
(assert (> m 0))
(assert (> n 0))
(assert (> k 0))
""", {"rewrite"}),
}
SIGN_INPUTS = {name: (fragment, source + _CHECK, kinds) for name, (fragment, source, kinds) in SIGN_INPUTS.items()}

# The inputs of SIGN_INPUTS whose refutations verify through the legacy proof object too, where the
# split is a rewrite step of the assertion. (Of the others, factors_of_the_quotient and five_factors
# fail in Lean there, as before, on a rewrite step that gets a split; square_against_its_root is
# rejected by the exporter: th-lemma arith assumed nlsat.)
LEGACY_SIGN_INPUTS = ("nonnegative_product", "nonpositive_product", "zero_product_without_a_root",
                      "quotient_over_products", "conjunction", "negated_disjunction", "chain_of_signs",
                      "function_factor", "split_next_to_a_kept_comparison", "predicate_next_to_the_product",
                      "ite_of_formulas", "zero_product_next_to_a_split")

# Inputs that get a sign split and are not certified by it: Lean rejects them.
NOT_CERTIFIED = {
    # 3 is no square: the signs of m and of m m decide nothing.
    "square_is_three": _INTS + "(assert (= (* m m) 3))\n" + _CHECK,
}

# Seeds of test_proof_to_lean_nonlinear.random_product_instance whose
# refutations failed in Lean on a sign split and verify now: the rewrite of
# a comparison (31, 152), factors of the quotient (37), a quotient over
# products (148), a product written in two orders (394), theory clauses of
# cnf lemmas (292, 500), the square of an atom next to the split (726,
# 1128), and a comparison split next to one over the same products that the
# rewriter only normalized (894). Of the unsatisfiable seeds 1-1200, 441 of
# 460 verify (375 before).
SIGN_SEEDS = (31, 37, 148, 152, 292, 394, 500, 726, 894, 1128)

# The log of nonnegative_product: the assertion over the product is assumed in the rewriter's form.
_NONNEGATIVE_LOG = """\
(declare-fun m () Int)
(define-const $31 Bool (>= m 0))
(declare-fun n () Int)
(define-const $25 Bool (<= n (- 1)))
(define-const $35 Bool (= $31 $25))
(declare-fun tseitin (Bool Bool Bool) Proof)
(define-const $40 Bool (not $31))
(define-const $39 Bool (not $35))
(define-const $41 Proof (tseitin $39 $25 $40))
(infer (not $31) $25 (not $35) $41)
(define-const $42 Bool (not $25))
(define-const $43 Proof (tseitin $39 $42 $31))
(infer $31 (not $25) (not $35) $43)
(define-const $44 Proof (tseitin $35 $25 $31))
(infer $31 $25 $35 $44)
(define-const $45 Proof (tseitin $35 $42 $40))
(infer (not $31) (not $25) $35 $45)
(define-const $28 Bool (= m 0))
(assume $28 $35)
(define-const $18 Bool (>= m 1))
(assume $18)
(define-const $19 Bool (>= n 0))
(assume $19)
(declare-fun farkas (Int Bool Int Bool) Proof)
(define-const $46 Proof (farkas 1 $25 1 $19))
(infer (not $25) $46)
(define-const $47 Proof (farkas 1 $40 1 $18))
(infer $31 $47)
(declare-fun rup () Proof)
(infer (not $35) rup)
(infer $28 rup)
(define-const $49 Proof (farkas 1 $28 1 $18))
(infer (not $18) (not $28) $49)
(declare-fun euf (Bool Bool) Proof)
(define-const $50 Bool (not $28))
(define-const $51 Proof (euf $50 $28))
(infer (not $28) $28 $51)
(infer rup)
"""
# The log of zero_product_without_a_root: the first assertion is assumed as (= m 0), the second as the empty clause.
_ZERO_LOG = """\
(declare-fun m () Int)
(define-const $16 Bool (= m 0))
(assume $16)
(assume)
(declare-fun rup () Proof)
(infer rup)
"""
# The log of conjunction: the conjunct over the product is assumed as (>= n 0), what it gives next to (>= m 0).
_CONJUNCTION_LOG = """\
(declare-fun m () Int)
(define-const $10 Bool (>= m 0))
(assume $10)
(declare-fun n () Int)
(define-const $24 Bool (<= 0 n))
(assume (not $24))
(define-const $18 Bool (>= n 0))
(assume $18)
(define-const $15 Bool (= m 0))
(assume (not $15))
(define-const $16 Bool (= n 0))
(assume (not $16))
(declare-fun farkas (Int Bool Int Bool) Proof)
(define-const $25 Bool (not $24))
(define-const $31 Proof (farkas 1 $18 1 $25))
(infer (not $18) $24 $31)
(declare-fun rup () Proof)
(infer rup)
"""
_PINNED_LOGS = {"nonnegative_product": _NONNEGATIVE_LOG, "zero_product_without_a_root": _ZERO_LOG,
                "conjunction": _CONJUNCTION_LOG}
# A step whose sign split fails in Lean and whose other proofs hold: the rewriter turns (abs n) into an
# ite, another atom to the split, which keeps atoms folded; the next proof equates the two atoms.
_FALLBACK_SOURCE = _INTS + "(assert (> (* m (abs n)) 2))\n(assert (< (* (abs n) m) 1))\n" + _CHECK
_FALLBACK_LOG = """\
(declare-fun n () Int)
(define-const $15 Bool (>= n 0))
(define-const $19 Int (* (- 1) n))
(define-const $20 Int (ite $15 n $19))
(define-const $29 Bool (= $20 n))
(declare-fun tseitin (Bool Bool) Proof)
(define-const $28 Bool (not $15))
(define-const $31 Proof (tseitin $28 $29))
(infer (not $15) $29 $31)
(define-const $30 Bool (= $20 $19))
(define-const $32 Proof (tseitin $15 $30))
(infer $15 $30 $32)
(declare-fun m () Int)
(define-const $21 Int (* m $20))
(define-const $22 Bool (<= $21 2))
(assume (not $22))
(define-const $24 Bool (<= 1 $21))
(assume (not $24))
(declare-fun farkas (Int Bool Int Bool) Proof)
(define-const $23 Bool (not $22))
(define-const $25 Bool (not $24))
(define-const $33 Proof (farkas 1 $25 1 $23))
(infer $33)
(declare-fun rup () Proof)
(infer rup)
"""


@functools.lru_cache(maxsize=None)
def _certificate(name):
    """The clause-log certificate of a documented input, exported once for the module."""
    return _export(SIGN_INPUTS[name][1])


@functools.lru_cache(maxsize=None)
def _legacy_certificate(name):
    """The certificate of a documented input from the legacy proof object, exported once for the module."""
    return proof_certificate.export_certificate(SIGN_INPUTS[name][1])


def _replay(name):
    """The certificate of a documented input from its pinned log, whatever Z3 logs today."""
    return _replay_log(SIGN_INPUTS[name][1], _PINNED_LOGS[name])


def _replay_log(source, log):
    context = z3.Context()
    assertions, fragment = proof_certificate.parse_assertions(source, context, integer=True)
    return proof_clause_log.build_certificate(source, fragment, assertions, log, context)


def _split_alone(text):
    """A reconstruction with the steps that start with a sign split left no other proof, and their number.

    The proofs of a step are the alternatives of one `first`, the split's
    the first of them (it starts from the folded goal, `show`); a blank
    line ends the step.
    """
    kept, steps, split, dropping = [], 0, False, False
    for line in text.split("\n"):
        if not line:
            split = dropping = False
        elif line.startswith("    | (show "):
            split, steps = True, steps + 1
        elif line.startswith("    | (") and split:
            dropping = True
        if not dropping:
            kept.append(line)
    return "\n".join(kept), steps


def _split_steps(text):
    """The theorems of a reconstruction proved by a sign split, each with the number of its splits."""
    steps, name = {}, None
    for line in text.split("\n"):
        match = re.match(r"(?:private )?theorem (\w+)", line)
        if match:
            name = match.group(1)
        elif "rcases Int.lt_trichotomy" in line:
            steps[name] = steps.get(name, 0) + 1
    return steps


def _kinds(steps):
    return {name.rsplit("_", 1)[0] for name in steps}


def _steps(graph, kind, hint=None):
    return [node for node in range(len(graph.nodes)) if graph.kind(node) == kind
            and (hint is None or graph.decl(node).parameters[:1] == (hint,))]


class TestSignFactoring(unittest.TestCase):
    """The factoring of a polynomial by the atoms its monomials share: no z3 executable, no Lean."""

    def test_common_factors(self):
        one = Fraction(1)
        # 2 a b + 3 a + 5 = a (2 b + 3) + 5.
        self.assertEqual(proof_to_lean._common_factors({(1, 2): 2 * one, (1,): 3 * one, (): 5 * one}),
                         ([1], {(2,): 2 * one, (): 3 * one}, 5 * one))
        # -4 a b = a b * -4: the quotient is the coefficient.
        self.assertEqual(proof_to_lean._common_factors({(1, 2): -4 * one}), ([1, 2], {(): -4 * one}, 0))
        # a a b - a a = a a (b - 1): a factor as often as every monomial has it.
        self.assertEqual(proof_to_lean._common_factors({(1, 1, 2): one, (1, 1): -one}),
                         ([1, 1], {(2,): one, (): -one}, 0))
        # 2 a b a - a b = a b (2 a - 1).
        self.assertEqual(proof_to_lean._common_factors({(1, 1, 2): 2 * one, (1, 2): -one}),
                         ([1, 2], {(1,): 2 * one, (): -one}, 0))
        for polynomial in ({(1, 2): one, (3,): one}, {(): one}, {}):
            with self.subTest(polynomial=polynomial):
                self.assertIsNone(proof_to_lean._common_factors(polynomial))

    def test_shapes(self):
        one = Fraction(1)
        shape = proof_to_lean._polynomial_shape
        # A comparison normalized (scaled, its constant moved or tightened) keeps its shape.
        self.assertEqual(shape({(1, 2): -4 * one, (3,): 2 * one, (): one}), shape({(1, 2): 2 * one, (3,): -one}))
        self.assertNotEqual(shape({(1, 2): one, (3,): one}), shape({(1, 2): one, (3,): -one}))
        self.assertNotEqual(shape({(1, 2): one}), shape({(1,): one}))
        self.assertEqual(shape({(): one}), ())

    def test_comparisons_with_zero(self):
        # What Z3's rewriter splits: a comparison that, divided by the gcd of its coefficients
        # and rounded, has a zero right side. The polynomial is that of left - right.
        one = Fraction(1)
        zero = proof_to_lean._compares_with_zero
        le, ge, lt, gt, eq = z3.Z3_OP_LE, z3.Z3_OP_GE, z3.Z3_OP_LT, z3.Z3_OP_GT, z3.Z3_OP_EQ
        product = {(1, 2): one}
        for kind in (le, ge, lt, gt, eq):
            with self.subTest(kind=kind):
                self.assertTrue(zero(kind, product))
                self.assertFalse(zero(kind, {**product, (): -7 * one}))
                self.assertFalse(zero(kind, {(): 0 * one}))
        double = {(1, 2): 2 * one, (3,): -4 * one}
        # 2 v <= 1 is v <= 0, 2 v <= -1 is v <= -1; 2 v >= -1 is v >= 0, 2 v >= 1 is v >= 1.
        for kind, constant, expected in [(le, -1, True), (le, 1, False), (le, -2, False), (ge, 1, True),
                                         (ge, -1, False), (ge, 2, False),
                                         # 2 v < 1 is not (v >= 1), 2 v < -1 is not (v >= 0); 2 v > -1 is
                                         # not (v <= -1), 2 v > 1 is not (v <= 0).
                                         (lt, -1, False), (lt, 1, True), (gt, 1, False), (gt, -1, True),
                                         # An equation is not rounded: 2 v = 1 is false.
                                         (eq, -1, False), (eq, 1, False)]:
            with self.subTest(kind=kind, constant=constant):
                self.assertEqual(zero(kind, {**double, (): constant * one}), expected)


class TestSignSplitValidation(unittest.TestCase):
    """Validation without Lean: which steps get a sign split, and its shape."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")

    def test_documented_inputs_get_sign_splits(self):
        for name, (fragment, source, kinds) in SIGN_INPUTS.items():
            with self.subTest(name=name):
                certificate = _certificate(name)
                self.assertEqual(certificate["fragment"], fragment)
                text = proof_to_lean.reconstruct(source, certificate)
                self.assertEqual(_kinds(_split_steps(text)), kinds)
                self.assertNotIn("sorry", text)

    def test_legacy_rewrites_get_sign_splits(self):
        for name in LEGACY_SIGN_INPUTS:
            with self.subTest(name=name):
                text = proof_to_lean.reconstruct(SIGN_INPUTS[name][1], _legacy_certificate(name))
                self.assertEqual(_kinds(_split_steps(text)), {"rewrite"})
                self.assertNotIn("sorry", text)

    def test_a_rewrite_is_proved_by_the_signs_of_its_factors(self):
        source = SIGN_INPUTS["nonnegative_product"][1]
        certificate = _replay("nonnegative_product")
        graph = proof_to_lean._validate_graph(source, certificate)
        rewrites = {node: proof_to_lean._sign_split(graph, node, rewrite=True)
                    for node in _steps(graph, z3.Z3_OP_PR_REWRITE)}
        # The rewrites of the two bounds only normalize them.
        self.assertEqual(sorted(lines is None for lines in rewrites.values()), [False, True, True])
        node, lines = next((node, lines) for node, lines in rewrites.items() if lines)
        self.assertEqual(lines[0], "show (formula_%d _atoms _vars)" % graph.conclusion(node))
        # -2 m - 3 n m - 0 = 1 * (m * (-2 + -3 n)) + 0, over the folded atoms.
        identity = re.fullmatch(
            r"have _i0 : \(term_\d+ _atoms _vars\) - \(term_\d+ _atoms _vars\) = \(\(1 : Int\)\) \* "
            r"\(\((term_\d+) _atoms _vars\) \* \(\(\(-2 : Int\)\) \+ \(\(\(-3 : Int\)\) \* "
            r"\((term_\d+) _atoms _vars\)\)\)\) \+ \(\(0 : Int\)\) := by delta [a-z_0-9 ]+; grind", lines[1])
        self.assertIsNotNone(identity, lines[1])
        self.assertNotEqual(identity.group(1), identity.group(2))
        self.assertEqual(lines[2], "revert _i0")
        self.assertTrue(lines[3].startswith("unfold formula_%d " % graph.conclusion(node)), lines[3])
        self.assertEqual(lines[4], "intro _i0")
        # m is split, and the quotient where m is not zero: seven cases.
        cases = "\n".join(lines[5:])
        self.assertEqual(cases.count("rcases Int.lt_trichotomy"), 3)
        self.assertEqual(cases.count("have _e0 :"), 7)
        for lemma, count in [("Int.mul_pos ", 1), ("Int.mul_pos_of_neg_of_neg ", 1),
                             ("Int.mul_neg_of_pos_of_neg ", 1), ("Int.mul_neg_of_neg_of_pos ", 1),
                             ("Int.mul_eq_zero.mpr (Or.inl _s0)", 1), ("Int.mul_eq_zero.mpr (Or.inr _s1)", 2)]:
            self.assertEqual(cases.count(lemma), count, lemma)
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertEqual(_split_steps(text), {"rewrite_%d" % node: 3})

    def test_a_cnf_lemma_is_proved_by_the_signs_of_its_factors(self):
        # The lemma is one theory fact: m (3 n - 2) = 0 and m != 0 are contradictory.
        source = SIGN_INPUTS["zero_product_without_a_root"][1]
        certificate = _replay("zero_product_without_a_root")
        graph = proof_to_lean._validate_graph(source, certificate)
        lemma, = _steps(graph, z3.Z3_OP_PR_TH_LEMMA, "cnf")
        lines = proof_to_lean._sign_split(graph, lemma)
        self.assertEqual(lines[0], "show (formula_%d _atoms _vars)" % graph.conclusion(lemma))
        self.assertEqual(sum("rcases Int.lt_trichotomy" in line for line in lines), 3)
        rewrite, = [node for node in _steps(graph, z3.Z3_OP_PR_REWRITE)
                    if proof_to_lean._sign_split(graph, node, rewrite=True)]
        self.assertEqual(_split_steps(proof_to_lean.reconstruct(source, certificate)),
                         {"rewrite_%d" % rewrite: 3, "th_lemma_%d" % lemma: 3})

    def test_a_theory_clause_is_proved_by_the_signs_of_its_factors(self):
        # 0 < m n and 0 <= m give 0 <= n: a clause over three leaves of the cnf lemma, each
        # stated with a `have` whose first proof is the split, the unfolded tactic its fallback.
        source = SIGN_INPUTS["conjunction"][1]
        certificate = _replay("conjunction")
        text = proof_to_lean.reconstruct(source, certificate)
        steps = _split_steps(text)
        self.assertEqual(_kinds(steps), {"th_lemma"})
        clauses = re.findall(r"have _f\d+ : \(Or [^\n]*\) := by\n +first\n +\| \(have _i0 :", text)
        self.assertEqual(len(clauses), len(steps))
        self.assertTrue(clauses)
        # A bridge between two leaves of one constraint is no theory clause: no split.
        graph = proof_to_lean._validate_graph(source, certificate)
        self.assertIsNone(proof_to_lean._sign_split_clause(graph, ("leaf", -1, "")))

    def test_steps_the_split_does_not_read_get_none(self):
        # Rewrites that only normalize a comparison over a product, and certificates without one.
        for name in ("bounds_on_a_product", "tightened_bounds_on_a_product", "scaled_products",
                     "parity_of_a_product"):
            with self.subTest(name=name):
                source = PRODUCT_INPUTS[name][1]
                self.assertEqual(_split_steps(proof_to_lean.reconstruct(source, _export(source))), {})
        linear = _INTS + "(assert (> (+ m n) 2))\n(assert (< (+ (* 2 m) (* 2 n)) 5))\n" + _CHECK
        certificate = _export(linear)
        graph = proof_to_lean._validate_graph(linear, certificate)
        self.assertFalse(graph.integer_products)
        for node in _steps(graph, z3.Z3_OP_PR_REWRITE):
            self.assertIsNone(proof_to_lean._sign_split(graph, node, rewrite=True))
        # A monomial equated with zero is Int.mul_eq_zero, which the step's grind has: no split.
        for name in ("zero_product", "zero_product_of_three"):
            with self.subTest(name=name):
                source = PRODUCT_INPUTS[name][1]
                self.assertEqual(_split_steps(proof_to_lean.reconstruct(source, _export(source))), {})
        # More factors than the split takes: the step keeps its other proofs.
        factors = ["x%d" % position for position in range(proof_to_lean._SIGN_SPLIT_FACTORS + 1)]
        wide = ("".join("(declare-const %s Int)\n" % factor for factor in factors)
                + "(assert (< (* %s) 0))\n" % " ".join(factors)
                + "".join("(assert (> %s 0))\n" % factor for factor in factors) + _CHECK)
        self.assertEqual(_split_steps(proof_to_lean.reconstruct(wide, _export(wide))), {})

    def test_a_split_comparison_next_to_a_kept_one_is_a_candidate(self):
        # (or (<= (* m n) 0) (>= (* m n) 7)): the right side keeps (>= (* m n) 7), which is not
        # what the rewriter made of (<= (* m n) 0); only that comparison is factored.
        source = SIGN_INPUTS["split_next_to_a_kept_comparison"][1]
        graph = proof_to_lean._validate_graph(source, _certificate("split_next_to_a_kept_comparison"))
        split = [lines for lines in (proof_to_lean._sign_split(graph, node, rewrite=True)
                                     for node in _steps(graph, z3.Z3_OP_PR_REWRITE)) if lines]
        self.assertEqual(len(split), 1)
        self.assertEqual(sum(line.startswith("have _i") for line in split[0]), 1)
        self.assertIn("+ ((0 : Int)) := by delta", split[0][1])

    def test_formulas_the_split_does_not_read_stay_folded(self):
        # The predicate application is no comparison of Int terms: the split's unfold leaves its definition.
        source = SIGN_INPUTS["predicate_next_to_the_product"][1]
        graph = proof_to_lean._validate_graph(source, _certificate("predicate_next_to_the_product"))
        applications = {"formula_%d" % node for node in range(len(graph.nodes))
                        if not graph.is_term(node) and graph.kind(node) == z3.Z3_OP_UNINTERPRETED
                        and graph.arguments(node)}
        self.assertTrue(applications)
        split = [lines for lines in (proof_to_lean._sign_split(graph, node, rewrite=True)
                                     for node in _steps(graph, z3.Z3_OP_PR_REWRITE)) if lines]
        self.assertEqual(len(split), 1)
        unfold, = [line for line in split[0] if line.startswith("unfold ")]
        self.assertFalse(applications & set(unfold.split()), unfold)

    def test_a_failing_split_is_followed_by_the_other_proofs(self):
        text = proof_to_lean.reconstruct(_FALLBACK_SOURCE, _replay_log(_FALLBACK_SOURCE, _FALLBACK_LOG))
        steps = _split_steps(text)
        self.assertEqual(_kinds(steps), {"rewrite"})
        alone, cut = _split_alone(text)
        self.assertEqual(cut, len(steps))
        self.assertEqual(_split_steps(alone), steps)
        # Every step with a split has at least one more alternative, and only those are dropped.
        self.assertGreaterEqual(text.count("\n    | (") - alone.count("\n    | ("), cut)
        self.assertEqual(text.count("theorem "), alone.count("theorem "))

    def test_pinned_seeds_get_sign_splits(self):
        for seed in SIGN_SEEDS:
            with self.subTest(seed=seed):
                source = random_product_instance(seed)
                self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % seed)
                self.assertTrue(_split_steps(proof_to_lean.reconstruct(source, _export(source))))


class TestSignSplitLeanIntegration(unittest.TestCase):
    """End-to-end: clause log, certificate, Lean reconstruction, kernel check."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")

    def _verify(self, checks):
        """Check (label, source, certificate) triples in Lean, in batches."""
        lean_test_support.prefetch((source, certificate) for _, source, certificate in checks)
        for label, source, certificate in checks:
            with self.subTest(input=label):
                _, report = lean_test_support.check(self, source, certificate)
                self.assertTrue(_STANDARD_AXIOMS in report or "does not depend on any axioms" in report, report)

    def test_documented_inputs_verify(self):
        checks = []
        for name, (_, source, _) in SIGN_INPUTS.items():
            with self.subTest(name=name):
                checks.append((name, source, _certificate(name)))
        self._verify(checks)

    def test_legacy_inputs_verify(self):
        self._verify([("legacy " + name, SIGN_INPUTS[name][1], _legacy_certificate(name))
                      for name in LEGACY_SIGN_INPUTS])

    def test_pinned_logs_verify(self):
        self._verify([(name, SIGN_INPUTS[name][1], _replay(name)) for name in _PINNED_LOGS])

    def test_a_step_whose_split_fails_is_proved_by_its_other_proofs(self):
        # The file verifies, and it does not with the split as the only proof of its steps:
        # the split attempt fails in Lean and the proofs after it close the steps.
        certificate = _replay_log(_FALLBACK_SOURCE, _FALLBACK_LOG)
        self._verify([("fallback", _FALLBACK_SOURCE, certificate)])
        alone, cut = _split_alone(proof_to_lean.reconstruct(_FALLBACK_SOURCE, certificate))
        self.assertTrue(cut)
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "split_alone.lean"
            output.write_text(alone)
            result = lean_test_support.run_check_lean(output)
            report = result.stdout + result.stderr
            self.assertNotEqual(result.returncode, 0, report)
            errors = [line for line in report.split("\n") if "error:" in line]
            self.assertTrue(errors, report)
            for error in errors:
                self.assertIn("`grind` failed", error)

    def test_pinned_random_instances_verify(self):
        checks = []
        for seed in SIGN_SEEDS:
            source = random_product_instance(seed)
            self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % seed)
            checks.append((seed, source, _export(source)))
        self._verify(checks)

    def test_a_step_that_needs_more_than_the_signs_fails_in_lean(self):
        # The split is an attempt like any other: Lean rejects the file when no proof of the step checks.
        for name, source in NOT_CERTIFIED.items():
            with warnings.catch_warnings():
                # Z3's trimmer rejects the log (the empty clause is a lemma of the nonlinear solver).
                warnings.simplefilter("ignore", RuntimeWarning)
                certificate = _export(source)
            text = proof_to_lean.reconstruct(source, certificate)
            self.assertTrue(_split_steps(text))
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                output = Path(directory) / "outside.lean"
                output.write_text(text)
                result = lean_test_support.run_check_lean(output)
                report = result.stdout + result.stderr
                self.assertNotEqual(result.returncode, 0, report)
                errors = [line for line in report.split("\n") if "error:" in line]
                self.assertTrue(errors, report)
                for error in errors:
                    self.assertIn("`grind` failed", error)


if __name__ == "__main__":
    unittest.main()
