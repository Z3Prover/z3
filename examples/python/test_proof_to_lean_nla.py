############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Tests for what Z3's nonlinear solver derives about products of Int terms,
# in the Lean reconstruction through the sat.smt clause log. A clause that
# holds by what its products denote has a polynomial refutation of its
# literals: the bounds and equalities they deny, the squares of the atoms,
# and products of two of these sum to a negative constant. Z3 looks for one
# as the evidence of an nla lemma (nla_lemma.cpp); the pipeline does not
# read Z3's but finds one again (proof_certificate.polynomial_refutation,
# z3 solving for the multipliers), checks the sum in exact arithmetic, and
# has Lean prove the clause from it: Int.mul_nonneg for each product, a
# case split for each square, and grind's ring normalization for the sum.
# Three kinds of clauses get such a proof: the lemmas of the nonlinear
# solver (hints nla and nla-unsupported), clauses the log assumes on nlsat's
# word, and simplex conflicts over bounds the nonlinear solver propagated
# (logged as cut, or tied to the assertions by a cnf lemma). A lemma
# without a refutation within the search stays rejected when used.
# Validation without Lean, and end-to-end checks that need the z3 executable
# and the pinned Lean toolchain.
############################################
import copy
from fractions import Fraction
import functools
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock
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
from test_proof_to_lean_nonlinear import (
    ASSUMED_BY_NLSAT, SQUARE_IS_TWO, _NONLINEAR_LEMMA, _UNCERTIFIED_HINTS, _hints, random_product_instance)

_INTS = "(declare-const m Int)\n(declare-const n Int)\n(declare-const k Int)\n"
_CHECK = "(check-sat)\n"

# Documented inputs, each unsatisfiable by what a product is of, with the
# fragment of each. None was certified before: Z3 refutes them with a lemma
# of its nonlinear solver (the first group; three are z3test's nl10, nl32,
# and nl36), with a conflict nlsat found (the second), or with a simplex
# conflict over a bound that solver propagated (the third).
NLA_INPUTS = {
    "factor_equal_to_one": ("qf_lia", _INTS + """(assert (<= (+ (* m n) k) 5))
(assert (= m 1))
(assert (>= n 2))
(assert (>= k 4))
"""),
    "substituted_factor": ("qf_lia", _INTS + "(assert (> (- (* m n) k) 0))\n(assert (= m 1))\n(assert (= n k))\n"),
    "product_above_its_factor": ("qf_lia", _INTS + """(assert (<= 0 m))
(assert (< m n))
(assert (not (<= (+ m 1) (+ (* m n) n))))
"""),
    "factored_sum": ("qf_lia", _INTS + "(assert (<= 0 m))\n(assert (<= (- 1) n))\n(assert (< (+ (* m n) m) 0))\n"),
    "square_below_its_root": ("qf_lia", _INTS + "(assert (>= m 2))\n(assert (< (* m m) (* 2 m)))\n"),
    "square_is_one": ("qf_lia", _INTS + "(assert (= (* m m) 1))\n(assert (> m 1))\n"),
    "difference_of_squares": ("qf_lia", _INTS + """(assert (> m n))
(assert (>= n 0))
(assert (<= (* m m) (* n n)))
"""),
    "positive_factors": ("qf_lia", ASSUMED_BY_NLSAT[:-len(_CHECK)]),
    "bounded_factors": ("qf_lia", _INTS + "(assert (>= m 2))\n(assert (>= n 3))\n(assert (< (* m n) 6))\n"),
    "three_positive_factors": ("qf_lia", _INTS + """(assert (> m 0))
(assert (> n 0))
(assert (> k 0))
(assert (< (* m n k) 1))
"""),
    "cube_below_one": ("qf_lia", _INTS + "(assert (> m 1))\n(assert (< (* m m m) 1))\n"),
    "function_factors": ("qf_uflia", "(declare-fun f (Int) Int)\n" + _INTS + """(assert (>= (f m) 2))
(assert (>= (f n) 3))
(assert (< (* (f m) (f n)) 6))
"""),
    "array_factor": ("qf_uflia", "(declare-const a (Array Int Int))\n" + _INTS + """(assert (>= (select a m) 2))
(assert (>= n 3))
(assert (< (* n (select a m)) 6))
"""),
    "bounded_factors_next_to_a_real": ("qf_lira", "(declare-const x Real)\n" + _INTS + """(assert (> x 0.5))
(assert (>= m 2))
(assert (>= n 3))
(assert (< (* m n) 6))
"""),
    "negative_square": ("qf_lia", _INTS + "(assert (< (* m m) 0))\n"),
    "ite_factor": ("qf_lia", _INTS + """(assert (>= (ite (> k 0) m n) 2))
(assert (>= k 3))
(assert (< (* k (ite (> k 0) m n)) 6))
"""),
    "mod_factor": ("qf_lia", _INTS + "(assert (>= m 3))\n(assert (< (* m (mod n 4)) 0))\n"),
    "product_in_a_clause": ("qf_lia", _INTS + """(assert (>= m 2))
(assert (>= n 3))
(assert (or (< (* m n) 6) (< (* n m) 5)))
"""),
}
NLA_INPUTS = {name: (fragment, source + _CHECK) for name, (fragment, source) in NLA_INPUTS.items()}

# Inputs Z3 refutes with its nonlinear solver that stay outside, each with
# what happens: the th-lemma hints of its certificate and the number of
# lemmas with a polynomial proof. Both are exported, and Lean rejects both.
# A square of a sum is no product of two facts of the lemma nor the square
# of an atom: Z3's rewriter settles the input, in a rewrite Lean does not
# prove. That no square is 2 needs the integers: the nonlinear solver's own
# lemma has a refutation, and the clause the log assumes ((* m m) = 2
# implies m <= -2, which lost the literals nlsat split on) is tied to the
# assertion by a cnf lemma that has none.
NOT_CERTIFIED = {
    "square_of_a_sum": (_INTS + "(assert (< (+ (* m m) (* 2 m n) (* n n)) 0))\n" + _CHECK, set(), 0),
    "square_is_two": (SQUARE_IS_TWO, {"cnf", "nla"}, 1),
}

# Seeds of test_proof_to_lean_nonlinear.random_product_instance that failed
# in Lean before (a cut, a bound, or an assumed clause over products) and
# verify with the polynomial refutations: of the seeds 1-600, 194 of the 235
# unsatisfiable ones verify (182 before).
NLA_SEEDS = (67, 93, 177, 369, 529)

# The log of a negative square with the solver's lemma 0 <= m m under a hint
# of the nonlinear solver (%s): the logged clause is the lemma.
_NEGATIVE_SQUARE = "(declare-const m Int)\n(assert (< (* m m) 0))\n" + _CHECK
_SQUARE_LOG = """\
(declare-fun m () Int)
(define-const $6 Int (* m m))
(define-const $9 Bool (<= 0 $6))
(assume (not $9))
(declare-fun |(polynomial-refutation (premises 1))| () Proof)
(define-const $10 Bool (not $9))
(define-const $14 Proof %s)
(infer $9 $14)
(declare-fun rup () Proof)
(infer rup)
"""
# The log of factor_equal_to_one. The lemma denies the four literals of the
# hint (the equality twice, as its two bounds, and written the other way
# round than in the clause), of which the logged clause kept the one that
# is not false at the base level.
_FACTOR_LOG = """\
(declare-fun k () Int)
(declare-fun n () Int)
(declare-fun m () Int)
(define-const $7 Int (* m n))
(define-const $9 Int (+ $7 k))
(define-const $11 Bool (<= $9 5))
(assume $11)
(define-const $13 Bool (= m 1))
(assume $13)
(define-const $15 Bool (>= n 2))
(assume $15)
(define-const $17 Bool (>= k 4))
(assume $17)
(define-const $21 Bool (= 1 m))
(declare-fun nla (Int Bool Int Bool Int Bool Int Bool Int Bool Proof) Proof)
(declare-fun |(polynomial-refutation (premises 7))| () Proof)
(define-const $23 Proof (nla 1 $13 1 $13 1 $11 1 $15 1 $17 |(polynomial-refutation (premises 7))|))
(infer (not $21) $23)
(declare-fun euf (Bool Bool) Proof)
(define-const $24 Bool (not $21))
(define-const $25 Proof (euf $24 $13))
(infer (not $13) $21 $25)
(declare-fun rup () Proof)
(infer $21 rup)
(infer rup)
"""
# The same log as Z3's trimmer leaves it: the logged clause is an axiom
# there, so the unit clauses the lemma rests on are gone.
_TRIMMED_FACTOR_LOG = """\
(declare-fun m () Int)
(declare-fun deps (Int) Proof)
(define-const $30 Bool (= m 1))
(define-const $42 Proof (deps 1))
(declare-fun nla (Int Bool Int Bool Int Bool Int Bool Int Bool Proof) Proof)
(declare-fun |(polynomial-refutation (premises 7))| () Proof)
(declare-fun k () Int)
(declare-fun n () Int)
(define-const $35 Bool (= 1 m))
(define-const $34 Bool (>= k 4))
(define-const $32 Bool (>= n 2))
(define-const $24 Int (* m n))
(define-const $26 Int (+ $24 k))
(define-const $28 Bool (<= $26 5))
(define-const $37 Proof (nla 1 $30 1 $30 1 $28 1 $32 1 $34 |(polynomial-refutation (premises 7))|))
(define-const $43 Proof (deps 4))
(declare-fun euf (Bool Bool) Proof)
(define-const $38 Bool (not $35))
(define-const $39 Proof (euf $38 $30))
(define-const $44 Proof (deps 5))
(declare-fun rup () Proof)
(declare-fun deps (Int Int Int Int) Proof)
(define-const $46 Proof (deps 7 1 5 4))
(assume $30 $42)
(infer (not $30) $35 $39 $44)
(infer (not $35) $37 $43)
(infer rup $46)
"""
# A clause the log assumes on nlsat's word, which no assertion states: a
# square that is 1 has a root of magnitude at least 1.
_ASSUMED_SQUARE = "(declare-const m Int)\n(assert (= (* m m) 1))\n(assert (> m 1))\n" + _CHECK
_ASSUMED_LOG = """\
(declare-fun m () Int)
(define-const $6 Int (* m m))
(define-const $8 Bool (= $6 1))
(assume $8)
(define-const $10 Bool (<= m 1))
(assume (not $10))
(define-const $12 Bool (<= m (- 1)))
(define-const $13 Bool (>= m 1))
(assume (not $8) $12 $13)
(define-const $14 Bool (<= 2 m))
(assume (not $8) (not $14))
(declare-fun farkas (Int Bool Int Bool) Proof)
(define-const $11 Bool (not $10))
(define-const $15 Bool (not $14))
(define-const $16 Proof (farkas 1 $11 1 $15))
(infer $10 $14 $16)
(declare-fun rup () Proof)
(infer rup)
"""


@functools.lru_cache(maxsize=None)
def _certificate(name):
    """The clause-log certificate of a documented input, exported once for the module."""
    with warnings.catch_warnings():
        # Expected where the trimmed log lacks the unit clauses under a lemma (factor_equal_to_one);
        # test_a_lemma_the_logged_clause_lost_literals_of pins the fallback and its warning.
        warnings.filterwarnings("ignore", "replaying the untrimmed log", RuntimeWarning)
        return _export(NLA_INPUTS[name][1])


def _not_certified(name):
    """The certificate of an input that stays outside, as the exporter writes it: none is rejected there."""
    source, _, _ = NOT_CERTIFIED[name]
    with warnings.catch_warnings():
        # The nonlinear solver's last lemma on square_is_two is the empty clause, a theory axiom
        # without premises, which Z3's trimmer refuses: the replay then reads the untrimmed log,
        # with a warning. Nowhere else is a fallback expected.
        warnings.simplefilter("ignore" if name == "square_is_two" else "error", RuntimeWarning)
        return _export(source)


def _product_proofs(text):
    """The number of lemmas in a Lean certificate with a proof by a polynomial refutation."""
    return text.count("\n    | (have _sum : ")


def _derived(facts, derivation):
    """(equality, polynomial) of a derivation of proof_certificate.polynomial_refutation over facts."""
    if derivation[0] == "fact":
        return facts[derivation[1]]
    if derivation[0] == "atom":
        return None, {(derivation[1],): Fraction(1)}
    if derivation[0] == "square":
        return False, {(derivation[1], derivation[1]): Fraction(1)}
    (left_equality, left), (right_equality, right) = (_derived(facts, part) for part in derivation[1:])
    # An atom is no fact: it may only multiply an equality.
    assert (left_equality or right_equality) or None not in (left_equality, right_equality), derivation
    return bool(left_equality or right_equality), proof_certificate.multiply_polynomials(left, right)


class TestPolynomialRefutation(unittest.TestCase):
    """The search for a polynomial refutation, without z3's executable and without Lean."""

    def refuted(self, facts):
        """Check a refutation of facts the way its users rely on it, and return it."""
        refutation = proof_certificate.polynomial_refutation(facts)
        self.assertIsNotNone(refutation)
        total = {}
        for multiplier, derivation in refutation:
            equality, polynomial = _derived(facts, derivation)
            self.assertTrue(multiplier > 0 or (equality and multiplier != 0), (multiplier, derivation))
            for monomial, value in polynomial.items():
                total[monomial] = total.get(monomial, 0) + multiplier * value
        self.assertEqual({monomial: value for monomial, value in total.items() if value}, {(): -1})
        return refutation

    def test_polynomials(self):
        multiply = proof_certificate.multiply_polynomials
        # (m - 2) (n - 3), with m = 0 and n = 1 the atoms.
        self.assertEqual(multiply({(0,): 1, (): -2}, {(1,): 1, (): -3}), {(0, 1): 1, (0,): -3, (1,): -2, (): 6})
        self.assertEqual(multiply({(0,): 1, (1,): 1}, {(0,): 1, (1,): -1}), {(0, 0): 1, (1, 1): -1})
        self.assertEqual(multiply({(1,): 2}, {}), {})

        # The linear form 3 p - m + 1 over the product atom p = (2 m + 1) (n - 2) of the atoms m, n.
        def factors(atom):
            return [({0: Fraction(2)}, Fraction(1)), ({1: Fraction(1)}, Fraction(-2))] if atom == 7 else None

        self.assertEqual(proof_certificate.expand_polynomial({7: Fraction(3), 0: Fraction(-1)}, Fraction(1), factors),
                         {(0, 1): 6, (0,): -13, (1,): 3, (): -5})
        self.assertEqual(proof_certificate.expand_polynomial({0: Fraction(1), 1: Fraction(0)}, Fraction(0), factors),
                         {(0,): 1})

        # A product of sums with more monomials than Z3's own search keeps is rejected.
        def wide(atom):
            return [({index: Fraction(1) for index in range(40)}, Fraction(1))] * 2 if atom == 99 else None

        with self.assertRaisesRegex(proof_certificate.ProofExportError, "a product of more than 512 monomials"):
            proof_certificate.expand_polynomial({99: Fraction(1)}, Fraction(0), wide)

    def test_refutations(self):
        m, n, k = 0, 1, 2
        one = Fraction(1)
        # m >= 2, n >= 3, m n <= 5: the product of the first two.
        refutation = self.refuted([(False, {(m,): one, (): -2 * one}), (False, {(n,): one, (): -3 * one}),
                                   (False, {(m, n): -one, (): 5 * one})])
        self.assertIn(("product", ("fact", 0), ("fact", 1)), [derivation for _, derivation in refutation])
        # m m <= -1: the square of the atom.
        refutation = self.refuted([(False, {(m, m): -one, (): -one})])
        self.assertIn(("square", m), [derivation for _, derivation in refutation])
        # m = 1, m n + k <= 5, n >= 2, k >= 4: the equality times the atom n.
        refutation = self.refuted([(True, {(m,): one, (): -one}), (False, {(m, n): -one, (k,): -one, (): 5 * one}),
                                   (False, {(n,): one, (): -2 * one}), (False, {(k,): one, (): -4 * one})])
        self.assertIn(("product", ("fact", 0), ("atom", n)), [derivation for _, derivation in refutation])
        # An equality's multiplier may be negative: m m = 1 and m >= 2, whichever way the equality is written.
        for sign in (1, -1):
            self.refuted([(True, {(m, m): sign * one, (): -sign * one}), (False, {(m,): one, (): -2 * one})])
        # Degree three: m >= 2 and m m m <= 0 need a product of degree three.
        facts = [(False, {(m,): one, (): -2 * one}), (False, {(m, m, m): -one})]
        refutation = self.refuted(facts)
        self.assertTrue(any(derivation[0] == "product" and max(map(len, _derived(facts, derivation)[1])) == 3
                            for _, derivation in refutation), refutation)

    def test_facts_without_a_refutation(self):
        m, n = 0, 1
        one = Fraction(1)
        for name, facts in [
                # Satisfiable: m >= 0, n >= 0, m n >= 1.
                ("satisfiable", [(False, {(m,): one}), (False, {(n,): one}), (False, {(m, n): one, (): -one})]),
                # Linear facts are the linear checks' business, contradictory or not.
                ("linear", [(False, {(m,): one, (): -one}), (False, {(m,): -one})]),
                ("none", []),
                # Unsatisfiable over the integers only: m m = 2 with -1 <= m.
                ("integers", [(True, {(m, m): one, (): -2 * one}), (False, {(m,): one, (): one})]),
                # (m + n)^2 <= -1: the square of a sum is not among the products.
                ("square of a sum", [(False, {(m, m): -one, (m, n): -2 * one, (n, n): -one, (): -one})]),
                # m = -1 as two bounds is no equality to multiply n by: m n + n >= 1.
                ("two bounds", [(False, {(m,): one, (): one}), (False, {(m,): -one, (): -one}),
                                (False, {(m, n): one, (n,): one, (): -one})])]:
            with self.subTest(name=name):
                self.assertIsNone(proof_certificate.polynomial_refutation(facts))

    def test_facts_of_a_clause(self):
        m, n = z3.Ints("m n")
        x = z3.Real("x")
        # The facts hold when every literal is false: a strict bound is
        # tightened, a denied disequality is an equality, and the products
        # are multiplied out over the atoms that are none.
        facts = proof_clause_log.polynomial_facts([z3.Not(m >= 2), n < 3, z3.Not((m + 1) * n == m * n + 5)])
        self.assertEqual(facts, [(False, {(m.get_id(),): 1, (): -2}), (False, {(n.get_id(),): 1, (): -3}),
                                 (True, {(n.get_id(),): -1, (): 5})])
        self.assertEqual(proof_clause_log.polynomial_facts([z3.Not(m * n * 2 <= 5)]),
                         [(False, {tuple(sorted((m.get_id(), n.get_id()))): -2, (): 5})])
        # No facts: an equality's complement, a Real bound, a Boolean literal, a division by a term.
        for literals in ([m * n == 1], [x * x < 0], [z3.Bool("p")], [z3.Not(m >= 2), m / n > 1]):
            with self.subTest(literals=literals):
                self.assertIsNone(proof_clause_log.polynomial_facts(literals))


class TestNonlinearLemmaValidation(unittest.TestCase):
    """Validation without Lean: the replay of the hints, the certificates, and what stays rejected."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")

    def replay(self, source, log):
        context = z3.Context()
        assertions, fragment = proof_certificate.parse_assertions(source, context, integer=True)
        return proof_clause_log.build_certificate(source, fragment, assertions, log, context)

    def test_documented_inputs_have_polynomial_proofs(self):
        for name, (fragment, source) in NLA_INPUTS.items():
            with self.subTest(name=name):
                certificate = _certificate(name)
                self.assertEqual(certificate["fragment"], fragment)
                self.assertFalse({hint[0] for hint in _hints(certificate)} & (_UNCERTIFIED_HINTS - {"nla"}))
                text = proof_to_lean.reconstruct(source, certificate)
                self.assertTrue(_product_proofs(text), "no lemma of %s is proved by a polynomial refutation" % name)
                self.assertNotIn("sorry", text)

    def test_a_lemma_with_a_polynomial_refutation_is_certified(self):
        # Whichever way the hint is logged: with Z3's polynomial refutation (not read), with
        # literals alone, or by its name.
        for hint in ("(nla 1 $10 |(polynomial-refutation (premises 1))|)", "(nla-unsupported 1 $10)",
                     "nla-unsupported", "nla"):
            with self.subTest(hint=hint):
                log = _SQUARE_LOG % hint if hint.startswith("(") else (_SQUARE_LOG % "(nla 1 $10)").replace(
                    "(infer $9 $14)", "(infer $9 %s)" % hint)
                certificate = self.replay(_NEGATIVE_SQUARE, log)
                self.assertEqual(_hints(certificate), {("nla",)})
                text = proof_to_lean.reconstruct(_NEGATIVE_SQUARE, certificate)
                self.assertEqual(_product_proofs(text), 1)
                self.assertIn("Int.mul_nonneg_of_nonpos_of_nonpos", text)  # the square of the atom
        # The reconstructor finds the refutation itself: the certificate holds the name alone.
        graph = proof_to_lean._validate_graph(_NEGATIVE_SQUARE, certificate)
        lemma = next(node for node in range(len(graph.nodes)) if graph.kind(node) == z3.Z3_OP_PR_TH_LEMMA)
        self.assertEqual(graph.decl(lemma).parameters, ("nla",))
        proof_to_lean._check_th_lemma(graph, lemma)
        _, bounds, refutation = proof_to_lean._polynomial_certificate(graph, lemma)
        self.assertEqual(len(bounds), 1)
        self.assertTrue(refutation)

    def test_a_lemma_the_logged_clause_lost_literals_of(self):
        source = NLA_INPUTS["factor_equal_to_one"][1]
        certificate = self.replay(source, _FACTOR_LOG)
        self.assertIn(("nla",), _hints(certificate))
        graph = proof_to_lean._validate_graph(source, certificate)
        lemma = next(node for node in range(len(graph.nodes)) if graph.kind(node) == z3.Z3_OP_PR_TH_LEMMA
                     and graph.decl(node).parameters == ("nla",))
        # The lemma has the hint's four literals, the equality once and as the clause writes it.
        self.assertEqual(len(graph.clause(graph.conclusion(lemma))), 4)
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertEqual(_product_proofs(text), 1)
        self.assertIn("Int.mul_eq_zero.mpr", text)  # the equality times a factor
        # Z3's trimmer drops the unit clauses the lemma rests on: the replay of the trimmed log
        # alone asks for the untrimmed one, by an error that says so.
        with self.assertRaisesRegex(proof_clause_log.TrimmedAwayError,
                                    "^the trimmed log lacks the unit clauses under a lemma of the nonlinear "
                                    r"solver \(the untrimmed log has them\): inferred clause is not derivable"):
            self.replay(source, _TRIMMED_FACTOR_LOG)
        # trim_clause_log returns the trimmed text with the log it was cut from, which
        # build_certificate then replays, with a warning: every caller that trims and replays
        # gets the certificate of the untrimmed log.
        trimmed = proof_clause_log.TrimmedLog(_TRIMMED_FACTOR_LOG, _FACTOR_LOG)
        self.assertEqual(trimmed, _TRIMMED_FACTOR_LOG)
        with self.assertWarnsRegex(RuntimeWarning, "^replaying the untrimmed log: the trimmed log lacks"):
            self.assertEqual(self.replay(source, trimmed), certificate)
        # Both replays share one time limit: the second does not start a new one.
        with warnings.catch_warnings(), mock.patch.object(
                proof_clause_log._Replay, "run", autospec=True, side_effect=self.deadlines(trimmed)):
            warnings.simplefilter("ignore", RuntimeWarning)
            self.replay(source, trimmed)
        self.assertEqual(len(self.seen_deadlines), 2)
        self.assertEqual(self.seen_deadlines[0], self.seen_deadlines[1])
        # An untrimmed log without the unit clauses either leaves the lemma uncertified.
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", RuntimeWarning)
            with self.assertRaisesRegex(proof_certificate.ProofExportError, _NONLINEAR_LEMMA % "nla"):
                self.replay(source, proof_clause_log.TrimmedLog(
                    _TRIMMED_FACTOR_LOG, _FACTOR_LOG.replace("(assume $15)\n", "")))
        # The documented input takes this path through the exporter, or needs no fallback.
        self.assertEqual({hint[0] for hint in _hints(_certificate("factor_equal_to_one"))} & {"nla"}, {"nla"})

    def deadlines(self, trimmed):
        """A stand-in for _Replay.run that records each replay's deadline and fails the trimmed one."""
        self.seen_deadlines = []

        def run(replay, text):
            self.seen_deadlines.append(replay.deadline)
            if text is trimmed:
                raise proof_clause_log.TrimmedAwayError("trimmed away")
            return {}

        return run

    def test_a_clause_assumed_by_nlsat_with_a_polynomial_refutation_is_a_lemma(self):
        certificate = self.replay(_ASSUMED_SQUARE, _ASSUMED_LOG)
        # The assumed clauses are theorems about the square: nothing ties them to an
        # assertion. The refutation uses the second; the first is left out.
        self.assertEqual({hint[0] for hint in _hints(certificate)}, {"nla", "farkas"})
        self.assertEqual(certificate["rule_counts"]["th-lemma"], 2)
        self.assertEqual(_product_proofs(proof_to_lean.reconstruct(_ASSUMED_SQUARE, certificate)), 1)
        # An assumed clause that is an assertion stays one.
        self.assertEqual(certificate["rule_counts"]["asserted"], 2)

    def test_inputs_outside_the_search_get_no_proof_of_the_step_that_is(self):
        # Exported: the refutation holds no lemma of the nonlinear solver without a polynomial
        # refutation. The step outside the search (a rewrite, a cnf lemma) gets no polynomial
        # proof and no sorry: it is Lean's to prove, and Lean does not
        # (test_inputs_outside_the_search_fail_in_lean).
        for name, (source, hints, proofs) in NOT_CERTIFIED.items():
            with self.subTest(name=name):
                certificate = _not_certified(name)
                self.assertEqual({hint[0] for hint in _hints(certificate)}, hints)
                text = proof_to_lean.reconstruct(source, certificate)
                self.assertEqual(_product_proofs(text), proofs)
                self.assertNotIn("sorry", text)
        # A lemma of the nonlinear solver without a refutation, used, is rejected by the exporter:
        # test_proof_to_lean_nonlinear (equality_as_two_bounds, and the pinned logs over the
        # square of a sum).

    def test_tampered_lemmas_are_rejected(self):
        source = NLA_INPUTS["square_below_its_root"][1]
        certificate = _certificate("square_below_its_root")
        self.assertIn(("nla",), _hints(certificate))
        nodes, declarations = certificate["nodes"], certificate["declarations"]
        lemma = next(position for position, node in enumerate(nodes)
                     if declarations[node["declaration"]]["parameters"] == ["nla"])
        clause = nodes[lemma]["arguments"][-1]
        # The clause weakened to one of its literals has no refutation.
        tampered = copy.deepcopy(certificate)
        tampered["nodes"][lemma]["arguments"] = [nodes[clause]["arguments"][0]]
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError,
                                    "^nla th-lemma without a polynomial refutation of its literals at node %d$"
                                    % lemma):
            proof_to_lean.reconstruct(source, tampered)
        # Coefficients, and a hint name of the nonlinear solver that certifies nothing.
        for parameters, message in [(["nla", "1", "1"], "nla th-lemma takes no coefficients"),
                                    (["nla-unsupported"], "th-lemma without a supported theory hint"),
                                    (["nlsat-assumed"], "th-lemma without a supported theory hint")]:
            tampered = copy.deepcopy(certificate)
            tampered["declarations"][nodes[lemma]["declaration"]]["parameters"] = parameters
            with self.subTest(parameters=parameters), self.assertRaisesRegex(
                    proof_to_lean.ReconstructionError, message):
                proof_to_lean.reconstruct(source, tampered)

    def test_pinned_seeds_are_unsatisfiable(self):
        for seed in NLA_SEEDS:
            with self.subTest(seed=seed):
                source = random_product_instance(seed)
                self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % seed)
                self.assertTrue(_product_proofs(proof_to_lean.reconstruct(source, _export(source))))


class TestNonlinearLemmaLeanIntegration(unittest.TestCase):
    """End-to-end: clause log, certificate, Lean reconstruction, kernel check."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")

    def test_documented_inputs_verify(self):
        certificates = {}
        for name, (fragment, _) in NLA_INPUTS.items():
            with self.subTest(name=name):
                certificates[name] = _certificate(name)
                self.assertEqual(certificates[name]["fragment"], fragment)
        lean_test_support.prefetch((NLA_INPUTS[name][1], certificate) for name, certificate in certificates.items())
        for name, certificate in certificates.items():
            with self.subTest(name=name):
                _, report = lean_test_support.check(self, NLA_INPUTS[name][1], certificate)
                self.assertTrue(_STANDARD_AXIOMS in report or "does not depend on any axioms" in report, report)

    def test_pinned_logs_verify(self):
        context = z3.Context()
        checks = []
        for source, log in [(_NEGATIVE_SQUARE, _SQUARE_LOG % "(nla 1 $10)"),
                            (NLA_INPUTS["factor_equal_to_one"][1], _FACTOR_LOG), (_ASSUMED_SQUARE, _ASSUMED_LOG)]:
            assertions, fragment = proof_certificate.parse_assertions(source, context, integer=True)
            checks.append((source, proof_clause_log.build_certificate(source, fragment, assertions, log, context)))
        lean_test_support.prefetch(checks)
        for position, (source, certificate) in enumerate(checks):
            with self.subTest(log=position):
                _, report = lean_test_support.check(self, source, certificate)
                self.assertTrue(_STANDARD_AXIOMS in report or "does not depend on any axioms" in report, report)

    def test_inputs_outside_the_search_fail_in_lean(self):
        # Not certified means Lean rejects the file: the step outside the search has no proof,
        # and the proofs of the other steps do not make up for it.
        for name, (source, _, _) in NOT_CERTIFIED.items():
            text = proof_to_lean.reconstruct(source, _not_certified(name))
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

    def test_pinned_random_instances_verify(self):
        sources = []
        for seed in NLA_SEEDS:
            source = random_product_instance(seed)
            self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % seed)
            sources.append((seed, source, _export(source)))
        lean_test_support.prefetch((source, certificate) for _, source, certificate in sources)
        for seed, source, certificate in sources:
            with self.subTest(seed=seed):
                _, report = lean_test_support.check(self, source, certificate)
                self.assertTrue(_STANDARD_AXIOMS in report or "does not depend on any axioms" in report, report)


if __name__ == "__main__":
    unittest.main()
