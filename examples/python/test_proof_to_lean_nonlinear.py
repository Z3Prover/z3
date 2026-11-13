############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Tests for products of Int terms in the Lean reconstruction: (* m n) in the
# integer fragments, through the sat.smt clause log and the legacy core.
# A product of two or more nonconstant Int terms is an atom of the linear
# forms, as it is a variable of Z3's simplex solver: the farkas, bound,
# implied-eq, and cut lemmas over products are linear combinations, which
# the exporter and the reconstructor re-derive and Lean proves (its Int * is
# the product, and grind normalizes polynomials, so (* m n) and (* n m) are
# one term there). What Z3's nonlinear solver derives about a product from
# its factors is not certified: a refutation that uses an nla lemma is
# rejected by the exporter, and a clause the solver assumed on nlsat's word
# is tied to the assertions by a lemma Lean has to prove, like any other
# assumed clause. A product of Real terms stays rejected: Real is Rat in
# Lean, which is faithful for linear constraints only.
# Validation without Lean, and end-to-end checks that need the z3 executable
# and the pinned Lean toolchain.
############################################
import copy
from fractions import Fraction
import functools
from pathlib import Path
import random
import sys
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

_INTS = "(declare-const m Int)\n(declare-const n Int)\n(declare-const k Int)\n"
_REALS = "(declare-const x Real)\n(declare-const y Real)\n"
_CHECK = "(check-sat)\n"

# Documented inputs, each unsatisfiable with its products read as variables
# (after Z3's rewriter ordered their factors), with the fragment of each.
PRODUCT_INPUTS = {
    "bounds_on_a_product": ("qf_lia", _INTS + "(assert (> (* m n) 2))\n(assert (< (* m n) 1))\n"),
    "commuted_factors": ("qf_lia", _INTS + "(assert (> (* m n) 2))\n(assert (< (* n m) 1))\n"),
    "scaled_products": ("qf_lia", _INTS + """(assert (<= (+ (* 2 m n) (* 3 m)) 1))
(assert (>= (* n m) 1))
(assert (>= m 0))
"""),
    "three_factors": ("qf_lia", _INTS + "(assert (> (* m n k) 1))\n(assert (< (* k (* n m)) 1))\n"),
    "product_named_by_a_variable": ("qf_lia", _INTS + """(assert (= k (* m n)))
(assert (> k 2))
(assert (< (* m n) 1))
"""),
    "square_between_bounds": ("qf_lia", _INTS + """(assert (>= (* m m) 4))
(assert (<= (+ (* m m) n) 3))
(assert (>= n 0))
"""),
    # Z3's rewriter orders the factors, sums included, so the two products are one term.
    "product_of_sums": ("qf_lia", _INTS + """(assert (> (* (+ m 1) (- n k)) 2))
(assert (< (* (- n k) (+ 1 m)) 1))
"""),
    # The gate of the ite gives (ite p n 1) = n; the two products are then equal by congruence.
    "ite_factor": ("qf_lia", "(declare-const p Bool)\n" + _INTS + """(assert (> (* m (ite p n 1)) 2))
(assert p)
(assert (< (* m n) 1))
"""),
    "abs_factor": ("qf_lia", _INTS + "(assert (> (* m (abs n)) 2))\n(assert (< (* (abs n) m) 1))\n"),
    "product_in_boolean_structure": ("qf_lia", "(declare-const p Bool)\n" + _INTS + """(assert (or p (> (* m n) 3)))
(assert (or (not p) (> (* m n) 4)))
(assert (<= (* 2 (* n m)) 7))
"""),
    # The strict bounds are tightened around the product.
    "tightened_bounds_on_a_product": ("qf_lia", _INTS + """(assert (> (* m n) 2))
(assert (< (* n m) 4))
(assert (not (= (* m n) 3)))
"""),
    # Z3's rewriter splits a product that is zero by its factors, which grind proves with Int.mul_eq_zero.
    "zero_product": ("qf_lia", _INTS + """(assert (= (* m n) 0))
(assert (not (= m 0)))
(assert (not (= n 0)))
"""),
    "zero_product_of_three": ("qf_lia", _INTS + """(assert (= (* m n k) 0))
(assert (not (= m 0)))
(assert (not (= n 0)))
(assert (not (= k 0)))
"""),
    # A gcd conflict over the product: twice an integer is not odd.
    "parity_of_a_product": ("qf_lia", _INTS + "(assert (= (* 2 (* m n)) (+ (* 2 k) 1)))\n"),
    # z3test regressions/smt2/nl40.smt2.
    "product_in_a_linear_system": ("qf_lia", _INTS + """(assert (= (+ (* 11 m) (* 7 n)) 1))
(assert (= n (+ (* m k) (- 1))))
(assert (>= k m))
(assert (= n 0))
"""),
    "mod_of_a_product": ("qf_lia", _INTS + "(assert (= (mod (* m n) 2) 1))\n(assert (= (* n m) (* 2 k)))\n"),
    "div_of_a_product": ("qf_lia", _INTS + "(assert (> (div (* m n) 3) 4))\n(assert (< (* n m) 15))\n"),
    # Z3's rewriter distributes to_real over a product, so the solver's variable is the Real
    # product of (to_real m) and (to_real n), bounded here on both sides (with the Int product
    # next to it the input is PRODUCT_AND_ITS_REAL_IMAGE).
    "to_real_of_a_product": ("qf_lira", "(declare-const x Real)\n" + _INTS + """(assert (> (to_real (* m n)) x))
(assert (> x 2.5))
(assert (< (to_real (* n m)) 2.0))
"""),
    "floor_factor": ("qf_lira", "(declare-const x Real)\n" + _INTS + """(assert (> (* m (to_int x)) 2))
(assert (< (* (to_int x) m) 1))
"""),
    "product_under_a_function": ("qf_uflia", "(declare-fun g (Int) Int)\n" + _INTS + """(assert (> (g (* m n)) 1))
(assert (< (g (* n m)) 0))
"""),
    "product_argument_disequality": ("qf_uflia", "(declare-fun g (Int) Int)\n" + _INTS
                                     + "(assert (not (= (g (* m n)) (g (* n m)))))\n"),
    "function_factor": ("qf_uflia", "(declare-fun g (Int) Int)\n" + _INTS + """(assert (> (* m (g n)) 2))
(assert (= n k))
(assert (< (* (g k) m) 1))
"""),
    "product_over_a_sort": ("qf_uflia", """(declare-sort U 0)
(declare-fun h (U) Int)
(declare-fun a () U)
(declare-fun b () U)
(assert (= a b))
(assert (> (* (h a) (h a)) 3))
(assert (< (* (h b) (h a)) 2))
"""),
    "read_at_a_product": ("qf_uflia", "(declare-const a (Array Int Int))\n" + _INTS
                          + "(assert (not (= (select a (* m n)) (select a (* n m)))))\n"),
    "stored_product": ("qf_uflia", "(declare-const a (Array Int Int))\n" + _INTS
                       + "(assert (> (select (store a k (* m n)) k) 5))\n(assert (< (* m n) 5))\n"),
    "product_of_reads": ("qf_uflia", "(declare-const a (Array Int Int))\n" + _INTS
                         + """(assert (> (* (select a m) (select a n)) 5))
(assert (= m n))
(assert (< (* (select a n) (select a n)) 5))
"""),
}
PRODUCT_INPUTS = {name: (fragment, source + _CHECK) for name, (fragment, source) in PRODUCT_INPUTS.items()}

# Inputs of PRODUCT_INPUTS that also verify through the legacy core's proof
# object. (On others the legacy core's refutation rests on its nonlinear
# solver, th-lemma arith assumed nlsat or unsupported nla, and is rejected:
# LEGACY_NONLINEAR_INPUTS.)
LEGACY_INPUTS = ("bounds_on_a_product", "commuted_factors", "scaled_products", "three_factors", "abs_factor",
                 "tightened_bounds_on_a_product", "zero_product", "parity_of_a_product", "mod_of_a_product",
                 "to_real_of_a_product", "product_under_a_function")
# Inputs of PRODUCT_INPUTS that the legacy core settles with its nonlinear
# solver today, although the simplex solver and congruence would do.
LEGACY_NONLINEAR_INPUTS = ("function_factor", "product_over_a_sort")
_LEGACY_NONLINEAR = "^th-lemma without a replayable theory hint: arith (unsupported nla|assumed nlsat)$"

_REAL_PRODUCT = "^nonlinear multiplication is supported over Int only: a product of Real terms is not certified$"
_NONLINEAR_LEMMA = "^the refutation uses a lemma of the nonlinear solver, which is not certified: %s$"
# Inputs Z3 refutes that the exporter rejects, each with its message: those
# that rest on what the nonlinear solver knows about a product (a polynomial
# refutation, nla, or a lemma without one, nla-unsupported), products of
# Real terms (Real is Rat in Lean: (= (* x x) 2.0) has a real solution and
# no rational one, so a theorem over Rat would not say the input is
# unsatisfiable), and divisions by a product.
REJECTED_INPUTS = {
    "square_is_two": (_INTS + "(assert (= (* m m) 2))\n", _NONLINEAR_LEMMA % "nla"),
    "substituted_factor": (_INTS + "(assert (> (- (* m n) k) 0))\n(assert (= m 1))\n(assert (= n k))\n",
                           _NONLINEAR_LEMMA % "nla-unsupported"),
    "real_product": (_REALS + "(assert (> (* x y) 2.0))\n(assert (< (* x y) 1.0))\n", _REAL_PRODUCT),
    "real_square": (_REALS + "(assert (< (* x x) 0.0))\n", _REAL_PRODUCT),
    "real_product_under_a_function": ("(declare-fun f (Real) Real)\n" + _REALS
                                      + "(assert (> (f (* x y)) 1.0))\n(assert (< (f (* y x)) 0.0))\n", _REAL_PRODUCT),
    "real_product_of_int_factors": (_INTS + "(assert (> (* (to_real m) (to_real n)) 2.0))\n"
                                    "(assert (< (* m n) 1))\n", _REAL_PRODUCT),
    "real_product_behind_false": (_REALS + "(assert false)\n(assert (> (* x y) 2.0))\n", _REAL_PRODUCT),
    "division_by_a_product": ("(declare-const x Real)\n" + _INTS + "(assert (> (/ x (to_real (* m n))) 1.0))\n"
                              "(assert (< x 0.0))\n", "^division is supported only by a nonzero constant$"),
    "modulus_by_a_product": (_INTS + "(assert (> (mod k (* m n)) 1))\n(assert (< k 0))\n",
                             "^integer mod is supported only by a nonzero constant$"),
    "power": (_INTS + "(assert (< (^ m 2) 0))\n", r"^unsupported arithmetic operator: \*\*$"),
}
REJECTED_INPUTS = {name: (source + _CHECK, message) for name, (source, message) in REJECTED_INPUTS.items()}

# A product next to its image in Real. Z3's rewriter distributes to_real, so
# (* (to_real m) (to_real n)) and (* m n) are two variables of the simplex
# solver, which only the nonlinear solver relates, and Z3 refutes the input
# with lemmas of that solver on the way. Whether it is certified depends on
# the refutation the trimmer keeps: one without such a lemma (today a
# coefficient-free cut over both products, which Lean proves) or one with,
# which is rejected by name. Not a documented input for that reason.
PRODUCT_AND_ITS_REAL_IMAGE = ("(declare-const x Real)\n" + _INTS + "(assert (> (to_real (* m n)) x))\n"
                              "(assert (> x 2.5))\n(assert (< (* n m) 3))\n" + _CHECK)

# Positive factors with a negative product: Z3's nlsat refutes it and the
# log assumes its clause without a hint the replay could check. The replay
# ties an assumed clause to the assertions by a cnf lemma, whatever assumed
# it, so the certificate states (m > 0 and n > 0 and m n < 0) -> false as a
# lemma for Lean, which does not prove it: the input is not certified.
ASSUMED_BY_NLSAT = _INTS + "(assert (> m 0))\n(assert (> n 0))\n(assert (< (* m n) 0))\n" + _CHECK

# A clause log with an nla lemma the refutation does not use (the lemma is
# valid, 0 <= m m; the conflict is linear over the product).
_UNUSED_NLA = "(declare-const m Int)\n(assert (> (* m m) 2))\n(assert (< (* m m) 1))\n" + _CHECK
_UNUSED_NLA_LOG = """\
(declare-fun m () Int)
(define-const $6 Int (* m m))
(define-const $9 Bool (<= $6 2))
(assume (not $9))
(define-const $11 Bool (<= 1 $6))
(assume (not $11))
(define-const $20 Bool (<= 0 $6))
(declare-fun nla (Int Bool Proof) Proof)
(declare-fun |(polynomial-refutation (premises 1))| () Proof)
(define-const $21 Bool (not $20))
(define-const $22 Proof (nla 1 $21 |(polynomial-refutation (premises 1))|))
(infer $20 $22)
(declare-fun farkas (Int Bool Int Bool) Proof)
(define-const $10 Bool (not $9))
(define-const $12 Bool (not $11))
(define-const $16 Proof (farkas 1 $12 1 $10))
(infer $11 $9 $16)
(declare-fun rup () Proof)
(infer rup)
"""
# The log of a negative square with the solver's lemma 0 <= m m under a hint
# of the nonlinear solver (%s), which the refutation uses.
_NEGATIVE_SQUARE = "(declare-const m Int)\n(assert (< (* m m) 0))\n" + _CHECK
_USED_NLA_LOG = """\
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
# The same lemma weakened (0 <= m m or 5 <= m m, hint %s), which the empty
# clause depends on through a farkas step and unit propagation only.
_CHAINED_NLA_LOG = """\
(declare-fun m () Int)
(define-const $6 Int (* m m))
(define-const $9 Bool (<= 0 $6))
(assume (not $9))
(define-const $10 Bool (not $9))
(define-const $14 Proof %s)
(define-const $20 Bool (<= 5 $6))
(infer $9 $20 $14)
(declare-fun farkas (Int Bool Int Bool) Proof)
(define-const $21 Proof (farkas 1 $20 1 $10))
(infer (not $20) $9 $21)
(declare-fun rup () Proof)
(infer $9 rup)
(infer rup)
"""


@functools.lru_cache(maxsize=None)
def _certificate(name):
    """The clause-log certificate of a documented input, exported once for the module.

    Exported where a test asks for it, in the subtest of the input, so that
    an input Z3 comes to refute through its nonlinear solver fails its own
    subtests and not the tests of the others.
    """
    return _export(PRODUCT_INPUTS[name][1])


def random_product_instance(seed, constraints=8):
    """A random problem over products of Int variables, unsatisfiable with the products read as variables, or None.

    Three products of two or three of three variables, each occurrence
    written with its factors in a random order and nesting, enter linear
    atoms with small coefficients next to the variables. The problem is
    kept when its linear abstraction, one fresh variable per product, is
    unsatisfiable: then the input is, and a refutation needs nothing about
    products but that reordering their factors does not change them. (Z3
    may still use its nonlinear solver or its rewriter's sign splits on the
    way; such refutations are not certified.)
    """
    generator = random.Random(seed)
    products = []
    while len(products) < 3:
        product = tuple(sorted(generator.choices(range(3), k=generator.randint(2, 3))))
        if product not in products:
            products.append(product)

    def numeral(value):
        return str(value) if value >= 0 else "(- %d)" % -value

    def written(product):
        factors = ["x%d" % factor for factor in generator.sample(product, len(product))]
        if len(factors) == 3 and generator.random() < 0.5:
            return "(* %s (* %s %s))" % tuple(factors)
        return "(* %s)" % " ".join(factors)

    def atom():
        """A linear atom over variables and products: its text, and the text of its abstraction."""
        texts, abstractions = [], []
        for _ in range(generator.randint(1, 3)):
            coefficient = numeral(generator.choice([-3, -2, -1, 1, 2, 3]))
            if generator.random() < 0.6:
                product = generator.choice(products)
                term, abstraction = written(product), "p%d" % products.index(product)
            else:
                term = abstraction = "x%d" % generator.randrange(3)
            texts.append("(* %s %s)" % (coefficient, term))
            abstractions.append("(* %s %s)" % (coefficient, abstraction))
        relation, bound = generator.choice(["<=", ">=", "<", ">", "="]), numeral(generator.randint(-5, 5))
        return tuple("(%s (+ %s 0) %s)" % (relation, " ".join(summands), bound)
                     for summands in (texts, abstractions))

    assertions = []
    for _ in range(constraints):
        roll = generator.random()
        first, second = atom(), atom()
        pattern = "(or %s %s)" if roll < 0.3 else "(not (and %s %s))" if roll < 0.4 else None
        assertions.append(first if pattern is None else tuple(pattern % pair for pair in zip(first, second)))
    source, abstraction = ("\n".join(["(declare-const %s Int)" % name for name in names]
                                     + ["(assert %s)" % assertion[position] for assertion in assertions]) + "\n"
                           for position, names in ((0, ["x0", "x1", "x2"]),
                                                   (1, ["x0", "x1", "x2", "p0", "p1", "p2"])))
    solver = z3.Solver(ctx=z3.Context())
    solver.from_string(abstraction)
    return source + _CHECK if solver.check() == z3.unsat else None


# Seeds of random_product_instance whose refutations verify. Of the seeds
# 1-300, 86 of the 110 unsatisfiable ones verify; the others rest on the
# nonlinear solver (its lemmas, the bounds it propagates, clauses nlsat
# assumed) or on the rewriter's split of a factored product by the signs of
# its factors, and fail in the exporter or in Lean.
PRODUCT_SEEDS = (3, 11, 20, 33, 44, 62, 164)


# The hint names of the nonlinear solver, in the clause log and in the
# legacy proof object: no certificate holds one.
_UNCERTIFIED_HINTS = set(proof_clause_log._NONLINEAR_HINTS) | {"nlsat-assumed", "nlsat", "unsupported", "assumed"}


def _hints(certificate):
    return {tuple(d["parameters"]) for d in certificate["declarations"] if d["name"] == "th-lemma"}


def _products(graph):
    return [node for node in range(len(graph.nodes)) if proof_to_lean._is_product(graph, node)]


class TestProductValidation(unittest.TestCase):
    """Validation without Lean: the atoms of the linear forms, the hints, and what stays rejected."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")

    def replay(self, source, log):
        context = z3.Context()
        assertions, fragment = proof_certificate.parse_assertions(source, context, integer=True)
        return proof_clause_log.build_certificate(source, fragment, assertions, log, context)

    def test_fragments_and_products(self):
        for name, (fragment, source) in PRODUCT_INPUTS.items():
            with self.subTest(name=name):
                certificate = _certificate(name)
                self.assertEqual(certificate["fragment"], fragment)
                self.assertFalse({hint[0] for hint in _hints(certificate)} & _UNCERTIFIED_HINTS)
                graph = proof_to_lean._validate_graph(source, certificate)
                self.assertTrue(_products(graph))
                self.assertTrue(graph.integer_products)
                text = proof_to_lean.reconstruct(source, certificate)
                self.assertIn("grind (splits := 64) [Int.mul_eq_zero]", text)
                self.assertNotIn("sorry", text)
        # A certificate without a product keeps the tactic it had.
        linear = "(declare-const m Int)\n(assert (> (* 2 m) 3))\n(assert (< (* 3 m) 5))\n" + _CHECK
        certificate = _export(linear)
        self.assertFalse(proof_to_lean._validate_graph(linear, certificate).integer_products)
        self.assertNotIn("Int.mul_eq_zero", proof_to_lean.reconstruct(linear, certificate))

    def test_a_product_is_an_atom_of_the_linear_forms(self):
        m, n, k = z3.Ints("m n k")
        # The term as written is the atom, numeral factors included; a
        # product by numerals alone scales its one nonconstant factor.
        for term, atoms in [(m * n, {(m * n): 1}), (2 * (m * n) + 3 * m, {(m * n): 2, m: 3}),
                            (z3.Product(2, m, n), {z3.Product(2, m, n): 1}), (2 * m * 3, {m: 6}),
                            (m * (n + 1) - m * n, {(m * (n + 1)): 1, (m * n): -1}),
                            (m * n - n * m, {(m * n): 1, (n * m): -1}),
                            (z3.ToReal(m * n) / 2, {(m * n): Fraction(1, 2)})]:
            with self.subTest(term=term):
                terms, constant = proof_clause_log._linear(term)
                self.assertEqual(constant, 0)
                self.assertEqual(terms, {atom.get_id(): coefficient for atom, coefficient in atoms.items()})
        # The combination of two bounds on one product refutes them, the
        # strict bounds tightened (no integer lies between 2 and 3); over
        # two ways of writing the product it does not (Z3's rewriter leaves
        # one), and an integer lemma whose coefficients do not certify it is
        # Lean's alone.
        self.assertTrue(proof_clause_log.check_linear_hint("farkas", [(1, m * n > 2), (1, m * n < 3)]))
        self.assertFalse(proof_clause_log.check_linear_hint("farkas", [(1, m * n > 2), (1, n * m < 3)]))
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "integer div is supported only by"):
            proof_clause_log._linear(k / (m * n))

    def test_linear_lemmas_over_products_keep_their_coefficients(self):
        certificate = _certificate("scaled_products")
        source = PRODUCT_INPUTS["scaled_products"][1]
        farkas = [hint for hint in _hints(certificate) if hint[0] == "farkas"]
        self.assertTrue(farkas and all(len(hint) > 1 for hint in farkas), farkas)
        # The reconstructor re-derives each combination over the product
        # nodes (_check_th_lemma), as it does over variables.
        graph = proof_to_lean._validate_graph(source, certificate)
        lemmas = [node for node in range(len(graph.nodes))
                  if graph.kind(node) == z3.Z3_OP_PR_TH_LEMMA and graph.decl(node).parameters[0] == "farkas"]
        self.assertTrue(lemmas)
        for node in lemmas:
            proof_to_lean._check_th_lemma(graph, node)
            forms = [proof_to_lean._linear_constraint(graph, literal)[1]
                     for literal in graph.clause(graph.conclusion(node))]
            self.assertTrue(any(proof_to_lean._is_product(graph, atom) for terms in forms for atom in terms))

    def test_rejected_inputs(self):
        for name, (source, message) in REJECTED_INPUTS.items():
            with self.subTest(name=name), warnings.catch_warnings():
                # The nonlinear solver's last lemma on square_is_two is the empty clause, a theory
                # axiom without premises, which Z3's trimmer refuses: the replay then reads the
                # untrimmed log, with a warning. Nowhere else is that fallback expected.
                warnings.simplefilter("ignore" if name == "square_is_two" else "error", RuntimeWarning)
                with self.assertRaisesRegex(proof_certificate.ProofExportError, message):
                    _export(source)
        # The reconstructor reads the input itself: no certificate makes a
        # theorem over Rat of a product of Real terms (here the certificate
        # of the same bounds on x, relabelled).
        source = REJECTED_INPUTS["real_product"][0]
        certificate = dict(_export(source.replace("(* x y)", "x")), source_smt2=source)
        with self.assertRaisesRegex(proof_certificate.ProofExportError, _REAL_PRODUCT):
            proof_to_lean.reconstruct(source, certificate)
        # The legacy core's exporter rejects them too.
        for name in ("real_product", "real_square", "real_product_of_int_factors", "division_by_a_product", "power"):
            with self.subTest(core="legacy", name=name):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, REJECTED_INPUTS[name][1]):
                    proof_certificate.export_certificate(REJECTED_INPUTS[name][0])

    def test_the_legacy_core_rejects_steps_of_the_nonlinear_solver(self):
        # The legacy proof object labels what the nonlinear solver derived (_ th-lemma arith
        # unsupported nla) and what nlsat decided (_ th-lemma arith assumed nlsat); neither is a
        # replayable hint (the labels alone: test_proof_certificate.py,
        # test_legacy_unsupported_conflicts_are_left_to_lean_over_int). No square is 2 and no
        # linear fact says so: every refutation of this input has such a step.
        with self.assertRaisesRegex(proof_certificate.ProofExportError, _LEGACY_NONLINEAR):
            proof_certificate.export_certificate(REJECTED_INPUTS["square_is_two"][0])
        # These the legacy core settles with its nonlinear solver today, although it need not: a
        # refutation with such a step is rejected by its label, one without is exported (and
        # checked by Lean like any other), and nothing else may happen.
        sources = {name: PRODUCT_INPUTS[name][1] for name in LEGACY_NONLINEAR_INPUTS}
        sources["product_and_its_real_image"] = PRODUCT_AND_ITS_REAL_IMAGE
        for name, source in sources.items():
            with self.subTest(name=name):
                try:
                    certificate = proof_certificate.export_certificate(source)
                except proof_certificate.ProofExportError as error:
                    self.assertRegex(str(error), _LEGACY_NONLINEAR)
                else:
                    self.assertFalse({hint[0] for hint in _hints(certificate)} & _UNCERTIFIED_HINTS)

    def test_a_product_and_its_real_image_are_related_by_the_nonlinear_solver_alone(self):
        source = PRODUCT_AND_ITS_REAL_IMAGE
        try:
            certificate = _export(source)
        except proof_certificate.ProofExportError as error:
            self.assertRegex(str(error), _NONLINEAR_LEMMA % "nla(-unsupported)?")
            return
        # Exported, it holds no lemma of the nonlinear solver, and Lean has to prove what
        # relates the two products, nodes of two sorts.
        self.assertEqual(certificate["fragment"], "qf_lira")
        self.assertFalse({hint[0] for hint in _hints(certificate)} & _UNCERTIFIED_HINTS)
        graph = proof_to_lean._validate_graph(source, certificate)
        self.assertEqual({graph.decl(node).range for node in _products(graph)}, {"Int", "Real"})
        self.assertNotIn("sorry", proof_to_lean.reconstruct(source, certificate))

    def test_a_lemma_of_the_nonlinear_solver_is_rejected_when_used(self):
        # Unused, the lemma is left out of the certificate.
        certificate = self.replay(_UNUSED_NLA, _UNUSED_NLA_LOG)
        self.assertEqual({hint[0] for hint in _hints(certificate)}, {"farkas"})
        proof_to_lean.reconstruct(_UNUSED_NLA, certificate)
        # Used, it rejects the refutation, whichever way the hint is logged:
        # with a polynomial refutation, with literals alone, or by its name.
        for name, hint in [("nla", "(nla 1 $10 |(polynomial-refutation (premises 1))|)"),
                           ("nla-unsupported", "(nla-unsupported 1 $10)"), ("nla-unsupported", "nla-unsupported")]:
            with self.subTest(hint=hint):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, _NONLINEAR_LEMMA % name):
                    self.replay(_NEGATIVE_SQUARE, _USED_NLA_LOG % hint)
        with self.assertRaisesRegex(proof_certificate.ProofExportError, _NONLINEAR_LEMMA % "nla-unsupported"):
            self.replay(_NEGATIVE_SQUARE, (_USED_NLA_LOG % "nla-unsupported").replace(
                "(infer $9 $14)", "(infer $9 nla-unsupported)"))
        # So does a lemma that is the empty clause itself (the log of square_is_two ends with
        # one), and one the empty clause depends on through other steps only.
        for name in proof_clause_log._NONLINEAR_HINTS:
            for use, log in [("empty clause", (_USED_NLA_LOG % ("(%s 1 $10)" % name)).replace(
                                 "(infer $9 $14)", "(infer $14)")),
                             ("chain", _CHAINED_NLA_LOG % ("(%s 1 $10)" % name))]:
                with self.subTest(name=name, use=use):
                    with self.assertRaisesRegex(proof_certificate.ProofExportError, _NONLINEAR_LEMMA % name):
                        self.replay(_NEGATIVE_SQUARE, log)
        # Any other hint name is still unknown.
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "^unsupported clause-log hint: nlsat$"):
            self.replay(_NEGATIVE_SQUARE, _USED_NLA_LOG % "(nlsat 1 $10)")
        # A certificate that states such a lemma anyway is rejected by the reconstructor.
        tampered = copy.deepcopy(certificate)
        next(d for d in tampered["declarations"] if d["name"] == "th-lemma")["parameters"] = ["nla"]
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "th-lemma without a supported theory hint"):
            proof_to_lean.reconstruct(_UNUSED_NLA, tampered)

    def test_a_clause_assumed_by_nlsat_is_a_lemma_for_lean(self):
        certificate = _export(ASSUMED_BY_NLSAT)
        self.assertIn(("cnf",), _hints(certificate))
        text = proof_to_lean.reconstruct(ASSUMED_BY_NLSAT, certificate)
        self.assertNotIn("sorry", text)
        self.assertEqual(text.count("\ntheorem unsat "), 1)

    def test_pinned_seeds_are_unsatisfiable(self):
        for seed in PRODUCT_SEEDS:
            with self.subTest(seed=seed):
                source = random_product_instance(seed)
                self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % seed)
                certificate = _export(source)
                self.assertEqual(certificate["fragment"], "qf_lia")
                self.assertTrue(_products(proof_to_lean._validate_graph(source, certificate)))


class TestProductLeanIntegration(unittest.TestCase):
    """End-to-end: clause log or legacy proof object, certificate, Lean reconstruction, kernel check."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")

    def test_documented_inputs_verify(self):
        certificates = {}
        for name, (fragment, _) in PRODUCT_INPUTS.items():
            with self.subTest(name=name):
                certificates[name] = _certificate(name)
                self.assertEqual(certificates[name]["fragment"], fragment)
        lean_test_support.prefetch((PRODUCT_INPUTS[name][1], certificate)
                                   for name, certificate in certificates.items())
        for name, certificate in certificates.items():
            with self.subTest(name=name):
                _, report = lean_test_support.check(self, PRODUCT_INPUTS[name][1], certificate)
                self.assertTrue(_STANDARD_AXIOMS in report or "does not depend on any axioms" in report, report)

    def test_documented_inputs_verify_through_the_legacy_core(self):
        certificates = {}
        for name in LEGACY_INPUTS:
            with self.subTest(name=name):
                certificates[name] = proof_certificate.export_certificate(PRODUCT_INPUTS[name][1])
        lean_test_support.prefetch((PRODUCT_INPUTS[name][1], certificate)
                                   for name, certificate in certificates.items())
        for name, certificate in certificates.items():
            with self.subTest(name=name):
                self.assertEqual(certificate["fragment"], PRODUCT_INPUTS[name][0])
                _, report = lean_test_support.check(self, PRODUCT_INPUTS[name][1], certificate)
                self.assertTrue(_STANDARD_AXIOMS in report or "does not depend on any axioms" in report, report)

    def test_pinned_random_instances_verify(self):
        sources = []
        for seed in PRODUCT_SEEDS:
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
