############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Tests for the QF_UFLRA slice of the Lean reconstruction (uninterpreted
# sorts and functions mixed with linear real arithmetic): validation without
# Lean, and end-to-end checks that need the z3 executable and the pinned
# Lean toolchain.
############################################
import collections
import copy
from fractions import Fraction
import json
from pathlib import Path
import random
import re
import sys
import tempfile
import unittest
from unittest.mock import patch

import z3

_EXAMPLES = Path(__file__).resolve().parent
sys.path.insert(0, str(_EXAMPLES))
import proof_certificate
import proof_clause_log
import lean_test_support
import proof_to_lean
from test_proof_to_lean_uf import _unsat_core_size, _z3_available, outlined_lemma_sizes, _proof_steps
from test_proof_to_lean_arith import _cnf_lemma_attempts

_STANDARD_AXIOMS = "[propext, Classical.choice, Quot.sound]"

# Uninterpreted functions mixed with linear real arithmetic. Each input is
# unsatisfiable and both cores certify all of them.
UFLRA_INPUTS = {
    # Congruence through a Real-valued function, then a Farkas step over the
    # two applications as opaque atoms.
    "uflra_real_function": """\
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-const x Real)
(declare-const y Real)
(assert (= x y))
(assert (< (f x) (f y)))
(check-sat)
""",
    # A function from the sort into Real.
    "uflra_sort_to_real": """\
(set-logic QF_UFLRA)
(declare-sort U 0)
(declare-fun g (U) Real)
(declare-fun h (Real) U)
(declare-const a U)
(declare-const b U)
(declare-const x Real)
(assert (= a b))
(assert (> (g a) (+ (g b) 1.0)))
(check-sat)
""",
    # A function from Real into the sort under a predicate; the equality of
    # the Real arguments is an implied equality of two bounds.
    "uflra_real_to_sort": """\
(set-logic QF_UFLRA)
(declare-sort U 0)
(declare-fun h (Real) U)
(declare-fun p (U) Bool)
(declare-const x Real)
(declare-const y Real)
(assert (<= x y))
(assert (>= x y))
(assert (p (h x)))
(assert (not (p (h y))))
(check-sat)
""",
    # A binary Real function under a disjunction: two congruences, one per case.
    "uflra_binary_split": """\
(set-logic QF_UFLRA)
(declare-fun f (Real Real) Real)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (or (= x y) (= x z)))
(assert (< (f x y) (f y y)))
(assert (< (f x z) (f z z)))
(check-sat)
""",
    # The implied equality x = y feeds the congruence (f x) = (f y), which
    # closes a Farkas combination with the bounds on the applications.
    "uflra_implied_equality": """\
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-const x Real)
(declare-const y Real)
(assert (<= (f x) 0.0))
(assert (>= (f y) 1.0))
(assert (<= (- x y) 0.0))
(assert (>= (- x y) 0.0))
(check-sat)
""",
    # Z3 rewrites the arguments (+ x 0.0) and (* 1.0 y) before logging, so
    # the assumed clauses are bridged to the assertions by rewrites.
    "uflra_rewritten_arguments": """\
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-const x Real)
(declare-const y Real)
(assert (<= (+ (f x) (f y)) 0.0))
(assert (>= (f (+ x 0.0)) 1.0))
(assert (>= (f (* 1.0 y)) 1.0))
(check-sat)
""",
    # A predicate over Real without any sort or Real-valued function still
    # runs the euf solver.
    "uflra_real_predicate": """\
(set-logic QF_UFLRA)
(declare-fun q (Real) Bool)
(declare-const x Real)
(declare-const y Real)
(assert (q x))
(assert (not (q y)))
(assert (<= x y))
(assert (<= y x))
(check-sat)
""",
    # A Real ite inside a function argument; Z3 decides this input before
    # search, so the log is empty and the refutation is one cnf lemma.
    "uflra_ite_argument": """\
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-const x Real)
(declare-const y Real)
(assert (< (f (ite (> x 0.0) x (- x))) (f 1.0)))
(assert (= x 1.0))
(check-sat)
""",
    # Arguments that are equal as linear forms but differ as terms, which
    # grind's congruence closure needs stated explicitly.
    "uflra_normalized_arguments": """\
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun q (Real) Bool)
(declare-const x Real)
(declare-const y Real)
(assert (q (f (- x y))))
(assert (or (not (q (f (+ x (* (- 1.0) y))))) (< (f (+ 2.0 2.0)) 4.0)))
(assert (>= (f 4.0) (f (- x x))))
(assert (= (f 0.0) 4.0))
(assert (>= y 0.0))
(assert (<= x (+ y 1.0)))
(check-sat)
""",
    # The same without the two bounds: y occurs in a single function argument,
    # which the frontend's elim-uncnstr tactic would replace by a fresh constant
    # (the exporters bypass the tactic preamble).
    "uflra_single_occurrence": """\
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun q (Real) Bool)
(declare-const x Real)
(declare-const y Real)
(assert (q (f (- x y))))
(assert (or (not (q (f (+ x (* (- 1.0) y))))) (< (f (+ 2.0 2.0)) 4.0)))
(assert (>= (f 4.0) (f (- x x))))
(assert (= (f 0.0) 4.0))
(check-sat)
""",
    # Real ite terms whose conditions are a Bool variable and a predicate:
    # no linear atom to key them by, so the argument helpers leave them as
    # opaque atoms and grind relates the two through (= p (q x)) alone.
    "uflra_opaque_ite_conditions": """\
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun q (Real) Bool)
(declare-const p Bool)
(declare-const x Real)
(declare-const y Real)
(assert (= (f (ite p x y)) 1.0))
(assert (= (f (ite (q x) x y)) 2.0))
(assert (= p (q x)))
(check-sat)
""",
    # A numeral quotient inside a ground atom next to a conflict at level
    # zero: the sat.smt arithmetic solver logs its division axiom
    # 2 * (1 / 2) = 1 under an arith hint whose first literal is the
    # constant true, which the clause log rejected before.
    "uflra_division_axiom": """\
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (< x x))
(assert (or (< y (f z)) (< (/ 1.0 2.0) 3.0)))
(check-sat)
""",
}

# A predicate over Bool alone applied to Real atoms: QF_UFLRA without a
# sort or a function over Real, so no euf hint mentions a Real term.
BOOL_PREDICATE_WITH_ARITHMETIC = """\
(set-logic QF_UFLRA)
(declare-fun r (Bool) Bool)
(declare-const x Real)
(declare-const y Real)
(assert (r (< x y)))
(assert (not (r (> y x))))
(check-sat)
"""

# Inputs whose single cnf lemma rests on congruence over the rewriter's form
# of the assertion: (ite c (f 0) (f 0)) is logged as (f 0), (+ 0 (f z)) as
# (f z), so the clause's leaves are applications the theory clauses of
# _theory_clauses relate to the assertion's (one per uninterpreted fragment).
THEORY_CLAUSE_INPUTS = {
    "uflra_rewritten_applications": """\
(set-logic QF_UFLRA)
(declare-fun b0 () Bool)
(declare-fun b1 () Bool)
(declare-fun c () Real)
(declare-fun f (Real) Real)
(declare-fun n () Real)
(declare-fun w () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(assert (and (= n (ite (= c 5) 1 (+ c 1)))
             (= w (ite (and (not b0) (not b1)) (f 0) (f 0)))
             (= y (ite (and (not b0) (not b1)) (+ 0 (f z)) 0))
             (or (= c 3) (= c 4))
             (or b0 (not (= w (f 0))) (= n 1) (and (not b1) (not (= y (f z)))))
             (not b0)
             (not b1)))
(check-sat)
""",
    "uflia_rewritten_applications": """\
(set-logic QF_UFLIA)
(declare-fun b0 () Bool)
(declare-fun b1 () Bool)
(declare-fun c () Int)
(declare-fun f (Int) Int)
(declare-fun n () Int)
(declare-fun w () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (and (= n (ite (= c 5) 1 (+ c 1)))
             (= w (ite (and (not b0) (not b1)) (f 0) (f 0)))
             (= y (ite (and (not b0) (not b1)) (+ 0 (f z)) 0))
             (or (= c 3) (= c 4))
             (or b0 (not (= w (f 0))) (= n 1) (and (not b1) (not (= y (f z)))))
             (not b0)
             (not b1)))
(check-sat)
""",
    "uf_ite_over_equal_applications": """\
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun b0 () Bool)
(declare-fun b1 () Bool)
(declare-fun a () U)
(declare-fun e () U)
(declare-fun z () U)
(declare-fun f (U) U)
(declare-fun g (U) U)
(declare-fun n () U)
(declare-fun w () U)
(assert (and (= n (ite (= (f a) e) (f e) (g (f a))))
             (= w (ite (and (not b0) (not b1)) z z))
             (= (f a) e)
             (or b0 (not (= w z)) (not (= n (f e))))
             (not b0)))
(check-sat)
""",
}


def random_instance(seed, variables=4, constraints=10, with_sort=False, depth=2):
    """A random QF_UFLRA instance, or None when it is satisfiable.

    Real variables, a unary and a binary Real function, a predicate over
    Real, and with_sort an uninterpreted sort with constants, functions in
    both directions, and a predicate over it.
    """
    rng = random.Random(seed)
    names = ["x%d" % i for i in range(variables)]
    lines = ["(set-logic QF_UFLRA)"]
    if with_sort:
        lines += ["(declare-sort U 0)", "(declare-fun a () U)", "(declare-fun b () U)",
                  "(declare-fun h (Real) U)", "(declare-fun g (U) Real)", "(declare-fun p (U) Bool)"]
    lines += ["(declare-fun %s () Real)" % n for n in names]
    lines += ["(declare-fun f (Real) Real)", "(declare-fun k (Real Real) Real)", "(declare-fun q (Real) Bool)"]

    def numeral():
        value = rng.choice([0, 1, 2, 3, "(/ 1.0 2.0)", "(/ 3.0 2.0)"])
        return "%d.0" % value if isinstance(value, int) else value

    def term(d=depth):
        choice = rng.random()
        if d == 0 or choice < 0.3:
            return rng.choice(names)
        if choice < 0.45:
            return numeral()
        if choice < 0.6:
            return "(f %s)" % term(d - 1)
        if choice < 0.7:
            return "(k %s %s)" % (term(d - 1), term(d - 1))
        if choice < 0.8 and with_sort:
            return "(g %s)" % uterm(d - 1)
        if choice < 0.9:
            return "(+ %s %s)" % (term(d - 1), term(d - 1))
        return "(- %s %s)" % (term(d - 1), term(d - 1))

    def uterm(d=depth):
        if d == 0 or rng.random() < 0.5:
            return rng.choice(["a", "b"])
        return "(h %s)" % term(d - 1)

    def atom():
        choice = rng.random()
        if choice < 0.5:
            return "(%s %s %s)" % (rng.choice(["<=", "<", "=", ">="]), term(), term())
        if choice < 0.7:
            return "(q %s)" % term()
        if with_sort and choice < 0.85:
            return rng.choice(["(p %s)" % uterm(), "(= %s %s)" % (uterm(), uterm())])
        return "(= %s %s)" % (term(), term())

    def formula():
        choice = rng.random()
        if choice < 0.6:
            return atom()
        if choice < 0.8:
            return "(or %s %s)" % (atom(), atom())
        if choice < 0.9:
            return "(not %s)" % atom()
        return "(=> %s %s)" % (atom(), atom())

    lines += ["(assert %s)" % formula() for _ in range(constraints)]
    lines.append("(check-sat)")
    source = "\n".join(lines) + "\n"
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.add(z3.parse_smt2_string(source, ctx=context))
    return source if solver.check() == z3.unsat else None


# Real abs terms of constants under applications, reads, and floors. Z3's
# rewriter evaluates (abs (- 2.5)) to 2.5, and the step that ties the
# assertion to what the solver saw is then a congruence over the value.
# Lean's abs is the ite (if t >= 0 then t else -t): each abs of a constant
# is stated equal to its value and replaced by it
# (proof_to_lean._abs_value_facts), and counts by its value where arguments
# are compared (proof_to_lean._real_argument_key). On the clause log Lean
# rejected each input marked "failed" (`grind` failed in a rewrite); the
# legacy core's proof evaluates the abs in steps of its own and verified
# them all.
ABS_VALUE_INPUTS = {
    # failed
    "abs_of_a_negative_fraction": """(declare-fun g (Real) Real)
(assert (not (= (g (abs (- 2.5))) (g 2.5))))
""",
    # failed: a rewrite and a theory lemma over the predicate
    "abs_under_a_predicate": """(declare-fun r (Real) Bool)
(assert (r (abs (- 0.5))))
(assert (not (r 0.5)))
""",
    # failed
    "abs_of_a_sum": """(declare-fun g (Real) Real)
(assert (not (= (g (abs (+ 1.5 (- 4.0)))) (g 2.5))))
""",
    # failed
    "abs_of_a_third": """(declare-fun g (Real) Real)
(assert (not (= (g (abs (- (/ 1.0 3.0)))) (g (/ 1.0 3.0)))))
""",
    # failed
    "abs_under_two_functions": """(declare-fun g (Real) Real)
(assert (not (= (g (g (abs (- 2.5)))) (g (g 2.5)))))
""",
    # failed
    "abs_in_two_assertions": """(declare-fun g (Real) Real)
(assert (= (g (abs (- 2.5))) 1.0))
(assert (= (g 2.5) 2.0))
""",
    # failed: the argument is a constant only with the abs counted by its
    # value, and is then related to the numeral the rewriter leaves
    "abs_in_a_sum_of_numerals": """(declare-fun g (Real) Real)
(assert (not (= (g (+ (+ 2.0 (- 3.25)) (abs (- 0.25)))) (g (- 1.0)))))
""",
    # The two arguments have one linear form over x; verified before.
    "abs_next_to_a_variable": """(declare-fun g (Real) Real)
(declare-const x Real)
(assert (not (= (g (+ x (abs (- 0.75)) 0.5)) (g (+ 1.25 x)))))
""",
    # failed: the abs's argument is a constant once x cancels
    "abs_of_cancelling_variables": """(declare-fun g (Real) Real)
(declare-const x Real)
(assert (not (= (g (abs (+ x (- x) (- 2.5)))) (g 2.5))))
""",
    # failed: the outer abs is stated over the inner one's value
    "nested_abs": """(declare-fun g (Real) Real)
(assert (not (= (g (abs (- (abs (- 2.5)) 4.0))) (g 1.5))))
""",
    # failed: (abs (- 0.5)) and (abs (- (/ 1.0 2.0))) are one Lean term;
    # the first one's replacement leaves the goal none for the second,
    # whose replacement then only uses up its own fact
    "one_abs_written_twice": """(declare-fun h (Real Real) Real)
(assert (not (= (h (abs (- 0.5)) (abs (- (/ 1.0 2.0)))) (h 0.5 0.5))))
""",
    # An integer value, which grind reached by evaluating the literals.
    "abs_of_an_integer": """(declare-fun g (Real) Real)
(assert (not (= (g (abs (- 3.0))) (g 3.0))))
""",
}
# The floor of an abs of a constant, in qf_uflira: the floor's value is
# stated over the abs's (proof_to_lean._floor_shift_facts). The first four
# failed.
ABS_FLOOR_INPUTS = {
    "floor_of_an_abs": """(declare-fun f (Int) Int)
(assert (not (= (f (to_int (abs (- 2.5)))) (f 2))))
""",
    "is_int_of_an_abs": """(declare-fun r (Real) Bool)
(assert (r 0.0))
(assert (is_int (abs (- 2.5))))
""",
    # grind did not bound 3/4 - 2 - (if 1/2 >= 0 then 1/2 else -(1/2)).
    "floor_of_a_difference_with_an_abs": """(declare-fun f (Int) Int)
(assert (not (= (f (to_int (- (- 0.75 2.0) (abs 0.5)))) (f (- 2)))))
""",
    # Two floored terms of one value: their floors are equated by an
    # argument helper, proved after the abs is replaced.
    "floors_of_one_value": """(declare-fun f (Int) Int)
(assert (not (= (f (to_int (- (+ (- 1.5) 2.25) (abs 3.25)))) (f (to_int (- (+ 0.0 2.5)))))))
""",
    # Two floored terms that differ by 2 with the abs counted by its value:
    # the fact that relates their floors is stated over that value. Verified
    # before (grind related the floors through the rewriter's normal forms).
    "floors_that_differ_by_an_integer": """(declare-fun f (Int) Int)
(declare-const x Real)
(assert (not (= (f (to_int (+ x (abs (- 2.5))))) (f (+ (to_int (+ x 0.5)) 2)))))
""",
}
# Reads and stores at an abs of a constant (clause log only). The third
# input has no abs: its read is at a numeral expression that the rewriter
# evaluates, next to three more in the arguments around it, and the two
# indices are related as arguments are (proof_to_lean._real_argument_pairs);
# it failed, as did the first (the store verified before). The last, in
# qf_uflira, is floors_of_one_value in a certificate with arrays, where the
# argument helper is stated over the terms written out and makes the
# replacement in its own goal as well; it failed.
ABS_ARRAY_INPUTS = {
    "read_at_an_abs": """(declare-const a (Array Real Real))
(assert (not (= (select a (abs (- 2.5))) (select a 2.5))))
""",
    "store_at_an_abs": """(declare-const a (Array Real Real))
(assert (not (= (select (store a (abs (- 2.5)) 1.0) 2.5) 1.0)))
""",
    "read_at_a_numeral_expression_among_others": """(declare-fun g (Real) Real)
(declare-fun h (Real Real) Real)
(declare-const a (Array Real Real))
(assert (not (= (h (g 2.75) (select a (+ (* 2.0 0.5) (+ (- 0.5) (- 0.75)))))
                (h (* 2.0 (/ 9.0 8.0)) (+ (+ (- 1.75) (- 0.5)) 5.0)))))
(assert (= (h (g 2.75) (select a (- 0.25))) (h 2.25 2.75)))
""",
    "floors_of_one_value_next_to_a_read": """(declare-fun f (Int) Int)
(declare-const a (Array Int Int))
(assert (= (select a 0) 0))
(assert (not (= (f (to_int (- (+ (- 1.5) 2.25) (abs 3.25)))) (f (to_int (- (+ 0.0 2.5)))))))
""",
}


def random_abs_value_instance(seed, variables=2, constraints=6, depth=2, floors=False, arrays=False):
    """A random instance whose applications take Real abs terms of constants as arguments; None unless unsat.

    g : Real -> Real, h : Real Real -> Real, and the predicate r over Real
    are applied to expressions of three values in quarters, written with
    abs, sums, differences, negations, and doubled halves of numerals, alone
    or added to a Real variable. With floors, f : Int -> Int and the
    predicate p over Int take the floors of such terms, and is_int tests
    them; with arrays, an array from Real to Real is read and stored at
    them.
    """
    generator = random.Random(seed)
    lines = ["(declare-fun g (Real) Real)", "(declare-fun h (Real Real) Real)", "(declare-fun r (Real) Bool)"]
    if floors:
        lines += ["(declare-fun f (Int) Int)", "(declare-fun p (Int) Bool)"]
    if arrays:
        lines.append("(declare-const a (Array Real Real))")
    lines += ["(declare-const x%d Real)" % i for i in range(variables)]
    values = [Fraction(generator.randint(-11, 11), 4) for _ in range(3)]

    def numeral(value):
        text = "%d.%s" % (abs(value) // 1, {0: "0", Fraction(1, 4): "25", Fraction(1, 2): "5",
                                            Fraction(3, 4): "75"}[abs(value) % 1])
        return text if value >= 0 else "(- %s)" % text

    def expression(value, depth):
        """A constant expression of the value: a multiple of 1/4, or of 1/8 as a quotient."""
        roll = generator.random()
        if value.denominator > 4:
            return "(/ %s %d.0)" % (numeral(Fraction(value.numerator)), value.denominator)
        if depth == 0 or roll < 0.15:
            return numeral(value)
        if roll < 0.5 and value >= 0:
            return "(abs %s)" % expression(generator.choice([1, -1]) * value, depth - 1)
        if roll < 0.7:
            part = Fraction(generator.randint(-9, 9), 4)
            return "(+ %s %s)" % (expression(part, depth - 1), expression(value - part, depth - 1))
        if roll < 0.8:
            return "(- %s)" % expression(-value, depth - 1)
        if roll < 0.9:
            return "(* 2.0 %s)" % expression(value / 2, depth - 1)
        part = Fraction(generator.randint(-9, 9), 4)
        return "(- %s %s)" % (expression(part, depth - 1), expression(part - value, depth - 1))

    def term():
        roll = generator.random()
        value = generator.choice(values)
        if roll < 0.55:
            return expression(value, depth)
        if roll < 0.7:
            return "(+ x%d %s)" % (generator.randrange(variables), expression(value, depth))
        if roll < 0.8:
            variable = generator.randrange(variables)
            return "(abs (+ x%d %s (- x%d)))" % (variable, expression(value, depth - 1), variable)
        if roll < 0.9:
            return "(g %s)" % expression(value, depth)
        if arrays:
            return "(select a %s)" % expression(value, depth)
        return "x%d" % generator.randrange(variables)

    def atom():
        roll = generator.random()
        if roll < 0.3:
            return "(= (g %s) (g %s))" % (term(), term())
        if roll < 0.55:
            return "(r %s)" % term()
        if roll < 0.65:
            return "(= (h %s %s) (h %s %s))" % (term(), term(), term(), term())
        if roll < 0.75:
            return "(%s %s %s)" % (generator.choice(["<=", "<", "="]), term(), term())
        if floors and roll < 0.85:
            return "(= (f (to_int %s)) (f (to_int %s)))" % (term(), term())
        if floors and roll < 0.92:
            return generator.choice(["(p (to_int %s))", "(is_int %s)"]) % term()
        if arrays and roll < 0.9:
            return "(= (select (store a %s %s) %s) %s)" % (term(), term(), term(), term())
        return "(< (g %s) (g %s))" % (term(), term())

    def literal():
        return atom() if generator.random() < 0.5 else "(not %s)" % atom()

    for _ in range(constraints):
        if generator.random() < 0.3:
            lines.append("(assert (or %s %s))" % (literal(), literal()))
        else:
            lines.append("(assert %s)" % literal())
    lines.append("(check-sat)")
    source = "\n".join(lines) + "\n"
    solver = z3.Solver(ctx=z3.Context())
    solver.set("timeout", 5000)
    solver.from_string(source)
    return source if solver.check() == z3.unsat else None


# Unsatisfiable seeds of random_abs_value_instance that Lean rejected on the
# clause log before the abs terms of constants were replaced by their
# values, by the generator's options: plain, 8 and 28 needing the abs counted
# by its value in an argument's linear form; with floors, 255 two floored
# terms of one value and 292 a floor of a difference with an abs; with
# arrays, 211 and 347 a read at a numeral expression among others, and 111
# the rewrite of an inequality over a variable and (abs 0.5), a step
# without conversions that needs the abs replaced (the other pinned inputs
# without floors verify with the values stated and nothing replaced). Seed
# 219 with arrays verified before (grind split the abs and then identified
# the read's index with its value; with the abs written as the numeral 2.75
# it did not).
ABS_VALUE_SEEDS = (({}, (8, 17, 28)), ({"floors": True}, (255, 292)), ({"arrays": True}, (111, 211, 219, 347)))


def _th_lemma_nodes(certificate):
    return [index for index, node in enumerate(certificate["nodes"])
            if certificate["declarations"][node["declaration"]]["name"] == "th-lemma"]


class TestMixedValidation(unittest.TestCase):
    """Certificate validation and Lean text generation, without running Lean."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")
        cls.source = UFLRA_INPUTS["uflra_sort_to_real"]
        cls.certificate = proof_certificate.export_clause_log_certificate(cls.source)

    def test_theory_expressions_declare_uninterpreted_symbols(self):
        # The oracle of _theory_clauses reads applications and constants of
        # an uninterpreted sort (Bool and Real arguments too), and leaves a
        # term over an array sort free.
        uninterpreted = z3.Z3_OP_UNINTERPRETED
        declarations = (
            proof_to_lean._Declaration(uninterpreted, "a", (), "U"),
            proof_to_lean._Declaration(uninterpreted, "x", (), "Real"),
            proof_to_lean._Declaration(uninterpreted, "p", (), "Bool"),
            proof_to_lean._Declaration(uninterpreted, "f", ("U", "Real", "Bool"), "U"),
            proof_to_lean._Declaration(uninterpreted, "r", ("U",), "Bool"),
            proof_to_lean._Declaration(uninterpreted, "m", (), "(Array Int U)"),
            proof_to_lean._Declaration(uninterpreted, "h", ("(Array Int U)",), "U"),
        )
        nodes = tuple(proof_to_lean._Node(index, arguments) for index, arguments in
                      enumerate([(), (), (), (0, 1, 2), (3,), (), (5,)]))
        graph = proof_to_lean._Graph(declarations, nodes, (), 0, sorts=("(Array Int U)", "U"))
        context, memo = z3.Context(), {}
        expression = proof_to_lean._theory_expression(graph, 4, context, {2: 0}, memo)
        self.assertEqual(str(expression), "f4(f3(u0, v1, a0))")
        self.assertTrue(z3.is_bool(expression))
        self.assertEqual(memo[0].sort().name(), "U")
        self.assertIsNone(proof_to_lean._theory_expression(graph, 6, context, {2: 0}, memo))
        self.assertIsNone(proof_to_lean._theory_expression(graph, 5, context, {2: 0}, memo))

    def test_theory_expressions_leave_enumeration_constructors_free(self):
        # A constant of an enumeration sort is declared as one of an
        # uninterpreted sort, and so is an application over it; a constructor
        # is not read, so the oracle cannot use that two constructors differ
        # (it knows less about the sort than Lean does, never more).
        declarations = (
            proof_to_lean._Declaration(z3.Z3_OP_UNINTERPRETED, "k", (), "Color"),
            proof_to_lean._Declaration(z3.Z3_OP_DT_CONSTRUCTOR, "red", (), "Color"),
            proof_to_lean._Declaration(z3.Z3_OP_UNINTERPRETED, "g", ("Color",), "U"),
            proof_to_lean._Declaration(z3.Z3_OP_EQ, "=", ("Color", "Color"), "Bool"),
        )
        nodes = tuple(proof_to_lean._Node(index, arguments) for index, arguments in
                      enumerate([(), (), (0,), (0, 1)]))
        graph = proof_to_lean._Graph(declarations, nodes, (), 0, sorts=("Color", "U"),
                                     enumerations={"Color": ("red", "green")})
        context, memo = z3.Context(), {}
        expression = proof_to_lean._theory_expression(graph, 2, context, {}, memo)
        self.assertEqual(str(expression), "f2(u0)")
        self.assertEqual(memo[0].sort().name(), "Color")
        self.assertFalse(z3.is_app_of(memo[0], z3.Z3_OP_DT_CONSTRUCTOR))
        self.assertIsNone(proof_to_lean._theory_expression(graph, 1, context, {}, memo))
        self.assertIsNone(proof_to_lean._theory_expression(graph, 3, context, {}, memo))

    def test_generated_lean_carries_the_valuation_and_the_interpretation(self):
        self.assertEqual(self.certificate["fragment"], "qf_uflra")
        text = proof_to_lean.reconstruct(self.source, self.certificate)
        self.assertIn("theorem unsat (_atoms : Nat -> Prop)" + proof_to_lean._UFLRA_BINDERS, text)
        self.assertIn("(_vars : Nat -> Rat)", proof_to_lean._UFLRA_BINDERS)
        self.assertIn(" (_m : Interpretation)", proof_to_lean._UFLRA_BINDERS)
        self.assertIn("\n  real : Rat -> U\n  rfuns : Nat -> List U -> Rat\n", text)
        self.assertIn('-- Element 0: "a"', text)
        self.assertIn('-- Real function 0: "g"', text)
        self.assertIn('-- Uninterpreted sort "U" is the type _m.U', text)
        self.assertIn("injected into _m.U by _m.real; functions with a Real result are the family _m.rfuns", text)
        self.assertIn(" : _m.U := _m.elems 0", text)
        self.assertIn(" : Rat := _m.rfuns 0 [(term_", text)
        self.assertNotIn(":= _m.funs ", text)  # h is declared but applied nowhere in this input
        self.assertIn("private theorem th_lemma_", text)
        self.assertNotIn("sorry", text)
        self.assertNotIn("axiom ", text)
        graph = proof_to_lean._validate_graph(self.source, self.certificate)
        self.assertEqual(graph.sorts, ("U",))
        self.assertTrue(graph.arithmetic)
        self.assertTrue(graph.uninterpreted)
        self.assertEqual(graph.fragment, "qf_uflra")
        self.assertEqual(graph.valuation, proof_to_lean._UFLRA_ARGUMENTS)
        hints = set()
        for node in _th_lemma_nodes(self.certificate):
            hints.add(graph.decl(node).parameters[0])
            proof_to_lean._check_th_lemma(graph, node)
            self.assertTrue(proof_to_lean._reachable(graph, graph.conclusion(node))[1])
        self.assertEqual(hints, {"farkas", "euf"})

    def test_real_arguments_are_injected_and_predicates_range_over_real(self):
        source = UFLRA_INPUTS["uflra_real_to_sort"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertIn('-- Function 0: "h"', text)
        self.assertIn('-- Predicate 0: "p"', text)
        self.assertIn(" : _m.U := _m.funs 0 [(_m.real (term_", text)
        self.assertIn(" : Prop := _m.preds 0 [(term_", text)
        self.assertNotIn("_m.rfuns 0", text.split("namespace", 1)[1])
        source = UFLRA_INPUTS["uflra_real_predicate"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertIn(" : Prop := _m.preds 0 [(_m.real (term_", text)
        self.assertNotIn("Uninterpreted sort", text)
        graph = proof_to_lean._validate_graph(source, certificate)
        self.assertEqual(graph.sorts, ())
        self.assertEqual(graph.fragment, "qf_uflra")

    def test_equal_linear_forms_of_arguments_are_stated_for_grind(self):
        # (f (- x y)) and (f (+ x (* -1 y))) are one term to Z3's rewriter and
        # two to grind's congruence closure; the lemma states their equality.
        source = UFLRA_INPUTS["uflra_normalized_arguments"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertRegex(text, r"have _r\d+_\d+ : .* = .* := by unfold [^;]*; grind")
        graph = proof_to_lean._validate_graph(source, certificate)
        terms, tables = proof_to_lean._bind_input(source, graph, "qf_uflra")
        indices = {table: {decl: index for index, decl in enumerate(sorted(symbols.values()))}
                   for table, symbols in tables.items()}
        atom_indices = {**indices["atoms"], **indices["predicates"]}
        variable_indices = {**indices["variables"], **indices["numeric_functions"]}
        reachable = set(range(len(graph.nodes)))
        pairs = proof_to_lean._real_argument_pairs(graph, reachable)
        self.assertEqual(len(pairs), 3, pairs)  # x - y, 2 + 2 = 4, x - x = 0
        sides = [" = ".join(proof_to_lean._inline(graph, node, atom_indices, variable_indices) for node in pair)
                 for pair in pairs]
        self.assertTrue(any("(_vars 0) - (_vars 1)" in h and "* (_vars 1)" in h for h in sides), sides)
        self.assertTrue(any("((4 : Rat))" in h for h in sides), sides)
        # Each stated over the two definitions, then unfolded in place (no
        # nested ites here, so no inner equalities to clear).
        helpers = proof_to_lean._real_argument_helpers(graph, reachable, atom_indices, variable_indices)
        self.assertEqual(len(helpers), 2 * len(pairs))
        facts, unfolds = helpers[:len(pairs)], helpers[len(pairs):]
        self.assertEqual([helper.split(" : ")[0].split()[-1] for helper in facts],
                         ["_r%d_%d" % pair for pair in pairs])
        for (first, second), fact, unfold in zip(pairs, facts, unfolds):
            self.assertIn(": %s = %s := by unfold " % (proof_to_lean._term(graph, first),
                                                        proof_to_lean._term(graph, second)), fact)
            self.assertTrue(unfold.endswith(" at _r%d_%d" % (first, second)), unfold)
        # Function applications are opaque atoms of the linear forms, keyed by
        # node in the atom-normalizing rewrite shape: a rewrite whose sides
        # apply f to different renderings of one argument ((f (+ 2.0 2.0))
        # against (f 4.0)) is left to grind, one whose sides share their
        # applications, or range over variables alone, is normalizable.
        verdicts = {}
        for node in range(len(graph.nodes)):
            if graph.kind(node) != z3.Z3_OP_PR_REWRITE:
                continue
            reachable, _ = proof_to_lean._reachable(graph, graph.conclusion(node))
            atoms = [formula for formula in sorted(reachable)
                     if graph.kind(formula) in (z3.Z3_OP_LE, z3.Z3_OP_GE, z3.Z3_OP_LT, z3.Z3_OP_GT, z3.Z3_OP_EQ)
                     and graph.arguments(formula) and graph.is_arith(graph.arguments(formula)[0])]
            if not atoms:
                continue
            applications = [{term for formula in proof_to_lean._reachable(graph, side)[0]
                             if graph.is_term(formula) for term in [formula]
                             if graph.kind(term) == z3.Z3_OP_UNINTERPRETED and graph.arguments(term)}
                            for side in graph.arguments(graph.conclusion(node))]
            verdicts[node] = (proof_to_lean._normalizable_rewrite(graph, node, reachable, atoms),
                              applications[0] == applications[1])
        self.assertEqual(set(verdicts.values()), {(False, False), (True, True)}, verdicts)

    def test_ite_arguments_are_keyed_up_to_normalization(self):
        # Z3 logs (f (ite (> x 0) x (- x))) with the ite in the rewriter's
        # normal form, (ite (<= x 0) (* -1 x) x); both ite terms get one key
        # (the non-strict condition, branches swapped), so the lemma states
        # their equality, which grind proves by splitting the conditions.
        source = UFLRA_INPUTS["uflra_ite_argument"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        graph = proof_to_lean._validate_graph(source, certificate)
        ites = [node for node in range(len(graph.nodes)) if graph.kind(node) == z3.Z3_OP_ITE]
        self.assertEqual(len(ites), 2)
        self.assertNotEqual(*(graph.arguments(node)[0] for node in ites))  # different conditions
        keys = {proof_to_lean._real_argument_key(graph, node) for node in ites}
        self.assertEqual(len(keys), 1)
        (((kind, condition, then_key, else_key), _),), constant = keys.pop()
        self.assertEqual((kind, condition[0], constant), ("ite", "<=", 0))
        self.assertNotEqual(then_key, else_key)
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertRegex(text, r"have _r%d_%d : \(term_%d .* = \(term_%d .* := by unfold [^;]*; grind" % (tuple(ites) * 2))
        # A variable and an application are opaque atoms.
        opaque = [node for node in range(len(graph.nodes)) if graph.is_arith(node)
                  and graph.kind(node) == z3.Z3_OP_UNINTERPRETED]
        self.assertTrue(opaque)
        for node in opaque:
            self.assertEqual(proof_to_lean._real_atom_key(graph, node), ("atom", node))
        # So is an ite whose condition is no linear atom (a Bool variable, a
        # predicate): the two ite terms keep different keys and no helper
        # states their equality.
        source = UFLRA_INPUTS["uflra_opaque_ite_conditions"]
        for certificate in (proof_certificate.export_clause_log_certificate(source),
                            proof_certificate.export_certificate(source)):
            graph = proof_to_lean._validate_graph(source, certificate)
            ites = [node for node in range(len(graph.nodes)) if graph.kind(node) == z3.Z3_OP_ITE]
            self.assertEqual(len(ites), 2)
            for node in ites:
                self.assertEqual(graph.kind(graph.arguments(node)[0]), z3.Z3_OP_UNINTERPRETED)
                self.assertEqual(proof_to_lean._real_atom_key(graph, node), ("atom", node))
            self.assertEqual(len({proof_to_lean._real_argument_key(graph, node) for node in ites}), 2)
            self.assertNotIn("have _r", proof_to_lean.reconstruct(source, certificate))

    def test_fragment_consistency(self):
        for fragment, message in [("qf_uf", "qf_uf certificates cannot contain arithmetic"),
                                  ("propositional", "propositional certificates cannot contain arithmetic"),
                                  ("qf_lra", "only qf_uf, qf_uflra, qf_uflia, and qf_uflira certificates")]:
            certificate = copy.deepcopy(self.certificate)
            certificate["fragment"] = fragment
            with self.subTest(fragment=fragment):
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, message):
                    proof_to_lean.reconstruct(self.source, certificate)
        # A pure QF_UF certificate relabeled qf_uflra has no arithmetic.
        from test_proof_to_lean_uf import UF_INPUTS
        source = UF_INPUTS["uf_congruence"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        certificate["fragment"] = "qf_uflra"
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "qf_uflra certificates must contain arithmetic"):
            proof_to_lean.reconstruct(source, certificate)
        # A pure QF_LRA certificate relabeled qf_uflra declares no uninterpreted function.
        from test_proof_to_lean_arith import Z3TEST_LRA_INPUTS
        source = Z3TEST_LRA_INPUTS["lra_farkas"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        certificate["fragment"] = "qf_uflra"
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "only qf_uf, qf_uflra, qf_uflia, and qf_uflira certificates"):
            proof_to_lean.reconstruct(source, certificate)

    def test_malformed_mixed_declarations_are_rejected(self):
        certificate = copy.deepcopy(self.certificate)
        for declaration in certificate["declarations"]:
            if declaration["name"] == "g":
                declaration["domain"] = ["Real"]  # g takes the sort, not Real
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "wrong argument sort"):
            proof_to_lean.reconstruct(self.source, certificate)
        for domain, range_name, message in [
            (["Proof"], "Real", "unsupported arithmetic function declaration"),
            (["Proof"], "Bool", "unsupported predicate declaration"),
            (["BitVec"], "Bool", "invalid native declaration"),
            (["Real", "Proof"], "U", "unsupported uninterpreted-sort declaration"),
        ]:
            with self.subTest(domain=domain, range=range_name):
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, message):
                    proof_to_lean._declaration({"kind": z3.Z3_OP_UNINTERPRETED, "name": "w", "domain": domain,
                                                "range": range_name, "parameters": []}, ("U",))
        # A Real-valued function over the sort, Bool, and Real is a valid declaration.
        decl = proof_to_lean._declaration({"kind": z3.Z3_OP_UNINTERPRETED, "name": "w", "domain": ["U", "Bool", "Real"],
                                           "range": "Real", "parameters": []}, ("U",))
        self.assertEqual(decl.domain, ("U", "Bool", "Real"))

    def test_rebinding_to_another_signature_is_rejected(self):
        # The same assertion text with g declared over a second sort V and a
        # constant of that sort: the certificate's signatures no longer match.
        other = self.source.replace("(declare-fun g (U) Real)", "(declare-sort V 0)(declare-fun g (V) Real)")
        other = other.replace("(declare-const a U)", "(declare-const a V)").replace("(declare-const b U)", "(declare-const b V)")
        with self.assertRaises(proof_to_lean.ReconstructionError):
            proof_to_lean.reconstruct(other, self.certificate)


class TestMixedInProcess(unittest.TestCase):
    """Checks that need neither the z3 executable nor Lean (only the Python bindings)."""

    def test_numerals_as_arguments_have_distinct_normalizer_keys(self):
        context = z3.Context()
        q = z3.Function("q", z3.RealSort(context), z3.BoolSort(context))
        one, two = z3.RealVal(1, context), z3.RealVal(2, context)
        normalizer = proof_clause_log._Normalizer()
        self.assertNotEqual(normalizer.key(q(one)), normalizer.key(q(two)))
        self.assertEqual(normalizer.key(q(one)), normalizer.key(q(z3.RealVal("1.0", context))))
        self.assertNotEqual(normalizer.key(q(one)), normalizer.key(z3.Not(q(one))))

    def test_bool_only_predicates_with_arithmetic_export_through_both_cores(self):
        certificate = proof_certificate.export_clause_log_certificate(BOOL_PREDICATE_WITH_ARITHMETIC)
        self.assertEqual(certificate["fragment"], "qf_uflra")
        self.assertIn("th-lemma", certificate["rule_counts"])
        self.assertEqual({d["name"] for d in certificate["declarations"] if d["kind"] == z3.Z3_OP_UNINTERPRETED},
                         {"r", "x", "y"})
        text = proof_to_lean.reconstruct(BOOL_PREDICATE_WITH_ARITHMETIC, certificate)
        self.assertIn("No uninterpreted sort", text)
        self.assertIn(proof_to_lean._UFLRA_BINDERS, text)
        certificate = proof_certificate.export_certificate(BOOL_PREDICATE_WITH_ARITHMETIC)
        self.assertEqual(certificate["fragment"], "qf_uflra")
        text = proof_to_lean.reconstruct(BOOL_PREDICATE_WITH_ARITHMETIC, certificate)
        self.assertIn("(congrArg _m.bool (propext ", text)
        self.assertIn("No uninterpreted sort", text)


class _LeanIntegration(unittest.TestCase):
    core = "clause-log"

    def check(self, source):
        if self.core == "legacy":
            certificate = proof_certificate.export_certificate(source)
        else:
            certificate = proof_certificate.export_clause_log_certificate(source)
        self.assertEqual(certificate["fragment"], "qf_uflra")
        text, report = lean_test_support.check(self, source, certificate)
        statement = text.split("theorem unsat", 1)[1].split(": False :=", 1)[0]
        self.assertEqual(statement.count("    (_h"), len(certificate["assertions"]))
        self.assertIn(proof_to_lean._UFLRA_BINDERS, statement)
        self.assertIn(".unsat' depends on axioms: " + _STANDARD_AXIOMS, report)
        return certificate, text


@unittest.skipUnless(_z3_available(), "the z3 executable is required for the clause log")
class TestMixedLeanIntegration(_LeanIntegration):
    """End-to-end: z3 clause log, certificate, Lean reconstruction, kernel check."""

    def test_documented_inputs_verify_under_the_standard_axioms(self):
        lean_test_support.prefetch((source, proof_certificate.export_clause_log_certificate(source))
                                    for source in UFLRA_INPUTS.values())
        for name, source in UFLRA_INPUTS.items():
            with self.subTest(name=name):
                certificate, text = self.check(source)
                self.assertIn("th-lemma", certificate["rule_counts"])
                if name == "uflra_normalized_arguments":
                    self.assertIn("have _r", text)
                if name == "uflra_single_occurrence":
                    self.assertNotIn("!", json.dumps(certificate["declarations"]))
                if name == "uflra_division_axiom":
                    self.assertIn(["arith"], [d["parameters"] for d in certificate["declarations"]
                                              if d["name"] == "th-lemma"])

    def test_bool_only_predicate_over_real_atoms_verifies_through_the_clause_log(self):
        certificate, text = self.check(BOOL_PREDICATE_WITH_ARITHMETIC)
        self.assertIn("th-lemma", certificate["rule_counts"])
        self.assertIn("No uninterpreted sort", text)

    # Seeds of random_instance whose unsat core has at least three assertions
    # (plain) and the first two such seeds with an uninterpreted sort, pinned
    # so the checked inputs stay the same across Z3 versions; seed 137 (plain)
    # and 66 (sort) need the explicit equalities of Real arguments.
    PLAIN_SEEDS = (63, 160, 208)
    SORT_SEEDS = (79, 218)
    ARGUMENT_SEEDS = ((137, False), (66, True))

    def test_random_instances(self):
        for seed in self.PLAIN_SEEDS:
            source = random_instance(seed)
            with self.subTest(seed=seed):
                self.assertGreaterEqual(_unsat_core_size(source), 3, "re-pick seed %d" % seed)
                certificate, _ = self.check(source)
                self.assertIn("th-lemma", certificate["rule_counts"])
        for seed in self.SORT_SEEDS:
            source = random_instance(seed, with_sort=True)
            with self.subTest(seed=seed):
                self.assertGreaterEqual(_unsat_core_size(source), 3, "re-pick seed %d" % seed)
                self.check(source)
        for seed, with_sort in self.ARGUMENT_SEEDS:
            source = random_instance(seed, with_sort=with_sort)
            with self.subTest(seed=seed):
                _, text = self.check(source)
                self.assertIn("have _r", text)

    def test_small_chunks_cut_every_lemma_shape(self):
        with patch.object(proof_to_lean, "_OUTLINE_PROOF_STEPS", 0), \
                patch.object(proof_to_lean, "_OUTLINE_CHUNK_STEPS", 3):
            source = UFLRA_INPUTS["uflra_binary_split"]
            certificate, text = self.check(source)
            sizes = outlined_lemma_sizes(text)
            self.assertGreater(len(sizes), 1)
            self.assertLessEqual(max(sizes), 3)
            self.assertEqual(sum(sizes), _proof_steps(certificate))

    def test_cnf_lemmas_over_applications_are_refuted_with_theory_clauses(self):
        fragments = {"uflra": "qf_uflra", "uflia": "qf_uflia", "uf": "qf_uf"}
        for name, source in THEORY_CLAUSE_INPUTS.items():
            with self.subTest(name=name):
                certificate = proof_certificate.export_clause_log_certificate(source)
                self.assertEqual(certificate["fragment"], fragments[name.split("_", 1)[0]])
                text = proof_to_lean.reconstruct(source, certificate)
                lemma, head, (structural, fallback) = _cnf_lemma_attempts(certificate, text)
                self.assertNotIn("unfold", head)
                # A theory clause over a function's term definitions.
                self.assertRegex(structural, r"have _f\d+ : \(Or [^\n]*\) := by unfold [^;\n]*\bterm_\d+[^;\n]*; ")
                self.assertIn("refine Classical.byContradiction ?_", structural)
                self.assertIn("unfold formula_", fallback)
                alone = text.replace(lemma, head + "\n  first\n" + structural, 1)
                self.assertNotEqual(alone, text)
                _, report = lean_test_support.check(self, source, certificate, text=alone)
                self.assertIn(_STANDARD_AXIOMS, report)
                # With the applications and the sort's constants free in the
                # oracle (as before it declared them), the search ends in a
                # model of the abstraction, and the unfolded proof is the
                # only one.
                with patch.object(proof_to_lean, "_theory_function", lambda *arguments: None):
                    text = proof_to_lean.reconstruct(source, certificate)
                lemma, head, attempts = _cnf_lemma_attempts(certificate, text)
                self.assertNotIn("refine Classical.byContradiction", lemma)
                self.assertIn("unfold formula_", head)
                self.assertEqual(attempts, [""])


class TestLegacyMixedLeanIntegration(_LeanIntegration):
    """End-to-end through the smt core's proof object."""
    core = "legacy"

    def test_documented_inputs_verify_through_the_legacy_core(self):
        lean_test_support.prefetch((source, proof_certificate.export_certificate(source))
                                    for source in UFLRA_INPUTS.values())
        for name, source in UFLRA_INPUTS.items():
            with self.subTest(name=name):
                certificate, text = self.check(source)
                self.assertIn("monotonicity", certificate["rule_counts"])
                if name == "uflra_real_function":
                    # Congruence through a Real argument injects it by _m.real.
                    self.assertIn("(congrArg (_m.rfuns 0) (congr (congrArg List.cons (congrArg _m.real ", text)
                if name == "uflra_real_to_sort":
                    # theory_lra propagates x = y from the two bounds for the
                    # congruence (h x) = (h y): the legacy implied-eq shape,
                    # stated as the implication from its premises.
                    hints = {certificate["declarations"][node["declaration"]]["parameters"][0]
                             for node in certificate["nodes"]
                             if certificate["declarations"][node["declaration"]]["name"] == "th-lemma"}
                    self.assertIn("implied-eq", hints)
                    self.assertRegex(text, r"private theorem th_lemma_\d+ .*\n    : \(formula_\d+ [^)]*\) -> \(formula_\d+ [^)]*\) -> \(formula_\d+ [^)]*\) := by")
        certificate, text = self.check(BOOL_PREDICATE_WITH_ARITHMETIC)
        self.assertIn("monotonicity", certificate["rule_counts"])
        self.assertNotIn("th-lemma", certificate["rule_counts"])
        self.assertIn("(congrArg _m.bool (propext ", text)

    def test_random_instances_through_the_legacy_core(self):
        for seed, with_sort in ((63, False), (79, True)):
            source = random_instance(seed, with_sort=with_sort)
            with self.subTest(seed=seed):
                certificate, _ = self.check(source)
                self.assertIn("monotonicity", certificate["rule_counts"])


def _export_core(source, core):
    if core == "legacy":
        return proof_certificate.export_certificate(source)
    return proof_certificate.export_clause_log_certificate(source)


# One abs of a constant as the step states it: its value, then its replacement.
_ABS_VALUE = re.compile(r"have _av(\d+) : (\(@ite Rat .*\)) = (\(\(-?\d+ : Rat\)(?: / \(\d+ : Rat\))?\)) := by grind$")
_ABS_REPLACEMENT = "generalize %s = _at%s at *; subst _av%s"


@unittest.skipUnless(_z3_available(), "the z3 executable is required for the clause log")
class TestAbsValueValidation(unittest.TestCase):
    """Validation without Lean of the abs terms of constants: their values, where they are stated, what they key."""

    def _values(self, source, core="clause-log"):
        """The graph of the input's certificate and the value lines of all its abs terms of constants."""
        graph = proof_to_lean._validate_graph(source, _export_core(source, core))
        indices = collections.defaultdict(int)  # every variable rendered with index 0
        lines, values = proof_to_lean._abs_value_facts(graph, set(range(len(graph.nodes))), indices, indices)
        # A value and its replacement for each abs, over one text.
        self.assertEqual(len(lines), 2 * len(values), lines)
        for fact, replacement in zip(lines[::2], lines[1::2]):
            match = _ABS_VALUE.match(fact)
            self.assertIsNotNone(match, fact)
            node, side, value = match.groups()
            self.assertEqual(replacement, _ABS_REPLACEMENT % (side, node, node))
            self.assertEqual(values[int(node)], value)
            self.assertEqual(graph.kind(int(node)), z3.Z3_OP_ABS)
        return graph, lines, values

    def test_abs_of_a_constant_is_stated_and_replaced_by_its_value(self):
        for name, value in (("abs_of_a_negative_fraction", "((5 : Rat) / (2 : Rat))"),
                            ("abs_under_a_predicate", "((1 : Rat) / (2 : Rat))"),
                            ("abs_of_a_sum", "((5 : Rat) / (2 : Rat))"),
                            ("abs_of_a_third", "((1 : Rat) / (3 : Rat))"),
                            ("abs_in_a_sum_of_numerals", "((1 : Rat) / (4 : Rat))"),
                            ("abs_of_cancelling_variables", "((5 : Rat) / (2 : Rat))"),
                            ("abs_of_an_integer", "((3 : Rat))")):
            for core in ("clause-log", "legacy"):
                with self.subTest(name=name, core=core):
                    _, lines, values = self._values(ABS_VALUE_INPUTS[name], core)
                    # The legacy proof also has the abs of the argument's
                    # value, a node of its own.
                    self.assertEqual(set(values.values()), {value}, lines)
                    self.assertEqual(len(values), 1 if core == "clause-log" else 2, lines)
        # The negated fraction's abs, written out as its ite.
        _, lines, _ = self._values(ABS_VALUE_INPUTS["abs_of_a_negative_fraction"])
        self.assertIn(" : (@ite Rat (((-(((5 : Rat) / (2 : Rat))))) >= ((0 : Rat))) (Classical.propDecidable _) "
                      "((-(((5 : Rat) / (2 : Rat))))) (-((-(((5 : Rat) / (2 : Rat))))))) = ((5 : Rat) / (2 : Rat)) "
                      ":= by grind", lines[0])

    def test_a_nested_abs_is_stated_over_the_inner_value(self):
        # |-5/2| = 5/2 first, then |5/2 - 4| = 3/2 over the numeral 5/2: one
        # ite in each statement.
        _, lines, values = self._values(ABS_VALUE_INPUTS["nested_abs"])
        self.assertEqual(list(values.values()), ["((5 : Rat) / (2 : Rat))", "((3 : Rat) / (2 : Rat))"])
        self.assertEqual(sorted(values), list(values))
        inner, outer = (_ABS_VALUE.match(line).group(2) for line in lines[::2])
        self.assertEqual((inner.count("@ite"), outer.count("@ite")), (1, 1))
        self.assertIn("((((5 : Rat) / (2 : Rat))) - (((4 : Rat))))", outer)
        # Two abs nodes that are one Lean term are both stated and replaced
        # (the second replacement finds the term in its own fact).
        _, lines, values = self._values(ABS_VALUE_INPUTS["one_abs_written_twice"])
        self.assertEqual(list(values.values()), ["((1 : Rat) / (2 : Rat))"] * 2)

    def test_other_abs_terms_have_no_value(self):
        # An abs of a variable, an Int abs of a constant (the simplifier
        # evaluates it), and an abs over the floor of a constant.
        for source in ("(declare-fun g (Real) Real)\n(declare-const x Real)\n"
                       "(assert (not (= (g (abs (- x))) (g (abs x)))))\n",
                       "(declare-fun f (Int) Int)\n(assert (not (= (f (abs (- 3))) (f 3))))\n",
                       "(declare-fun g (Real) Real)\n"
                       "(assert (not (= (g (abs (- (to_real (to_int 2.5)) 4.5))) (g 2.5))))\n"):
            with self.subTest(source=source):
                graph, lines, _ = self._values(source)
                self.assertTrue([node for node in range(len(graph.nodes)) if graph.kind(node) == z3.Z3_OP_ABS])
                self.assertEqual(lines, [])
                self.assertNotIn("_av", proof_to_lean.reconstruct(source, _export_core(source, "clause-log")))
        # The Int abs still counts by its value where arguments are compared.
        graph, _, _ = self._values("(declare-fun f (Int) Int)\n(assert (not (= (f (abs (- 3))) (f 3))))\n")
        node = next(node for node in range(len(graph.nodes)) if graph.kind(node) == z3.Z3_OP_ABS)
        self.assertEqual(proof_to_lean._abs_free_value(graph, node), 3)
        self.assertEqual(proof_to_lean._real_argument_key(graph, node), ((), 3))

    def test_arguments_are_keyed_by_the_value_of_an_abs(self):
        # (+ x (abs (- 0.75)) 0.5) and (+ 1.25 x) have one key, and the
        # helper that equates them replaces the abs in its own goal.
        source = ABS_VALUE_INPUTS["abs_next_to_a_variable"]
        graph, _, values = self._values(source)
        (node,) = values
        arguments = [argument for parent in range(len(graph.nodes))
                     if graph.kind(parent) == z3.Z3_OP_UNINTERPRETED for argument in graph.arguments(parent)]
        self.assertEqual(len(set(arguments)), 2)
        self.assertEqual(len({proof_to_lean._real_argument_key(graph, argument) for argument in arguments}), 1)
        self.assertEqual(proof_to_lean._real_argument_key(graph, arguments[0])[1], Fraction(5, 4))
        self.assertIn(tuple(sorted(set(arguments))),
                      proof_to_lean._real_argument_pairs(graph, set(range(len(graph.nodes)))))
        text = proof_to_lean.reconstruct(source, _export_core(source, "clause-log"))
        self.assertRegex(text, r"have _r\d+_\d+ : \(term_\d+ [^=]*= \(term_\d+ [^:]* := by unfold [^;]*term_%d[^;]*; "
                               r"\(have _av%d : \(@ite Rat .* := by grind\); "
                               r"\(generalize \(@ite Rat .* = _at%d at \*; subst _av%d\); grind"
                               % ((node,) * 4))
        # In the step itself the replacement follows the helpers and
        # precedes the tactic.
        self.assertRegex(text, r"\n +unfold [^\n]* at _r\d+_\d+\n +have _av%d : [^\n]* := by grind\n"
                               r" +generalize [^\n]* = _at%d at \*; subst _av%d\n +grind \(splits := 64\)\)"
                               % ((node,) * 3))
        # In a certificate with arrays the helper is stated over the terms
        # written out, and makes the replacement in its goal the same way.
        source = ABS_ARRAY_INPUTS["floors_of_one_value_next_to_a_read"]
        text = proof_to_lean.reconstruct(source, _export_core(source, "clause-log"))
        self.assertRegex(text, r"have _r\d+_\d+ : \(Rat\.floor [^\n]* := by "
                               r"\(have _av\d+ : \(@ite Rat [^\n]* := by grind\); "
                               r"\(generalize \(@ite Rat [^\n]* = _at\d+ at \*; subst _av\d+\); first \| ")

    def test_floors_are_stated_over_the_value_of_an_abs(self):
        # floor |-5/2| = 2 and floor (3/4 - 2 - |1/2|) = -2, both over the
        # numeral that replaced the abs, after its replacement.
        for name, floored, value in (
                ("floor_of_an_abs", "((5 : Rat) / (2 : Rat))", "2"),
                ("floor_of_a_difference_with_an_abs",
                 "((((((3 : Rat) / (4 : Rat))) - (((2 : Rat))))) - (((1 : Rat) / (2 : Rat))))", "-2")):
            with self.subTest(name=name):
                source = ABS_FLOOR_INPUTS[name]
                certificate = _export_core(source, "clause-log")
                self.assertEqual(certificate["fragment"], "qf_uflira")
                text = proof_to_lean.reconstruct(source, certificate)
                fact = "have _zi%%s : Rat.floor (%s) = (((%s : Int))) := _floor_value _ _ " % (floored, value)
                self.assertRegex(text, r"\n +have _av\d+ : [^\n]*\n +generalize [^\n]* = _at\d+ at \*; "
                                       r"subst _av\d+\n +" + re.escape(fact).replace("%s", r"\d+", 1))
                self.assertIn("try (generalize Rat.floor (%s) = _fv" % floored, text)
        # Without the map of replaced terms the floor of an abs has no value.
        source = ABS_FLOOR_INPUTS["floor_of_an_abs"]
        graph, _, values = self._values(source)
        indices = collections.defaultdict(int)
        self.assertEqual(proof_to_lean._floor_shift_facts(graph, list(values), indices, indices), ([], []))
        facts, substitutions = proof_to_lean._floor_shift_facts(graph, list(values), indices, indices, values)
        self.assertEqual((len(facts), len(substitutions)), (2, 1))
        # The floors of two terms that differ by an integer are related over
        # the value too: floor (x + 5/2) = floor (x + 1/2) + 2, no abs left.
        source = ABS_FLOOR_INPUTS["floors_that_differ_by_an_integer"]
        shifts = re.findall(r"have _di\d+_\d+ := [^\n]*", proof_to_lean.reconstruct(
            source, _export_core(source, "clause-log")))
        self.assertIn("(show (((_vars 0) + (((5 : Rat) / (2 : Rat))))) = (((_vars 0) + (((1 : Rat) / (2 : Rat))))) + "
                      "(((((2 : Int))) : Int) : Rat) by push_cast; grind)", "\n".join(shifts))
        for shift in shifts:
            self.assertNotIn("@ite", shift)

    def test_constant_indices_of_reads_are_related_as_arguments(self):
        source = ABS_ARRAY_INPUTS["read_at_a_numeral_expression_among_others"]
        certificate = _export_core(source, "clause-log")
        graph = proof_to_lean._validate_graph(source, certificate)
        indices = sorted({graph.arguments(node)[1] for node in range(len(graph.nodes))
                          if graph.kind(node) == z3.Z3_OP_SELECT})
        # The input's two indices and the rewriter's numeral.
        self.assertGreaterEqual(len(indices), 2)
        self.assertEqual({proof_to_lean._abs_free_value(graph, index) for index in indices}, {Fraction(-1, 4)})
        pairs = proof_to_lean._real_argument_pairs(graph, set(range(len(graph.nodes))))
        text = proof_to_lean.reconstruct(source, certificate)
        for pair in zip(indices, indices[1:]):
            self.assertIn(pair, pairs)
        # Each step states the pairs it reaches: the rewrite the input's
        # index and the numeral.
        stated = {(int(first), int(second))
                  for first, second in re.findall(r"have _r(\d+)_(\d+) : .* = .* := by grind", text)}
        self.assertTrue([pair for pair in stated if set(pair) <= set(indices)], stated)
        # An index over a variable is no constant: reads at (+ i 1.0) and
        # (+ 1.0 i) are left to grind, as before.
        source = ("(declare-fun g (Real) Real)\n(declare-const a (Array Real Real))\n(declare-const i Real)\n"
                  "(assert (not (= (g (select a (+ i 1.0))) (g (select a (+ 1.0 i))))))\n")
        self.assertNotIn("have _r", proof_to_lean.reconstruct(source, _export_core(source, "clause-log")))


# The lines of a step that state the value of an abs of a constant and
# replace it, and the segments an argument helper puts before its tactic.
_STEP_ABS_VALUE = r"\s*have _av\d+ : \(@ite Rat .* := by grind$"
_STEP_ABS_REPLACEMENT = r"\s*generalize \(@ite Rat .* = _at\d+ at \*; subst _av\d+$"
_HELPER_ABS_VALUE = r"\(have _av\d+ : \(@ite Rat [^\n;]* := by grind\); "
_HELPER_ABS_REPLACEMENT = r"\(generalize \(@ite Rat [^\n;]* = _at\d+ at \*; subst _av\d+\); "


def _without_abs_values(text, steps=True, helpers=True, values=True):
    """The Lean text without the replacements of its abs terms of constants by their values.

    In the steps, in the goals of their argument helpers, or both; with
    values the facts that state the values are left out too, otherwise
    they stay and only the generalize and subst go.
    """
    if steps:
        patterns = [_STEP_ABS_REPLACEMENT] + ([_STEP_ABS_VALUE] if values else [])
        text = "\n".join(line for line in text.split("\n")
                         if not any(re.match(pattern, line) for pattern in patterns))
    if helpers:
        text = re.sub((_HELPER_ABS_VALUE if values else "") + _HELPER_ABS_REPLACEMENT, "", text)
    return text


@unittest.skipUnless(_z3_available(), "the z3 executable is required for the clause log")
class TestAbsValueLeanIntegration(unittest.TestCase):
    """End-to-end over abs terms of constants: both proof cores, certificate, Lean reconstruction, kernel check."""

    # The array inputs are in qf_uflra but the one that floors.
    INPUTS = ([(name, source, "qf_uflra", ("clause-log", "legacy")) for name, source in ABS_VALUE_INPUTS.items()]
              + [(name, source, "qf_uflira", ("clause-log", "legacy")) for name, source in ABS_FLOOR_INPUTS.items()]
              + [(name, source, "qf_uflira" if "to_int" in source else "qf_uflra", ("clause-log",))
                 for name, source in ABS_ARRAY_INPUTS.items()])
    BINDERS = {"qf_uflra": proof_to_lean._UFLRA_BINDERS, "qf_uflira": proof_to_lean._UFLIRA_BINDERS}

    def check(self, source, core, fragment):
        certificate = _export_core(source, core)
        self.assertEqual(certificate["fragment"], fragment)
        text, report = lean_test_support.check(self, source, certificate)
        statement = text.split("theorem unsat", 1)[1].split(": False :=", 1)[0]
        self.assertEqual(statement.count("    (_h"), len(certificate["assertions"]))
        self.assertIn(self.BINDERS[fragment], statement)
        axioms = re.search(r"\.unsat' depends on axioms: \[(.*?)\]", report)
        self.assertIsNotNone(axioms, report)
        self.assertLessEqual(set(axioms.group(1).split(", ")), {"propext", "Classical.choice", "Quot.sound"}, report)
        return text

    def rejected(self, name, **parts):
        """Check that Lean rejects a clause-log certificate, by a failing grind, without parts of its replacements.

        name is a documented input or (seed, options) of the generator;
        parts are _without_abs_values's. Returns the texts, whole and
        without the parts.
        """
        if isinstance(name, str):
            source = {**ABS_VALUE_INPUTS, **ABS_FLOOR_INPUTS, **ABS_ARRAY_INPUTS}[name]
        else:
            source = random_abs_value_instance(name[0], **name[1])
            self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % name[0])
        text = proof_to_lean.reconstruct(source, _export_core(source, "clause-log"))
        stripped = _without_abs_values(text, **parts)
        self.assertNotEqual(stripped, text)
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "stripped.lean"
            output.write_text(stripped)
            result = lean_test_support.run_check_lean(output)
        report = result.stdout + result.stderr
        self.assertNotEqual(result.returncode, 0, report)
        errors = [line for line in report.split("\n") if "error:" in line]
        self.assertTrue(errors, report)
        for error in errors:
            self.assertIn("`grind` failed", error)
        return text, stripped

    def test_documented_inputs_verify_on_both_cores(self):
        lean_test_support.prefetch((source, _export_core(source, core)) for _, source, _, cores in self.INPUTS
                                    for core in cores)
        for name, source, fragment, cores in self.INPUTS:
            for core in cores:
                with self.subTest(name=name, core=core):
                    text = self.check(source, core, fragment)
                    if core == "clause-log" and "(abs " in source:
                        self.assertIn("have _av", text)

    def test_pinned_random_instances_verify_on_both_cores(self):
        for options, seeds in ABS_VALUE_SEEDS:
            for seed in seeds:
                source = random_abs_value_instance(seed, **options)
                self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % seed)
                for core in ("clause-log",) if "arrays" in options else ("clause-log", "legacy"):
                    with self.subTest(seed=seed, options=sorted(options), core=core):
                        text = self.check(source, core, "qf_uflira" if "floors" in options else "qf_uflra")
                        if core == "clause-log":
                            self.assertIn("have _av", text)

    def test_the_values_are_needed(self):
        # Without the values and replacements Lean rejects the rewrites
        # over floors, in the step and in the helper that equates two
        # floors. (An argument that is an abs is related to its value by an
        # argument helper as well, which grind proves by splitting the abs.)
        for name in ("floor_of_an_abs", "floor_of_a_difference_with_an_abs", "floors_of_one_value"):
            with self.subTest(name=name):
                _, stripped = self.rejected(name)
                self.assertNotIn("_av", stripped)

    def test_the_replacements_are_needed(self):
        # With every value still stated and only the replacements left out
        # Lean rejects these too: the abs terms the facts are about are the
        # goal's, and the steps rest on their being replaced there. (That a
        # replacement succeeds shows nothing: the generalize always finds
        # its term in the fact stated before it.) Under floors, in the
        # folded and the written out argument helper, and without floors in
        # the rewrite of an inequality over a variable and an abs (seed 111).
        for name in ("floor_of_an_abs", "floors_of_one_value", "floors_of_one_value_next_to_a_read",
                     (111, {"arrays": True})):
            with self.subTest(name=name):
                text, stripped = self.rejected(name, values=False)
                self.assertEqual(stripped.count("have _av"), text.count("have _av"))
                self.assertNotRegex(stripped, r"_at\d")

    def test_the_helpers_replace_in_their_own_goals(self):
        # With the steps' own replacements kept, Lean rejects the helper
        # that equates two floors once it proves the equality over the abs
        # as written: stated folded, and written out next to arrays.
        for name in ("floors_of_one_value", "floors_of_one_value_next_to_a_read"):
            with self.subTest(name=name):
                _, stripped = self.rejected(name, steps=False)
                self.assertNotIn("(have _av", stripped)
                self.assertRegex(stripped, r"\n +have _av\d+ : ")

    def test_the_steps_replace_after_their_helpers(self):
        # With the helpers' replacements kept, Lean rejects the step that
        # does not make its own: among the facts of the conversions, and in
        # a step without conversions (seed 111, the rewrite of an inequality).
        for name in ("floor_of_a_difference_with_an_abs", (111, {"arrays": True})):
            with self.subTest(name=name):
                _, stripped = self.rejected(name, helpers=False)
                self.assertNotRegex(stripped, r"\n +have _av\d+ : ")


if __name__ == "__main__":
    unittest.main()
