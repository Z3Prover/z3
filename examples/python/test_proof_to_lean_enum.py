############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Tests for enumeration datatypes (declare-datatype(s) with nullary
# constructors only) in the Lean reconstruction. An enumeration is one more
# sort of the carrier _m.U: its constructors are the family _m.ctors, and
# the interpretation states that two constructors of one enumeration differ
# (enum_distinct) and that every constant and function value of the sort is
# one of them (enum_cases_i, enum_fcases_j). The clause log's datatype hints
# (the datatype solver's case splits) are proved by grind from those fields.
# Validation without Lean, and end-to-end checks through the clause-log core
# that need the z3 executable and the pinned Lean toolchain.
############################################
import copy
from pathlib import Path
import random
import re
import sys
import tempfile
import time
import unittest

import z3

_EXAMPLES = Path(__file__).resolve().parent
sys.path.insert(0, str(_EXAMPLES))
import proof_certificate
import proof_clause_log
import lean_test_support
import proof_to_lean
from test_proof_to_lean_lia import _STANDARD_AXIOMS, _hints, _z3_available

_COLOR = "(declare-datatypes ((Color 0)) (((red) (green) (blue))))\n"

# Documented inputs: each refutation needs what an enumeration is, its
# constructors being distinct, its values being among them, or both.
ENUM_INPUTS = {
    # Four pairwise distinct values of a three-constructor enumeration. Z3
    # used to refute a root distinct with more arguments than the sort has
    # values by an empty clause with an empty tseitin hint, which certifies
    # nothing (the exporter rejected the log; an earlier build crashed writing
    # it); with proofs it now adds the pairwise disequalities and the
    # datatype solver's case splits refute them.
    "pigeonhole": _COLOR + """(declare-const a Color)
(declare-const b Color)
(declare-const c Color)
(declare-const d Color)
(assert (distinct a b c d))
(check-sat)
""",
    # A value that is none of the constructors (exhaustiveness alone).
    "none_of_the_constructors": _COLOR + """(declare-const a Color)
(assert (not (= a red)))
(assert (not (= a green)))
(assert (not (= a blue)))
(check-sat)
""",
    # Two constructors are distinct (blue is never mentioned, yet its
    # constructor is part of the encoding).
    "constructor_clash": _COLOR + """(declare-const a Color)
(assert (= a red))
(assert (= a green))
(check-sat)
""",
    # A function into the enumeration takes four distinct values: the
    # exhaustiveness of its results over every argument list (enum_fcases).
    "function_into_enumeration": _COLOR + """(declare-sort U 0)
(declare-fun f (U) Color)
(declare-const x U)
(declare-const y U)
(declare-const z U)
(declare-const w U)
(assert (distinct (f x) (f y) (f z) (f w)))
(check-sat)
""",
    # A transition function over a state enumeration: two steps from any
    # state but idle reach done.
    "state_machine": """(declare-datatype State ((idle) (busy) (done)))
(declare-fun next (State) State)
(declare-const s0 State)
(declare-const s1 State)
(declare-const s2 State)
(assert (= (next idle) busy))
(assert (= (next busy) done))
(assert (= (next done) done))
(assert (= s1 (next s0)))
(assert (= s2 (next s1)))
(assert (not (= s2 done)))
(assert (not (= s0 idle)))
(check-sat)
""",
    # An enumeration next to Int arithmetic (qf_uflia): a level per mode.
    "mode_levels": """(declare-datatype Mode ((off) (low) (high)))
(declare-fun level (Mode) Int)
(declare-const m Mode)
(declare-const k Int)
(assert (= (level off) 0))
(assert (= (level low) 1))
(assert (= (level high) 2))
(assert (= k (level m)))
(assert (> k 2))
(check-sat)
""",
    # Two enumerations, one the result of a function over the other.
    "two_enumerations": _COLOR + """(declare-datatype Bit ((zero) (one)))
(declare-fun g (Color) Bit)
(declare-const a Color)
(declare-const b Color)
(declare-const c Color)
(assert (distinct (g a) (g b)))
(assert (distinct (g b) (g c)))
(assert (distinct (g a) (g c)))
(check-sat)
""",
    # z3test regressions/smt2/t198.smt2: recognizers, ((_ is A) x) is (= x A),
    # in the SMT-LIB 2.5 declaration syntax.
    "recognizers": """(declare-datatypes () ((T A B)))
(declare-const x T)
(assert ((_ is A) x))
(assert ((_ is B) x))
(check-sat)
""",
    # Recognizers and an equality over an application, a case split away.
    "recognizer_split": _COLOR + """(declare-fun f (Color) Color)
(declare-const a Color)
(assert (not ((_ is red) (f a))))
(assert (not ((_ is green) (f a))))
(assert (not (= (f a) blue)))
(check-sat)
""",
    # SMT-LIB 2.5's is-c recognizers (a declaration of their own in Z3, which
    # the clause log prints as (_ is c)).
    "old_style_recognizers": """(declare-datatypes () ((T A B C)))
(declare-fun f (T) T)
(declare-const x T)
(assert (is-A (f x)))
(assert (not (= (f x) A)))
(assert (or (is-B x) (is-C x)))
(assert (= (f x) x))
(check-sat)
""",
    # A one-constructor enumeration has a single value.
    "single_constructor": """(declare-datatype One ((only)))
(declare-const a One)
(declare-const b One)
(assert (not (= a b)))
(check-sat)
""",
    # An enumeration next to an uninterpreted predicate and an ite over the
    # enumeration: whichever branch is taken, P holds of a constructor.
    "predicate_and_ite": _COLOR + """(declare-fun P (Color) Bool)
(declare-const c Color)
(declare-const p Bool)
(assert (P red))
(assert (P green))
(assert (P blue))
(assert (not (P (ite p c red))))
(check-sat)
""",
}


# Documented inputs over arrays of an enumeration, (Array I Color): each
# refutation needs the cases of a read (one of the constructors), of an array
# constant, a store, an ite of arrays, or a function's array value.
ENUM_ARRAY_INPUTS = {
    # A read that is none of the constructors (enum_acases).
    "read_of_a_constant": _COLOR + """(declare-const a (Array Int Color))
(declare-const i Int)
(assert (not (= (select a i) red)))
(assert (not (= (select a i) green)))
(assert (not (= (select a i) blue)))
(check-sat)
""",
    # A read of a store at another index may be the stored value or the
    # array's: both are constructors (_cases_store).
    "read_of_a_store": _COLOR + """(declare-const a (Array Int Color))
(declare-const i Int)
(declare-const j Int)
(declare-const c Color)
(assert (not (= (select (store a i c) j) red)))
(assert (not (= (select (store a i c) j) green)))
(assert (not (= (select (store a i c) j) blue)))
(check-sat)
""",
    # Four distinct reads of one array (a pigeonhole over reads).
    "four_distinct_reads": _COLOR + """(declare-const a (Array Int Color))
(assert (distinct (select a 0) (select a 1) (select a 2) (select a 3)))
(check-sat)
""",
    # A read of an ite over arrays (_cases_ite), and recognizers.
    "read_of_an_ite": _COLOR + """(declare-const a (Array Int Color))
(declare-const b (Array Int Color))
(declare-const p Bool)
(declare-const i Int)
(assert (not ((_ is red) (select (ite p a b) i))))
(assert (not ((_ is green) (select (ite p a b) i))))
(assert (not ((_ is blue) (select (ite p a b) i))))
(check-sat)
""",
    # A function into arrays of an enumeration over uninterpreted indices
    # (enum_afcases), its value an argument of a predicate too: x and y
    # differ, so blue is left for the read of f y.
    "function_into_arrays": _COLOR + """(declare-sort U 0)
(declare-fun f (U) (Array U Color))
(declare-fun Q ((Array U Color)) Bool)
(declare-const x U)
(declare-const y U)
(declare-const k U)
(assert (Q (f x)))
(assert (not (Q (f y))))
(assert (not ((_ is red) (select (f y) k))))
(assert (not ((_ is green) (select (f y) k))))
(assert (or (= x y) (not ((_ is blue) (select (f y) k)))))
(check-sat)
""",
    # Bool indices: three distinct reads at true, false, and p.
    "bool_indices": _COLOR + """(declare-const a (Array Bool Color))
(declare-const p Bool)
(assert (distinct (select a true) (select a false) (select a p)))
(check-sat)
""",
    # Array indices: four distinct reads at Int arrays.
    "array_indices": _COLOR + """(declare-const a (Array (Array Int Int) Color))
(declare-const b (Array Int Int))
(declare-const c (Array Int Int))
(declare-const d (Array Int Int))
(declare-const e (Array Int Int))
(assert (distinct (select a b) (select a c) (select a d) (select a e)))
(check-sat)
""",
    # Extensionality: two arrays equal after one store at the same index,
    # with equal reads there, are equal.
    "extensionality": _COLOR + """(declare-const a (Array Int Color))
(declare-const b (Array Int Color))
(declare-const i Int)
(assert (= (store a i red) (store b i red)))
(assert (not (= a b)))
(assert (= (select a i) (select b i)))
(check-sat)
""",
}


# Documented inputs over constant arrays of an enumeration (Int or Real
# indices): a read of one is its value (_cases_const), and so is its default
# value (_cases_default_const), the default value of a store being that of
# the array below it (_cases_default_store).
ENUM_CONSTANT_INPUTS = {
    # A read of a store over a constant array at another index is the stored
    # value or the constant's.
    "read_of_a_constant_store": _COLOR + """(declare-const c Color)
(declare-const i Int)
(declare-const j Int)
(assert (not ((_ is red) (select (store ((as const (Array Int Color)) c) i green) j))))
(assert (not ((_ is green) (select (store ((as const (Array Int Color)) c) i green) j))))
(assert (not ((_ is blue) (select (store ((as const (Array Int Color)) c) i green) j))))
(check-sat)
""",
    # The default value of an ite of a store over a constant array and a
    # constant array.
    "default_of_constant_arrays": _COLOR + """(declare-const c Color)
(declare-const i Int)
(declare-const p Bool)
(define-fun k () (Array Int Color)
  (ite p (store ((as const (Array Int Color)) c) i green) ((as const (Array Int Color)) blue)))
(assert (not ((_ is red) (default k))))
(assert (not ((_ is green) (default k))))
(assert (not ((_ is blue) (default k))))
(check-sat)
""",
    # An array constant equal to a constant array; its reads are the value.
    "array_equal_to_a_constant": _COLOR + """(declare-const a (Array Int Color))
(declare-const i Int)
(assert (= a ((as const (Array Int Color)) red)))
(assert (not (= (select a i) red)))
(check-sat)
""",
    # Two stores at one index over constant arrays of different values
    # differ (the rewriter compares their default values; the comparison
    # reaches a cnf step).
    "constant_arrays_differ": _COLOR + """(declare-const c Color)
(declare-const d Color)
(assert (= (store ((as const (Array Int Color)) c) 0 red) (store ((as const (Array Int Color)) d) 0 red)))
(assert (not (= c d)))
(check-sat)
""",
    # Real indices.
    "real_indices": _COLOR + """(declare-const c Color)
(declare-const x Real)
(declare-const y Real)
(assert (not ((_ is red) (select (store ((as const (Array Real Color)) c) y blue) x))))
(assert (not ((_ is green) (select (store ((as const (Array Real Color)) c) y blue) x))))
(assert (not ((_ is blue) (select (store ((as const (Array Real Color)) c) y blue) x))))
(check-sat)
""",
}


# z3test regressions/smt2/z3.14.smt2: the second query, four distinct values
# of a three-constructor enumeration, had no certifiable proof (see pigeonhole).
Z3_14 = """(set-option :auto-config true)
(set-option :produce-models true)

(declare-datatypes () ((S A B C)))
(declare-const x S)
(declare-const y S)
(declare-const z S)
(declare-const u S)
(assert (distinct x y z))
(check-sat)
(assert (distinct x y z u))
(check-sat)
"""


def random_enum_instance(seed, variables=3, constraints=12, depth=2, integer=False):
    """A random input over two enumerations, an uninterpreted sort, and (with integer) Int, or None if sat.

    Color (three constructors) and Bit (two) constants, functions between
    them and from the sort (f, g, h), a predicate (P), Boolean constants,
    ite terms over Color, recognizers, and with integer a function from
    Color into Int compared with an Int constant.
    """
    rng = random.Random(seed)
    lines = ["(set-logic ALL)",
             "(declare-datatypes ((Color 0)) (((red) (green) (blue))))",
             "(declare-datatype Bit ((zero) (one)))",
             "(declare-sort U 0)", "(declare-const u U)", "(declare-const v U)",
             "(declare-const p Bool)", "(declare-const q Bool)"]
    lines += ["(declare-const c%d Color)" % i for i in range(variables)]
    lines += ["(declare-const b%d Bit)" % i for i in range(variables)]
    lines += ["(declare-fun f (Color) Color)", "(declare-fun g (U) Color)", "(declare-fun h (Color Bit) Bit)",
              "(declare-fun P (Color) Bool)"]
    if integer:
        lines += ["(declare-fun level (Color) Int)", "(declare-const n Int)"]

    def condition():
        return rng.choice(["p", "q", "(P %s)" % color(0), "(= %s %s)" % (bit(0), bit(0))])

    def color(d=depth):
        roll = rng.random()
        if d == 0 or roll < 0.35:
            return "c%d" % rng.randrange(variables)
        if roll < 0.55:
            return rng.choice(["red", "green", "blue"])
        if roll < 0.75:
            return "(f %s)" % color(d - 1)
        if roll < 0.85:
            return "(g %s)" % rng.choice(["u", "v"])
        return "(ite %s %s %s)" % (condition(), color(d - 1), color(d - 1))

    def bit(d=depth):
        roll = rng.random()
        if d == 0 or roll < 0.4:
            return "b%d" % rng.randrange(variables)
        if roll < 0.6:
            return rng.choice(["zero", "one"])
        return "(h %s %s)" % (color(d - 1), bit(d - 1))

    def atom():
        roll = rng.random()
        if roll < 0.4:
            return "(= %s %s)" % (color(), color())
        if roll < 0.55:
            return "(distinct %s %s %s)" % (color(), color(), color())
        if roll < 0.7:
            return "(= %s %s)" % (bit(), bit())
        if roll < 0.75:
            return "(P %s)" % color()
        if roll < 0.8:
            return "((_ is %s) %s)" % (rng.choice(["red", "green", "blue"]), color())
        if integer and roll < 0.9:
            return "(%s (level %s) %s)" % (rng.choice(["<=", "<", "="]), color(),
                                           rng.choice(["n", "0", "1", "(+ n 1)"]))
        return rng.choice(["p", "q", "(= u v)"])

    def formula():
        roll = rng.random()
        if roll < 0.5:
            return atom()
        if roll < 0.8:
            return "(or %s %s)" % (atom(), atom())
        return "(not %s)" % atom()

    lines += ["(assert %s)" % formula() for _ in range(constraints)]
    lines.append("(check-sat)")
    source = "\n".join(lines) + "\n"
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set("timeout", 10000)
    solver.from_string(source)
    return source if solver.check() == z3.unsat else None


def random_enum_array_instance(seed, variables=2, constraints=10, depth=2, index="Int", constant=False):
    """A random input over arrays of an enumeration, (Array index Color), or None if sat.

    Array constants a0, a1, ..., a function f into the arrays, stores of
    Color terms, ite over arrays and over Color terms; reads at index
    constants (and numerals over Int), compared with each other and with the
    constructors, recognizers, a predicate P over Color, and array
    equalities. index is Int or U (an uninterpreted index sort). With
    constant (Int indices), arrays are also constant arrays of Color terms,
    and atoms also compare the default value of an array built from
    constant arrays by store and ite (the default values the exporter
    admits) with a Color term or a constructor.
    """
    rng = random.Random(seed)
    lines = ["(set-logic ALL)", "(declare-datatypes ((Color 0)) (((red) (green) (blue))))",
             "(declare-sort U 0)", "(declare-const p Bool)", "(declare-const q Bool)",
             "(declare-fun P (Color) Bool)", "(declare-fun f (U) (Array %s Color))" % index,
             "(declare-const u U)", "(declare-const v U)"]
    lines += ["(declare-const a%d (Array %s Color))" % (i, index) for i in range(variables)]
    lines += ["(declare-const k%d %s)" % (i, index) for i in range(variables + 1)]
    lines += ["(declare-const c%d Color)" % i for i in range(variables)]

    def position():
        if index == "Int" and rng.random() < 0.3:
            return str(rng.randrange(3))
        return "k%d" % rng.randrange(variables + 1)

    def array(d=depth):
        if constant and rng.random() < 0.25:
            return "((as const (Array Int Color)) %s)" % color(max(d - 1, 0))
        roll = rng.random()
        if d == 0 or roll < 0.4:
            return "a%d" % rng.randrange(variables)
        if roll < 0.75:
            return "(store %s %s %s)" % (array(d - 1), position(), color(d - 1))
        if roll < 0.85:
            return "(f %s)" % rng.choice(["u", "v"])
        return "(ite %s %s %s)" % (rng.choice(["p", "q"]), array(d - 1), array(d - 1))

    def color(d=depth):
        roll = rng.random()
        if d == 0 or roll < 0.25:
            return "c%d" % rng.randrange(variables)
        if roll < 0.4:
            return rng.choice(["red", "green", "blue"])
        if roll < 0.9:
            return "(select %s %s)" % (array(d - 1), position())
        return "(ite %s %s %s)" % (rng.choice(["p", "q"]), color(d - 1), color(d - 1))

    def constant_built(d=depth):
        roll = rng.random()
        if d == 0 or roll < 0.4:
            return "((as const (Array Int Color)) %s)" % color(max(d - 1, 0))
        if roll < 0.8:
            return "(store %s %s %s)" % (constant_built(d - 1), position(), color(d - 1))
        return "(ite %s %s %s)" % (rng.choice(["p", "q"]), constant_built(d - 1), constant_built(d - 1))

    def atom():
        if constant and rng.random() < 0.2:
            if rng.random() < 0.5:
                return "((_ is %s) (default %s))" % (rng.choice(["red", "green", "blue"]), constant_built())
            return "(= (default %s) %s)" % (constant_built(), color())
        roll = rng.random()
        if roll < 0.4:
            return "(= %s %s)" % (color(), color())
        if roll < 0.55:
            return "(distinct %s %s %s)" % (color(), color(), color())
        if roll < 0.65:
            return "((_ is %s) %s)" % (rng.choice(["red", "green", "blue"]), color())
        if roll < 0.75:
            return "(P %s)" % color()
        if roll < 0.9:
            return "(= %s %s)" % (array(), array())
        return rng.choice(["p", "q"])

    def formula():
        roll = rng.random()
        if roll < 0.5:
            return atom()
        if roll < 0.8:
            return "(or %s %s)" % (atom(), atom())
        return "(not %s)" % atom()

    lines += ["(assert %s)" % formula() for _ in range(constraints)]
    lines.append("(check-sat)")
    source = "\n".join(lines) + "\n"
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set("timeout", 10000)
    solver.from_string(source)
    return source if solver.check() == z3.unsat else None


# Pinned unsatisfiable seeds over recognizers, ite terms, and applications:
# (keyword arguments, seed). On iteration 67's macOS build, 24, 125, and 181
# (and 133 with integer) failed before the datatype lemma took the logged
# clause (the hint states (= c0 blue) for the logged (= blue c0)), and 89
# and 110 of the small configuration failed Lean before the replay's keys
# told constructors apart ((= x red) and (= x blue) shared a key). Which
# hints a seed's log carries depends on Z3's search, so only verification is
# asserted. 53 with integer has Int lemmas with opaque atoms over
# enumeration applications, whose outside definitions are unfolded before
# the lemma's unfold; that unfold must therefore not name the applications
# themselves (_folded_enumeration_cases), and the seed fails Lean if it does.
_SMALL = {"variables": 2, "constraints": 6}
ENUM_SEEDS = (({}, 24), ({}, 125), ({}, 181), ({"integer": True}, 53), ({"integer": True}, 133),
              ({"integer": True}, 150), (_SMALL, 89), (_SMALL, 110))


# Pinned unsatisfiable seeds of random_enum_array_instance whose logs carry
# datatype hints over reads, over Int and uninterpreted indices; U seed 43
# fails Lean without the read cases. 219 and 251 of the deeper U
# configuration failed Lean until iteration 83: Z3's rewriter evaluates a
# read through an ite over a store, (select (ite p (store a k c) b) k), to
# (ite p c (select b k)), and the read got no fact of the store branch
# (_array_helpers' _si facts).
_DEEP_U = {"index": "U", "constraints": 14, "depth": 3}
ENUM_ARRAY_SEEDS = (({"index": "U"}, 3), ({"index": "U"}, 43), ({"index": "U"}, 46),
                    ({"variables": 3, "constraints": 16, "depth": 3}, 40), (_DEEP_U, 219), (_DEEP_U, 251))


# Pinned unsatisfiable seeds of random_enum_array_instance with constant
# arrays and their default values. On iteration 83's macOS build each
# failed Lean before one of the rewriter's constant-array evaluations was
# stated: 13 folds (store (const c) i (select (const c) j)) into (const c),
# 137 pushes a read into an ite of a constant array and an array constant
# and evaluates the constant's read, 178 and 222 decide (= (const c) (store
# (const c) i v)) as (= c v). (None of the 178 unsat seeds 1-300 fails
# without the cases of constant-array reads and default values; the
# documented inputs do, see test_dropped_read_cases_fail_lean.)
ENUM_CONSTANT_SEEDS = (({"constant": True}, 13), ({"constant": True}, 137), ({"constant": True}, 178),
                       ({"constant": True}, 222))


def enumeration_chain_instance(depth=8):
    """Two copies of a chain of depth Color ites over equal inputs whose outputs are said to differ.

    Stage k of copy u (and likewise of copy w) is (ite (p u<k-1>) (f
    u<k-1>) (ite (= u<k-1> green) blue (g u<k-1> red))), so every
    application of f and g has the whole chain below it as its argument.
    The refutation is euf lemmas, one per congruence, each with the
    enumeration cases of the applications it reaches.
    """
    lines = ["(set-logic ALL)", _COLOR.strip(), "(declare-fun f (Color) Color)", "(declare-fun p (Color) Bool)",
             "(declare-fun g (Color Color) Color)"]
    for copy in "uw":
        lines.append("(declare-const %s0 Color)" % copy)
        for stage in range(1, depth + 1):
            lines.append("(define-fun {0}{1} () Color (ite (p {0}{2}) (f {0}{2}) "
                         "(ite (= {0}{2} green) blue (g {0}{2} red))))".format(copy, stage, stage - 1))
    lines += ["(assert (= u0 w0))", "(assert (not (= u%d w%d)))" % (depth, depth)]
    return "\n".join(lines + ["(check-sat)"]) + "\n"


def _pigeonhole(constructors, terms):
    """A distinct of terms constants over an enumeration of constructors constructors (no check-sat)."""
    return ("(declare-datatypes () ((E %s)))\n" % " ".join("c%d" % i for i in range(constructors))
            + "".join("(declare-const v%d E)\n" % i for i in range(terms))
            + "(assert (distinct %s))" % " ".join("v%d" % i for i in range(terms)))


def _statement(text):
    return text.split("theorem unsat", 1)[1].split(": False :=", 1)[0]


def _structure(text):
    return text.split("structure Interpretation where\n", 1)[1].split("\n\n", 1)[0]


class TestEnumerationExport(unittest.TestCase):
    """The frontend, the classification, and the clause log, without Lean."""

    def test_enumerations_are_sorts_of_the_uf_fragments(self):
        for name, fragment in (("constructor_clash", "qf_uf"), ("state_machine", "qf_uf"),
                               ("mode_levels", "qf_uflia"), ("recognizers", "qf_uf"),
                               ("old_style_recognizers", "qf_uf")):
            with self.subTest(name=name):
                _, found = proof_certificate.parse_assertions(ENUM_INPUTS[name], z3.Context(), integer=True)
                self.assertEqual(found, fragment)

    def test_other_datatypes_are_rejected(self):
        cases = {
            "(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))\n(declare-const x L)\n"
            "(assert (not (= x nil)))\n(assert (= x nil))": "only enumeration datatypes",
            "(declare-datatypes ((E 1)) ((par (T) ((e1) (e2)))))\n(declare-const x (E Int))\n"
            "(assert (= x (as e1 (E Int))))": "parametric datatypes are not supported",
            # SMT-LIB 2.5 lists the parameters first, without par.
            "(declare-datatypes (T) ((E A B)))\n(declare-const x (E Int))\n"
            "(assert (= x (as B (E Int))))": "parametric datatypes are not supported",
            "(declare-datatypes ((P 0)) (((pair (fst Int) (snd Int)))))\n(declare-const x P)\n"
            "(assert ((_ is pair) x))": "only enumeration datatypes",
            # An accessor into an enumeration: the record is not one.
            _COLOR + "(declare-datatypes ((P 0)) (((mk (fst Color)))))\n(declare-const p P)\n"
            "(assert (= (fst p) red))": "only enumeration datatypes",
            # Arrays indexed by an enumeration (extensionality would have to
            # range over its finitely many values; the constant-array and
            # default-value axioms assume an infinite index sort).
            _COLOR + "(declare-const a (Array Color Int))\n"
            "(assert (not (= (select (store a red 1) red) 1)))": "unsupported sort",
            # Arrays of an enumeration as rows or indices of other arrays
            # (no field covers the reads of rows and witnesses), maps over
            # them, and the default value of an array constant.
            _COLOR + "(declare-const a (Array Int (Array Int Color)))\n"
            "(assert (= (select (select a 0) 1) red))": "unsupported sort",
            _COLOR + "(declare-const a (Array (Array Int Color) Int))\n(declare-const b (Array Int Color))\n"
            "(assert (= (select a b) 1))": "unsupported sort",
            # The default value of an array constant or application is not
            # known to be a constructor. (Constant arrays over Bool indices
            # are admitted, test_proof_to_lean_const_sort.py.)
            _COLOR + "(declare-fun f (Int) (Array Int Color))\n"
            "(assert (= (default (store (f 0) 1 red)) red))": "supported over constant arrays only",
            _COLOR + "(declare-fun g (Color) Color)\n(declare-const a (Array Int Color))\n"
            "(assert (= (select ((_ map g) a) 0) red))": "maps over arrays of an enumeration",
            _COLOR + "(declare-const a (Array Int Color))\n(declare-const b (Array Int Color))\n"
            "(assert (select ((_ map (= (Color Color) Bool)) a b) 0))": "maps over arrays of an enumeration",
            _COLOR + "(declare-const a (Array Int Color))\n"
            "(assert (= (default a) red))": "supported over constant arrays only",
            # Pigeonholes past the bounds Lean checks: six constructors (the
            # search grows exponentially), and 17 terms over three (each
            # clause over the distinct unfolds its pairwise disequalities; see
            # _PIGEONHOLE_MAX_CONSTRUCTORS).
            _pigeonhole(6, 7): "pigeonhole search under proofs",
            _pigeonhole(3, 17): "pigeonhole search under proofs",
        }
        for source, message in cases.items():
            with self.subTest(source=source):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, message):
                    proof_certificate.parse_assertions(source + "\n(check-sat)\n", z3.Context(), integer=True)

    def test_pigeonholes_within_the_bounds_are_accepted(self):
        # At the bounds, and a distinct that is not a pigeonhole (no more
        # terms than constructors) whatever its width.
        for constructors, terms in ((5, 16), (8, 8), (3, 3)):
            with self.subTest(constructors=constructors, terms=terms):
                _, found = proof_certificate.parse_assertions(_pigeonhole(constructors, terms) + "\n(check-sat)\n",
                                                              z3.Context(), integer=True)
                self.assertEqual(found, "qf_uf")

    def test_arrays_of_an_enumeration_are_admitted(self):
        for name, fragment in (("read_of_a_constant", "qf_uflia"), ("function_into_arrays", "qf_uf"),
                               ("bool_indices", "qf_uf"), ("array_indices", "qf_uflia")):
            with self.subTest(name=name):
                _, found = proof_certificate.parse_assertions(ENUM_ARRAY_INPUTS[name], z3.Context(), integer=True)
                self.assertEqual(found, fragment)
        # The legacy core rejects arrays, of an enumeration too.
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "through the clause log only"):
            proof_certificate.export_certificate(ENUM_ARRAY_INPUTS["function_into_arrays"])

    def test_constant_arrays_of_an_enumeration_are_admitted(self):
        # Over Int and Real indices, with default values of arrays built
        # from constant arrays by store and ite.
        for name, fragment in (("read_of_a_constant_store", "qf_uflia"), ("default_of_constant_arrays", "qf_uflia"),
                               ("real_indices", "qf_uflra")):
            with self.subTest(name=name):
                _, found = proof_certificate.parse_assertions(ENUM_CONSTANT_INPUTS[name], z3.Context(),
                                                              integer=True)
                self.assertEqual(found, fragment)

    def test_default_check_visits_shared_arrays_once(self):
        # Thirty ites, each over a store into the one below and that one
        # itself: as a tree the default's array has 2^30 leaves, as a DAG 61
        # nodes. The check walks the DAG (it took 150 s at 22 levels when it
        # walked the tree).
        levels = 30
        lines = [_COLOR, "(define-fun k0 () (Array Int Color) ((as const (Array Int Color)) red))"]
        for level in range(levels):
            lines.append("(declare-const p%d Bool)" % level)
            lines.append("(define-fun k%d () (Array Int Color) (ite p%d (store k%d %d green) k%d))"
                         % (level + 1, level, level, level, level))
        start = time.monotonic()
        _, found = proof_certificate.parse_assertions(
            "\n".join(lines + ["(assert (= (default k%d) blue))" % levels, "(check-sat)"]), z3.Context(),
            integer=True)
        self.assertEqual(found, "qf_uflia")
        self.assertLess(time.monotonic() - start, 10.0)

    def test_clause_log_knows_the_constructors_of_array_elements(self):
        # No term of Color occurs, only arrays of it: the replay still knows
        # its constructors (the datatype solver's case splits name them).
        context = z3.Context()
        assertions = z3.parse_smt2_string(
            _COLOR + "(declare-const a (Array Int Color))(declare-const b (Array Int Color))(assert (= a b))",
            ctx=context)
        terms = proof_clause_log._Terms(context, list(assertions))
        self.assertEqual(terms.enumerations, {"Color"})
        self.assertEqual(terms.build("blue").decl().kind(), z3.Z3_OP_DT_CONSTRUCTOR)
        self.assertEqual(str(terms.build([["_", "is", "red"], "blue"])), "is(red, blue)")

    def test_the_legacy_core_rejects_enumerations_explicitly(self):
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "through the clause log only"):
            proof_certificate.export_certificate(ENUM_INPUTS["constructor_clash"])

    def test_replay_keys_tell_constructors_apart(self):
        # The structural key of an atom names its constructors and the
        # constructor of a recognizer; (= x red) and (= x blue) used to share
        # one, so unit propagation took one for the other.
        context = z3.Context()
        assertions = z3.parse_smt2_string(
            _COLOR + "(declare-const x Color)(assert (= x red))(assert (= x blue))"
                     "(assert ((_ is red) x))(assert ((_ is blue) x))", ctx=context)
        normalizer = proof_clause_log._Normalizer()
        keys = [normalizer.key(assertion) for assertion in assertions]
        self.assertEqual(len(set(keys)), 4)
        # is-red and (_ is red) are two declarations of one predicate.
        old_style = z3.parse_smt2_string(_COLOR + "(declare-const x Color)(assert (is-red x))", ctx=context)[0]
        self.assertEqual(old_style.decl().kind(), z3.Z3_OP_DT_RECOGNISER)
        self.assertEqual(normalizer.key(old_style), keys[2])

    def test_clause_log_reads_recognizers_and_unused_constructors(self):
        context = z3.Context()
        assertions = z3.parse_smt2_string(_COLOR + "(declare-const x Color)(assert ((_ is red) x))", ctx=context)
        terms = proof_clause_log._Terms(context, list(assertions))
        self.assertTrue(terms.build([["_", "is", "red"], "x"]).eq(assertions[0]))
        blue = terms.build("blue")
        self.assertEqual(str(blue), "blue")
        self.assertEqual(blue.decl().kind(), z3.Z3_OP_DT_CONSTRUCTOR)
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "unsupported application head"):
            terms.build([["_", "is", "purple"], "x"])

    def test_root_distinct_over_too_few_values_logs_case_splits(self):
        # The C++ fix: with proofs, a root distinct with more arguments than
        # the enumeration has values is clausified pairwise (before, z3 logged
        # an empty clause with an empty tseitin hint), and the datatype
        # solver's case splits refute it.
        if not _z3_available():
            self.skipTest("the z3 executable is required for the clause log")
        commands, _, _ = proof_certificate.query_snapshot(ENUM_INPUTS["pigeonhole"])
        log = proof_clause_log.run_clause_log(proof_certificate.default_z3_executable(), commands)
        self.assertIn("(declare-fun datatype", log)
        self.assertIn("(assume (not ", log)


class TestEnumerationValidation(unittest.TestCase):
    """The encoding and the reconstructor's checks against the input, without Lean."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")
        cls.source = ENUM_INPUTS["function_into_enumeration"]
        cls.certificate = proof_certificate.export_clause_log_certificate(cls.source)

    def test_interpretation_states_the_enumeration(self):
        text = proof_to_lean.reconstruct(self.source, self.certificate)
        structure = _structure(text)
        self.assertIn("  ctors : Nat -> U\n", structure)
        self.assertIn("  enum_distinct : (And (Not (ctors 0 = ctors 1)) (And (Not (ctors 0 = ctors 2)) "
                      "(Not (ctors 1 = ctors 2))))", structure)
        self.assertIn("  enum_fcases_0 : forall _args : List U, (Or (funs 0 _args = ctors 0) "
                      "(Or (funs 0 _args = ctors 1) (funs 0 _args = ctors 2)))", structure)
        self.assertIn('-- Enumeration "Color" is part of _m.U with constructors "red", "green", "blue", '
                      '_m.ctors 0 to 2', text)
        self.assertIn('-- Uninterpreted sort "U" is the type _m.U', text)

    def test_interpretation_states_the_cases_of_array_reads(self):
        # Every read of an array constant, at every index of the Lean index
        # type, and of a function's array value is one of the constructors.
        expected = {
            "read_of_a_constant": "  enum_acases_0 : forall _i : Int, (Or (arrs_iu 0 _i = ctors 0) "
                                  "(Or (arrs_iu 0 _i = ctors 1) (arrs_iu 0 _i = ctors 2)))\n",
            "function_into_arrays": "  enum_afcases_0 : forall _args : List U, forall _i : U, "
                                    "(Or (arrs_funs 0 _args _i = ctors 0) (Or (arrs_funs 0 _args _i = ctors 1) "
                                    "(arrs_funs 0 _args _i = ctors 2)))\n",
            "bool_indices": "  enum_acases_0 : forall _i : Prop, (Or (arrs_bu 0 _i = ctors 0) "
                            "(Or (arrs_bu 0 _i = ctors 1) (arrs_bu 0 _i = ctors 2)))\n",
        }
        for name, field in expected.items():
            with self.subTest(name=name):
                source = ENUM_ARRAY_INPUTS[name]
                text = proof_to_lean.reconstruct(source, proof_certificate.export_clause_log_certificate(source))
                self.assertIn(field, _structure(text) + "\n")
                self.assertIn("private theorem _cases_store", text)
        # A read of a store is proved from the cases below it.
        source = ENUM_ARRAY_INPUTS["read_of_a_store"]
        text = proof_to_lean.reconstruct(source, proof_certificate.export_clause_log_certificate(source))
        self.assertRegex(text, r"have _ec\d+ : \(Or \(\(\(_select .*:= \(_cases_store .*\(_m\.enum_acases_0 ")
        # Arrays of other element sorts get no such field or theorem.
        source = ENUM_INPUTS["predicate_and_ite"]
        text = proof_to_lean.reconstruct(source, proof_certificate.export_clause_log_certificate(source))
        self.assertNotIn("enum_acases", text)
        self.assertNotIn("_cases_store", text)

    def test_cases_of_constant_arrays_and_default_values(self):
        # A read of a store over a constant array is proved from the
        # constant's value; a default value through the stores and ites
        # down to constant arrays.
        expected = {"read_of_a_constant_store": ("(_cases_store ", "(_cases_const "),
                    "default_of_constant_arrays": ("(_cases_ite ", "(_cases_default_store ", "(_cases_default_const ")}
        for name, proofs in expected.items():
            with self.subTest(name=name):
                source = ENUM_CONSTANT_INPUTS[name]
                text = proof_to_lean.reconstruct(source, proof_certificate.export_clause_log_certificate(source))
                self.assertIn("private theorem _cases_default_store", text)
                facts = "\n".join(line for line in text.split("\n") if line.lstrip().startswith("have _ec"))
                for proof in proofs:
                    self.assertIn(proof, facts)
        # Without constant arrays the theorems are not stated.
        source = ENUM_ARRAY_INPUTS["read_of_a_store"]
        text = proof_to_lean.reconstruct(source, proof_certificate.export_clause_log_certificate(source))
        self.assertNotIn("_cases_const", text)

    def test_unused_constructors_are_part_of_the_cases(self):
        # The assertions of constructor_clash never name blue, but a value
        # of Color may be blue: the cases list every constructor of the
        # input, whether or not the proof names it.
        source = ENUM_INPUTS["constructor_clash"]
        structure = _structure(proof_to_lean.reconstruct(
            source, proof_certificate.export_clause_log_certificate(source)))
        self.assertIn("  enum_cases_0 : (Or (elems 0 = ctors 0) (Or (elems 0 = ctors 1) (elems 0 = ctors 2)))",
                      structure)

    def test_constructors_are_checked_against_the_input(self):
        # The assertions of function_into_enumeration name no constructor, so
        # the proof's constructors are checked against the input's
        # declaration of Color alone.
        tampered = copy.deepcopy(self.certificate)
        constructors = [d for d in tampered["declarations"] if d["kind"] == z3.Z3_OP_DT_CONSTRUCTOR]
        self.assertTrue(constructors)
        constructors[0]["name"] = "purple"
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError,
                                    "not a constructor of the input's enumeration Color: purple"):
            proof_to_lean.reconstruct(self.source, tampered)
        # Constructors are told apart by name: red for blue changes an assertion.
        source = ENUM_INPUTS["constructor_clash"]
        tampered = proof_certificate.export_clause_log_certificate(source)
        for declaration in tampered["declarations"]:
            if declaration["kind"] == z3.Z3_OP_DT_CONSTRUCTOR and declaration["name"] == "red":
                declaration["name"] = "blue"
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "do not match the original input"):
            proof_to_lean.reconstruct(source, tampered)

    def test_recognizers_are_checked_against_the_input(self):
        source = ENUM_INPUTS["recognizers"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        recognizers = [d for d in certificate["declarations"] if d["kind"] == z3.Z3_OP_DT_IS]
        self.assertEqual({d["name"] for d in recognizers}, {"A", "B"})
        for name, message in (("C", "not a constructor of the input's enumeration T: C"),
                              ("B", "do not match the original input")):
            tampered = copy.deepcopy(certificate)
            next(d for d in tampered["declarations"] if d["kind"] == z3.Z3_OP_DT_IS and d["name"] == "A")[
                "name"] = name
            with self.subTest(name=name):
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, message):
                    proof_to_lean.reconstruct(source, tampered)
        tampered = copy.deepcopy(certificate)
        next(d for d in tampered["declarations"] if d["kind"] == z3.Z3_OP_DT_IS)["domain"] = ["Bool"]
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "invalid enumeration recognizer"):
            proof_to_lean.reconstruct(source, tampered)

    def test_a_constructor_cannot_change_its_sort(self):
        tampered = copy.deepcopy(self.certificate)
        tampered["declarations"].append({"kind": z3.Z3_OP_DT_CONSTRUCTOR, "name": "red", "domain": [],
                                         "range": "U", "parameters": []})
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "unused declaration|two sorts"):
            proof_to_lean.reconstruct(self.source, tampered)

    def test_enumeration_cases_of_applications_are_stated_folded(self):
        # The cases of an application of an enumeration sort are stated over
        # its arguments' definitions, before the lemma's unfold, and
        # reverted with the gates (_folded_enumeration_cases). Written out,
        # every application's argument list repeated the chain below it in
        # full: the euf lemmas of enumeration_chain_instance(8) were 26.7 MB
        # (27.2 MB of Lean, which the 12 GB watchdog stopped after 288 s).
        source = enumeration_chain_instance(8)
        certificate = proof_certificate.export_clause_log_certificate(source)
        graph = proof_to_lean._validate_graph(source, certificate)
        text = proof_to_lean.reconstruct(source, certificate)
        lemmas = re.findall(r"\nprivate theorem th_lemma_\d+ (.*?)\n\n", text, re.S)
        cases = re.findall(r"have _ec(\d+) (.*)", "\n".join(lemmas))
        applications = [(int(node), fact) for node, fact in cases if "enum_fcases" in fact]
        self.assertGreater(len(applications), 100)
        for node, fact in applications:
            self.assertEqual(graph.kind(node), z3.Z3_OP_UNINTERPRETED)
            arguments = ", ".join("(term_%d _atoms _m)" % argument for argument in graph.arguments(node))
            self.assertRegex(fact, r"^:= _m\.enum_fcases_\d+ \[%s\]$" % re.escape(arguments))
        for lemma in lemmas:
            names = re.findall(r"have (_ec\d+) := _m\.enum_fcases_", lemma)
            if names:
                reverts = [line.split()[1:] for line in lemma.split("\n") if line.lstrip().startswith("revert ")]
                self.assertEqual(len(reverts), 1, lemma)
                self.assertLessEqual(set(names), set(reverts[0]), lemma)
        self.assertLess(sum(len(lemma) for lemma in lemmas), 200000)

    def test_datatype_lemmas_are_enumeration_clauses(self):
        # none_of_the_constructors is refuted by exhaustiveness alone, which
        # only the datatype solver knows.
        source = ENUM_INPUTS["none_of_the_constructors"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        self.assertIn("datatype", _hints(certificate))
        graph = proof_to_lean._validate_graph(source, certificate)
        proof_to_lean._bind_input(source, graph, certificate["fragment"])
        lemma = next(node for node in range(len(graph.nodes))
                     if graph.decl(node).name == "th-lemma" and graph.decl(node).parameters == ("datatype",))
        proof_to_lean._check_th_lemma(graph, lemma)
        # The same lemma over an input whose sort is not an enumeration.
        graph.enumerations.clear()
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "not an enumeration equality"):
            proof_to_lean._check_th_lemma(graph, lemma)


def _check_in_lean(test, source, query=None, certificate=None):
    """Export through the clause log, reconstruct, and kernel-check once; return the certificate."""
    if certificate is None:
        certificate = proof_certificate.export_clause_log_certificate(source, query=query)
    text, report = lean_test_support.check(test, source, certificate)
    test.assertEqual(_statement(text).count("    (_h"), len(certificate["assertions"]))
    test.assertIn("  ctors : Nat -> U\n", _structure(text))
    test.assertTrue(_STANDARD_AXIOMS in report or "does not depend on any axioms" in report, report)
    return certificate


class TestEnumerationLeanIntegration(unittest.TestCase):
    """End-to-end through the clause log: certificate, Lean reconstruction, kernel check."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")

    def test_documented_inputs_verify(self):
        certificates = {name: proof_certificate.export_clause_log_certificate(source)
                        for name, source in ENUM_INPUTS.items()}
        lean_test_support.prefetch((ENUM_INPUTS[name], certificate) for name, certificate in certificates.items())
        hints = set()
        for name, source in ENUM_INPUTS.items():
            with self.subTest(name=name):
                hints |= _hints(_check_in_lean(self, source, certificate=certificates[name]))
        self.assertIn("datatype", hints)

    def test_z3test_incremental_pigeonhole_verifies(self):
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "sat: no unsat proof exists"):
            proof_certificate.export_clause_log_certificate(Z3_14, query=0)
        _check_in_lean(self, Z3_14, query=1)

    @lean_test_support.slow("the largest pigeonhole the exporter accepts (about 2 MB of Lean, 1.5 GB)")
    def test_the_largest_accepted_pigeonhole_verifies(self):
        source = _pigeonhole(proof_certificate._PIGEONHOLE_MAX_CONSTRUCTORS,
                             proof_certificate._PIGEONHOLE_MAX_ARGUMENTS) + "\n(check-sat)\n"
        _check_in_lean(self, source)

    def test_pinned_random_instances_verify(self):
        sources = []
        for arguments, seed in ENUM_SEEDS:
            source = random_enum_instance(seed, **arguments)
            self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % seed)
            sources.append((arguments, seed, source, proof_certificate.export_clause_log_certificate(source)))
        lean_test_support.prefetch((source, certificate) for _, _, source, certificate in sources)
        for arguments, seed, source, certificate in sources:
            with self.subTest(seed=seed, options=sorted(arguments)):
                _check_in_lean(self, source, certificate=certificate)

    def test_enumeration_ite_chains_verify(self):
        # Two eight-level chains of Color ites through f and g: 27.2 MB of
        # Lean with the enumeration cases written out (the watchdog stopped
        # it at 12.6 GB), 0.6 MB and about a second with them folded.
        _check_in_lean(self, enumeration_chain_instance(8))

    def test_documented_array_inputs_verify(self):
        certificates = {name: proof_certificate.export_clause_log_certificate(source)
                        for name, source in ENUM_ARRAY_INPUTS.items()}
        lean_test_support.prefetch((ENUM_ARRAY_INPUTS[name], certificate)
                                   for name, certificate in certificates.items())
        hints = set()
        for name, source in ENUM_ARRAY_INPUTS.items():
            with self.subTest(name=name):
                hints |= _hints(_check_in_lean(self, source, certificate=certificates[name]))
        self.assertIn("datatype", hints)

    def test_pinned_random_array_instances_verify(self):
        sources = []
        for arguments, seed in ENUM_ARRAY_SEEDS:
            source = random_enum_array_instance(seed, **arguments)
            self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % seed)
            sources.append((arguments, seed, source, proof_certificate.export_clause_log_certificate(source)))
        lean_test_support.prefetch((source, certificate) for _, _, source, certificate in sources)
        for arguments, seed, source, certificate in sources:
            with self.subTest(seed=seed, options=sorted(arguments.items())):
                _check_in_lean(self, source, certificate=certificate)

    def test_documented_constant_inputs_verify(self):
        certificates = {name: proof_certificate.export_clause_log_certificate(source)
                        for name, source in ENUM_CONSTANT_INPUTS.items()}
        lean_test_support.prefetch((ENUM_CONSTANT_INPUTS[name], certificate)
                                   for name, certificate in certificates.items())
        hints = set()
        for name, source in ENUM_CONSTANT_INPUTS.items():
            with self.subTest(name=name):
                hints |= _hints(_check_in_lean(self, source, certificate=certificates[name]))
        self.assertIn("datatype", hints)

    def test_pinned_random_constant_instances_verify(self):
        sources = []
        for arguments, seed in ENUM_CONSTANT_SEEDS:
            source = random_enum_array_instance(seed, **arguments)
            self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % seed)
            self.assertIn("(as const (Array Int Color))", source)
            sources.append((arguments, seed, source, proof_certificate.export_clause_log_certificate(source)))
        lean_test_support.prefetch((source, certificate) for _, _, source, certificate in sources)
        for arguments, seed, source, certificate in sources:
            with self.subTest(seed=seed):
                _check_in_lean(self, source, certificate=certificate)

    def test_dropped_read_cases_fail_lean(self):
        # The datatype lemmas over reads (and default values) rest on their
        # cases: without them Lean rejects each file (the constants keep
        # their fields). A read of a constant array is not among them: its
        # value is also a fact of the array lemmas (_select_const), from
        # which grind finds the cases of read_of_a_constant_store alone.
        names = ("read_of_a_constant", "read_of_a_store", "read_of_an_ite", "function_into_arrays",
                 "default_of_constant_arrays")
        inputs = dict(ENUM_ARRAY_INPUTS, **ENUM_CONSTANT_INPUTS)
        tampered = []
        for name in names:
            source = inputs[name]
            lines = proof_to_lean.reconstruct(source, proof_certificate.export_clause_log_certificate(source)).split("\n")
            kept = [line for line in lines
                    if not (line.lstrip().startswith("have _ec")
                            and ("_select" in line.split(":=", 1)[0] or "_default" in line.split(":=", 1)[0]))]
            self.assertLess(len(kept), len(lines), name)
            tampered.append("\n".join(kept))
        for name, text in zip(names, tampered):
            with self.subTest(name=name):
                with tempfile.TemporaryDirectory() as directory:
                    output = Path(directory) / "tampered.lean"
                    output.write_text(text)
                    result = lean_test_support.run_check_lean(output)
                report = result.stdout + result.stderr
                self.assertNotEqual(result.returncode, 0, report)
                errors = [line for line in report.split("\n") if "error:" in line]
                self.assertTrue(errors, report)
                for error in errors:
                    self.assertIn("`grind` failed", error)

    def test_a_dropped_enumeration_fact_fails_lean(self):
        # The datatype lemma of none_of_the_constructors rests on the cases
        # field: without it Lean rejects the file, so the facts are needed
        # and not decoration.
        source = ENUM_INPUTS["none_of_the_constructors"]
        text = proof_to_lean.reconstruct(source, proof_certificate.export_clause_log_certificate(source))
        self.assertIn("  have _ec", text)
        tampered = "\n".join(line for line in text.split("\n") if not line.startswith("  have _ec"))
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "tampered.lean"
            output.write_text(tampered)
            result = lean_test_support.run_check_lean(output)
        report = result.stdout + result.stderr
        self.assertNotEqual(result.returncode, 0, report)
        errors = [line for line in report.split("\n") if "error:" in line]
        self.assertTrue(errors, report)
        for error in errors:
            self.assertIn("`grind` failed", error)


if __name__ == "__main__":
    unittest.main()
