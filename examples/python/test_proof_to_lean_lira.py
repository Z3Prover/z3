############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Tests for the QF_LIRA slice of the Lean reconstruction: Int and Real
# variables side by side, each sort valued on its own (_ivars into Int,
# _vars into Rat), and related by to_real (Int.cast into Rat), to_int
# (Rat.floor), and is_int. Validation without Lean, and end-to-end
# checks through both proof cores that need the z3 executable and the
# pinned Lean toolchain.
############################################
import collections
import copy
from pathlib import Path
import random
import re
import sys
import unittest
from unittest import mock

import z3

_EXAMPLES = Path(__file__).resolve().parent
sys.path.insert(0, str(_EXAMPLES))
import proof_certificate
import proof_clause_log
import lean_test_support
import proof_to_lean
from test_proof_to_lean_lia import LIA_INPUTS, _STANDARD_AXIOMS, _hints, _parameters, _th_lemma_nodes, _z3_available

# Documented QF_LIRA inputs: each refutation needs atoms of both sorts, tied
# together by Boolean structure, while every theory lemma stays within one
# sort (Z3 never relates Int and Real atoms without a conversion).
LIRA_INPUTS = {
    # A Real conflict forces p, under which an Int conflict follows.
    "lira_case_split": """(set-logic QF_LIRA)
(declare-const x Real)
(declare-const y Real)
(declare-const n Int)
(declare-const m Int)
(declare-const p Bool)
(assert (or p (> x (+ y 1.5))))
(assert (or (not p) (> (* 2 n) (+ (* 2 m) 1))))
(assert (< x y))
(assert (< n (+ m 1)))
(check-sat)
""",
    # Parity: 2a = 2b + 1 has a Real solution but no Int one (a cut).
    "lira_parity": """(set-logic QF_LIRA)
(declare-const x Real)
(declare-const a Int)
(declare-const b Int)
(declare-const q Bool)
(assert (= q (> x 0.5)))
(assert (=> q (= (* 2 a) (+ (* 2 b) 1))))
(assert (=> (not q) (< x (- 1.0))))
(assert (> x (- 0.75)))
(check-sat)
""",
    # One condition selects an Int and a Real ite branch at once.
    "lira_ite": """(set-logic QF_LIRA)
(declare-const x Real)
(declare-const n Int)
(declare-const p Bool)
(assert (= x (ite p 1.5 2.5)))
(assert (= n (ite p 3 4)))
(assert (or (> x 2.0) (> n 3)))
(assert (or (< x 2.0) (< n 4)))
(check-sat)
""",
    # abs over both sorts, Real division by a numeral, and Int mod.
    "lira_abs_mod": """(set-logic QF_LIRA)
(declare-const x Real)
(declare-const n Int)
(assert (or (> (abs x) 3.0) (> (abs n) 3) (= (mod n 2) 1)))
(assert (< (- 1.5) (/ x 2.0) 1.5))
(assert (< (- 3) n 3))
(assert (distinct n (- 1) 1))
(check-sat)
""",
    # An Int ite over a Real condition: the farkas lemmas over the ite are
    # Int steps, the condition's Real atoms not theirs.
    "lira_int_ite_over_real_condition": """(set-logic QF_LIRA)
(declare-const x Real)
(declare-const y Real)
(declare-const a Int)
(declare-const b Int)
(assert (< (+ (ite (> x y) a b) 1) a))
(assert (< a (+ b 1)))
(check-sat)
""",
    # A Real ite over an Int condition, the other way round.
    "lira_real_ite_over_int_condition": """(set-logic QF_LIRA)
(declare-const n Int)
(declare-const m Int)
(declare-const u Real)
(declare-const v Real)
(assert (< (+ (ite (> n m) u v) 1.0) u))
(assert (< u (+ v 1.0)))
(check-sat)
""",
}
# The ite inputs whose conditions are over the other sort, with the ite's sort.
_OTHER_SORT_CONDITIONS = {"lira_int_ite_over_real_condition": "Int", "lira_real_ite_over_int_condition": "Real"}


# Documented inputs relating the sorts through to_real: theory lemmas over
# Int and Real atoms at once, proved with the Int atoms cast into Rat and
# the Real atoms over Int terms alone tied to Int atoms
# (proof_to_lean._cast_facts).
CAST_INPUTS = {
    # x = n, 0 < x < 1: one farkas lemma over both sorts, which refutes only
    # once the Int literal (not (<= n 0)) is tightened to n >= 1.
    "cast_tightening": """(set-logic QF_LIRA)
(declare-const x Real)
(declare-const n Int)
(assert (= x (to_real n)))
(assert (< 0.0 x))
(assert (< x 1.0))
(check-sat)
""",
    # A sum under to_real next to a Real offset, and an Int ite of numerals
    # in a Real position, which Z3 reads as (to_real (ite p 1 2)) (logic ALL).
    "cast_sum_ite": """(declare-const x Real)
(declare-const y Real)
(declare-const n Int)
(declare-const m Int)
(declare-const p Bool)
(assert (= x (+ (to_real (+ n m)) 0.5)))
(assert (or (> x 4.0) (< n 0) (> y 2.5)))
(assert (<= (+ n m) 3))
(assert (>= n 0))
(assert (= y (ite p 1 2)))
(check-sat)
""",
    # 2n = 2m + 1 over the casts: refuted by integrality alone, a cut over
    # a Real atom whose linear form ranges over Int terms.
    "cast_parity_cut": """(set-logic QF_LIRA)
(declare-const n Int)
(declare-const m Int)
(assert (= (* 2.0 (to_real n)) (+ (* 2.0 (to_real m)) 1.0)))
(check-sat)
""",
    # div, mod, and abs of Int terms under to_real.
    "cast_div_mod_abs": """(set-logic QF_LIRA)
(declare-const x Real)
(declare-const n Int)
(assert (= x (to_real (+ (div n 3) (mod n 3)))))
(assert (or (< x 2.5) (> x 3.5) (<= (abs (to_real n)) 0.5)))
(assert (= n 5))
(check-sat)
""",
}


# Documented inputs taking floors of Real terms: to_int is Rat.floor, an
# Int atom bounded by the core lemmas Rat.floor_le and Rat.lt_floor_add_one
# (Z3's two arith axioms for it), and (is_int t) is t = ((Rat.floor t : Int)
# : Rat) (proof_to_lean._cast_facts).
FLOOR_INPUTS = {
    # n = floor x with x > 5/2 forces n >= 2: a farkas lemma over both
    # sorts through the upper floor axiom.
    "floor_bounds": """(declare-const x Real)
(declare-const n Int)
(assert (= n (to_int x)))
(assert (> x 2.5))
(assert (< n 2))
""",
    # An integer strictly between 5/2 and 3: the Real atom (<= 3.0 x) over
    # the floor alone is tightened through its Int counterpart.
    "is_int_window": """(declare-const x Real)
(assert (is_int x))
(assert (> x 2.5))
(assert (< x 3.0))
""",
    "not_is_int": """(declare-const x Real)
(assert (not (is_int x)))
(assert (= (* 2.0 x) 6.0))
""",
    # The floor of a sum and of a scaled term; the legacy core rewrites
    # inside the floors (congruence through to_int).
    "floor_sum": """(set-logic QF_LIRA)
(declare-const x Real)
(declare-const n Int)
(assert (= n (to_int (+ x 0.5))))
(assert (>= x 1.25))
(assert (<= x 1.4))
(assert (not (= n 1)))
""",
    "floor_half": """(set-logic QF_LIRA)
(declare-const x Real)
(declare-const n Int)
(assert (= n (to_int (/ x 2.0))))
(assert (< (* 2 n) 3))
(assert (> x 4.0))
""",
    # z3test regressions/smt2/issue-1608.smt2: Z3 rewrites (is_int (+ x 1))
    # to (is_int x), proved through floor (x + 1) = floor x + 1.
    "is_int_shift": """(declare-const x Real)
(assert (is_int x))
(assert (not (is_int (+ x 1))))
""",
    # to_int undoes to_real, also below zero.
    "floor_round_trip": """(set-logic QF_LIRA)
(declare-const n Int)
(declare-const x Real)
(declare-const y Real)
(assert (= x (to_real n)))
(assert (or (not (= (to_int x) n)) (and (< (- 2.0) y (- 1.0)) (not (= (to_int y) (- 2))))))
""",
    # The floor of an integer-valued term is that term (Rat.floor_intCast);
    # the floor bounds alone leave floor (n) = n - 1 open.
    "is_int_of_int": """(declare-const n Int)
(assert (not (is_int (to_real n))))
""",
    "is_int_of_int_sum": """(declare-const n Int)
(declare-const m Int)
(assert (not (is_int (+ (to_real n) (* 2.0 (to_real m)) 3.0))))
""",
    # Integrality cuts through floors of Real variables
    # (proof_to_lean._projection_facts): x = 2 floor(x/2) + 1 has Real
    # solutions only, and 1/4 is no integer.
    "is_int_parity": """(set-logic QF_LIRA)
(declare-const x Real)
(assert (is_int x))
(assert (is_int (/ x 2.0)))
(assert (or (= x 3.0) (= x 5.0)))
""",
    "is_int_quarter": """(set-logic QF_LIRA)
(declare-const x Real)
(declare-const p Bool)
(assert (is_int x))
(assert (= (ite p x 0.25) 0.25))
(assert p)
""",
}


def random_floor_instance(seed, variables=3, constraints=10):
    """A random QF_LIRA problem over floors of Real terms (to_int, is_int), or None when it is satisfiable."""
    generator = random.Random(seed)
    lines = ["(set-logic QF_LIRA)"]
    lines += ["(declare-const n%d Int)" % i for i in range(variables)]
    lines += ["(declare-const x%d Real)" % i for i in range(variables)]
    lines += ["(declare-const p%d Bool)" % i for i in range(2)]

    def real_numeral(quarters):
        text = "%d.%s" % (abs(quarters) // 4, ("0", "25", "5", "75")[abs(quarters) % 4])
        return text if quarters >= 0 else "(- %s)" % text

    def integer_numeral(value):
        return "%d" % value if value >= 0 else "(- %d)" % -value

    def real_term():
        roll, v = generator.random(), generator.randrange(variables)
        if roll < 0.5:
            return "x%d" % v
        if roll < 0.7:
            return "(+ x%d %s)" % (v, real_numeral(generator.randint(-6, 6)))
        if roll < 0.85:
            return "(* %s x%d)" % (generator.choice(["0.5", "2.0", "(- 1.0)", "1.5"]), v)
        return "(ite p%d x%d %s)" % (generator.randrange(2), v, real_numeral(generator.randint(-6, 6)))

    def int_term():
        return "(to_int %s)" % real_term() if generator.random() < 0.6 else "n%d" % generator.randrange(variables)

    def atom():
        roll = generator.random()
        relation = generator.choice(["<=", ">=", "<", ">", "="])
        if roll < 0.15:
            return "(is_int %s)" % real_term()
        if roll < 0.55:
            return "(%s %s %s)" % (relation, int_term(), integer_numeral(generator.randint(-4, 4)))
        if roll < 0.75:
            return "(%s %s (+ %s %s))" % (relation, int_term(), int_term(), integer_numeral(generator.randint(-2, 2)))
        return "(%s %s %s)" % (relation, real_term(), real_numeral(generator.randint(-16, 16)))

    def literal():
        if generator.random() < 0.15:
            return generator.choice(["p0", "p1", "(not p0)", "(not p1)"])
        return atom() if generator.random() < 0.8 else "(not %s)" % atom()

    # A small box for the Real variables, where Z3 decides is_int quickly.
    lines += ["(assert (<= (- 4.0) x%d 4.0))" % i for i in range(variables)]
    for _ in range(constraints):
        roll = generator.random()
        if roll < 0.4:
            lines.append("(assert (or %s %s))" % (literal(), literal()))
        elif roll < 0.55:
            lines.append("(assert (or %s %s %s))" % (literal(), literal(), literal()))
        else:
            lines.append("(assert %s)" % atom())
    lines.append("(check-sat)")
    source = "\n".join(lines) + "\n"
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set("timeout", 5000)
    solver.from_string(source)
    return source if solver.check() == z3.unsat else None


# Unsatisfiable seeds of random_floor_instance: 39 relates floors of terms
# differing by an integer on both cores and rewrites inside a legacy floor,
# 43 has a clause-log rewrite of (is_int (+ x 1.0)) to (is_int x), 73
# bound hints and a legacy floor shift, 135 an is_int atom the clause log
# keeps, with its definition as arith hints; 5 and 54 integrality cuts
# through floors of Real variables on both cores (_projection_facts).
FLOOR_SEEDS = (39, 43, 73, 135, 5, 54)


def random_cast_instance(seed, variables=3, constraints=10):
    """A random QF_LIRA problem whose Real atoms range over to_real of Int terms, or None when it is satisfiable."""
    generator = random.Random(seed)
    lines = ["(set-logic QF_LIRA)"]
    lines += ["(declare-const n%d Int)" % i for i in range(variables)]
    lines += ["(declare-const x%d Real)" % i for i in range(variables)]
    lines += ["(declare-const p%d Bool)" % i for i in range(2)]

    def coefficient():
        value = generator.choice([-3, -2, -1, 1, 2, 3])
        return "%d" % value if value > 0 else "(- %d)" % -value

    def real_numeral(halves):
        text = "%d.%d" % (abs(halves) // 2, 5 * (abs(halves) % 2))
        return text if halves >= 0 else "(- %s)" % text

    def int_term():
        roll, v = generator.random(), generator.randrange(variables)
        if roll < 0.5:
            return "n%d" % v
        if roll < 0.8:
            w = generator.randrange(variables)
            return "(+ n%d (* %s n%d))" % (v, coefficient(), w)
        return "(ite p%d n%d %s)" % (generator.randrange(2), v, integer_numeral(generator.randint(-2, 2)))

    def real_term():
        return "(to_real %s)" % int_term() if generator.random() < 0.6 else "x%d" % generator.randrange(variables)

    def integer_numeral(value):
        return "%d" % value if value >= 0 else "(- %d)" % -value

    def atom():
        roll = generator.random()
        relation = generator.choice(["<=", ">=", "<", ">", "="])
        if roll < 0.6:
            terms = ["(* %s.0 %s)" % (generator.choice([1, 2, 3]), real_term())
                     for _ in range(generator.randint(1, 2))]
            left = terms[0] if len(terms) == 1 else "(+ %s)" % " ".join(terms)
            return "(%s %s %s)" % (relation, left, real_numeral(generator.randint(-12, 12)))
        return "(%s %s %s)" % (relation, int_term(), integer_numeral(generator.randint(-6, 6)))

    def literal():
        if generator.random() < 0.15:
            return generator.choice(["p0", "p1", "(not p0)", "(not p1)"])
        return atom()

    for _ in range(constraints):
        roll = generator.random()
        if roll < 0.4:
            lines.append("(assert (or %s %s))" % (literal(), literal()))
        elif roll < 0.55:
            lines.append("(assert (or %s %s %s))" % (literal(), literal(), literal()))
        else:
            lines.append("(assert %s)" % atom())
    lines.append("(check-sat)")
    source = "\n".join(lines) + "\n"
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.from_string(source)
    return source if solver.check() == z3.unsat else None


# Unsatisfiable seeds of random_cast_instance: 11 and 36 have clause-log
# cuts over Real atoms of Int terms, 12 legacy congruences through to_real,
# 25 a legacy farkas lemma without coefficients over both sorts.
CAST_SEEDS = (11, 12, 25, 36)


def cast_chains_instance(depth=8, compare="real"):
    """Two Int chains of nested ites with one value, compared through to_real or under a predicate.

    The chains of test_proof_to_lean_lia.modular_chains_instance, x + 5 *
    depth and x + 10 * (depth / 2) modulo 17, each step an ite holding the
    previous step three times, so written out the depth-th one is about
    3^depth times the size of its definition. compare "real" relates their
    casts through a Real y (QF_LIRA: theory lemmas transport the Int atoms
    over the chains into Rat, the cast facts of proof_to_lean._cast_facts);
    "function" compares a Real function f of the two casts (QF_UFLIRA: Real
    atoms over the casts alone too, _integrality_fact); "predicate" compares
    a predicate p of a bound on each chain (QF_UFLIA: the excluded-middle
    facts of Boolean arguments, _folded_boolean_arguments).
    """
    logic = {"real": "QF_LIRA", "function": "QF_UFLIRA", "predicate": "QF_UFLIA"}[compare]
    lines = ["(set-logic %s)" % logic, "(declare-const x Int)"]
    for name, step, count in (("a", 5, depth), ("b", 10, depth // 2)):
        previous = "x"
        for index in range(1, count + 1):
            lines.append("(define-fun %s%d () Int (let ((s (+ %s %d))) (ite (< s 17) s (- s 17))))" % (
                name, index, previous, step))
            previous = "%s%d" % (name, index)
    first, second = "a%d" % depth, "b%d" % (depth // 2)
    lines.append("(assert (and (<= 0 x) (< x 17)))")
    if compare == "real":
        lines += ["(declare-const y Real)", "(assert (= y (to_real %s)))" % second,
                  "(assert (not (= (to_real %s) y)))" % first]
    elif compare == "function":
        lines += ["(declare-fun f (Real) Real)",
                  "(assert (not (= (f (to_real %s)) (f (to_real %s)))))" % (first, second)]
    else:
        lines += ["(declare-fun p (Bool) Bool)", "(assert (not (= (p (< %s 9)) (p (< %s 9)))))" % (first, second)]
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


def random_mixed_instance(seed, variables=3, constraints=12, ites=0.0):
    """A random QF_LIRA problem over Int and Real variables tied by Booleans, or None when it is satisfiable.

    With ites, each variable of an atom is, with that probability, an ite
    of it and another variable of its sort over an atom of the other sort.
    Without, the generator draws as it did before the option existed.
    """
    generator = random.Random(seed)
    lines = ["(set-logic QF_LIRA)"]
    lines += ["(declare-const n%d Int)" % i for i in range(variables)]
    lines += ["(declare-const x%d Real)" % i for i in range(variables)]
    lines += ["(declare-const p%d Bool)" % i for i in range(2)]

    def numeral(value, real):
        text = ("%d.%d" % (abs(value) // 2, 5 * (abs(value) % 2)) if real else "%d" % (abs(value) // 2))
        return text if value >= 0 else "(- %s)" % text

    def variable(real, index, nested):
        name = "%s%d" % ("x" if real else "n", index)
        if nested or not ites or generator.random() >= ites:
            return name
        other = "%s%d" % ("x" if real else "n", generator.randrange(variables))
        return "(ite %s %s %s)" % (atom(not real, True), name, other)

    def atom(real, nested=False):
        chosen = generator.sample(range(variables), generator.randint(1, 2))
        terms = " ".join("(* %s %s)" % (numeral(2 * generator.choice([-3, -2, -1, 1, 2, 3]), False),
                                        variable(real, v, nested)) for v in chosen)
        # Real bounds in halves, Int bounds whole, both within [-6, 6].
        bound = generator.randint(-12, 12) if real else 2 * generator.randint(-6, 6)
        return "(%s (+ %s) %s)" % (generator.choice(["<=", ">=", "<", ">", "="]), terms, numeral(bound, real))

    def literal():
        roll = generator.random()
        if roll < 0.2:
            return generator.choice(["p0", "p1", "(not p0)", "(not p1)"])
        return atom(roll < 0.6)

    for _ in range(constraints):
        roll = generator.random()
        if roll < 0.5:
            lines.append("(assert (or %s %s))" % (literal(), literal()))
        elif roll < 0.7:
            lines.append("(assert (or %s %s %s))" % (literal(), literal(), literal()))
        else:
            lines.append("(assert %s)" % atom(generator.random() < 0.5))
    lines.append("(check-sat)")
    source = "\n".join(lines) + "\n"
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.from_string(source)
    return source if solver.check() == z3.unsat else None


def wide_mixed_rewrite_instance(variables=5, ites=False):
    """Int and Real variables bounded, and one clause asking for one of them outside.

    The clause is a single rewrite over 4 * variables linear atoms of both
    sorts, more than proof_to_lean._NORMALIZED_REWRITE_ATOMS for five
    variables of each, so it takes the normalized-rewrite path, where each
    atom keeps its own sort (a strict Int atom keyed as the complement of
    the bound it contradicts, a strict Real one as it is). With ites, every
    atom adds (ite p 1 2) over Int or (ite p 1.0 2.0) over Real, and the
    bounds shift so that both values of p stay inside: the two ites have
    one value table, but each sort keeps its own representative
    (proof_to_lean._ite_representatives).
    """
    lines = ["(set-logic QF_LIRA)"] + ["(declare-const p Bool)"] * ites
    lines += ["(declare-const n%d Int)" % i for i in range(variables)]
    lines += ["(declare-const x%d Real)" % i for i in range(variables)]

    def term(variable, ite):
        return "(+ %s %s)" % (variable, ite) if ites else variable

    low, high, real_low, real_high = ("4", "5", "(- 0.5)", "5.5") if ites else ("5", "7", "0.5", "7.5")
    atoms, bounds = [], []
    for i in range(variables):
        integer, real = term("n%d" % i, "(ite p 1 2)"), term("x%d" % i, "(ite p 1.0 2.0)")
        atoms += ["(< %s 5)" % integer, "(> %s 7)" % integer, "(< %s 0.5)" % real, "(> %s 7.5)" % real]
        bounds += ["(assert (>= n%d %s))" % (i, low), "(assert (<= n%d %s))" % (i, high),
                   "(assert (>= x%d %s))" % (i, real_low), "(assert (<= x%d %s))" % (i, real_high)]
    lines.append("(assert (or %s))" % " ".join(atoms))
    lines += bounds
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


# Unsatisfiable seeds of random_mixed_instance: 12 folds an Int assertion to
# false, after which Z3 logs the rest unprocessed, to_real coercions of Int
# numerals included (see proof_clause_log._Terms.build), 17 has bound and
# euf hints, 18 an Int cut, 21 a cnf lemma.
MIXED_SEEDS = (12, 17, 18, 21)
# Unsatisfiable seeds of random_mixed_instance with ites=0.3: on iteration
# 87's macOS build each was rejected on both cores for an arithmetic step
# over both Int and Real atoms (the atoms of an ite's condition) before
# _lemma_numeric left conditions out. (The 35 unsatisfiable seeds in 1-150
# then verify on both cores, 70 of 70 runs; 13 were rejected before.)
CROSS_ITE_SEEDS = (6, 47, 129)


def _export(source, core):
    if core == "clause-log":
        return proof_certificate.export_clause_log_certificate(source)
    return proof_certificate.export_certificate(source)


class TestMixedValidation(unittest.TestCase):
    """Validation without Lean: the encoding, the fragment labels, and the per-lemma sort."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")
        cls.source = LIRA_INPUTS["lira_ite"]
        cls.certificate = _export(cls.source, "clause-log")

    def test_each_sort_has_its_own_valuation(self):
        self.assertEqual(self.certificate["fragment"], "qf_lira")
        text = proof_to_lean.reconstruct(self.source, self.certificate)
        statement = text.split("theorem unsat", 1)[1].split(": False :=", 1)[0]
        self.assertIn("(_vars : Nat -> Rat) (_ivars : Nat -> Int)", statement)
        self.assertIn("-- Real variables are encoded as Rat (_vars) and Int variables as Int (_ivars)", text)
        # x is variable 0, valued in Rat; n is variable 1, valued in Int.
        self.assertIn('-- Variable 0: "x"', text)
        self.assertIn('-- Variable 1: "n"', text)
        self.assertRegex(text, r"\(_ivars : Nat -> Int\) : Rat := _vars 0\n")
        self.assertRegex(text, r"\(_ivars : Nat -> Int\) : Int := _ivars 1\n")
        self.assertNotIn("_ivars 0", text)
        self.assertNotIn("_vars 1", text.replace("_ivars 1", ""))
        # Numerals and ites carry the sort of their node.
        self.assertIn("((3 : Int))", text)
        self.assertIn("((3 : Rat) / (2 : Rat))", text)
        self.assertIn("(@ite Int ", text)
        self.assertIn("(@ite Rat ", text)

    def test_fragment_labels_and_sorts_are_consistent(self):
        for fragment in ("qf_lia", "qf_lra", "qf_uflia"):
            relabelled = copy.deepcopy(self.certificate)
            relabelled["fragment"] = fragment
            with self.subTest(fragment=fragment):
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError,
                                            "%s certificates cannot mix Int and Real arithmetic" % fragment):
                    proof_to_lean.reconstruct(self.source, relabelled)
        # A single-sort certificate labelled qf_lira, and the mixed input
        # under a single-sort certificate.
        source = LIA_INPUTS["lia_gomory"]
        relabelled = _export(source, "clause-log")
        relabelled["fragment"] = "qf_lira"
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "contain both Int and Real arithmetic"):
            proof_to_lean.reconstruct(source, relabelled)
        relabelled["source_smt2"] = self.source
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "contain both Int and Real arithmetic"):
            proof_to_lean.reconstruct(self.source, relabelled)

    def test_theory_lemmas_over_both_sorts_are_rejected(self):
        # Retarget a farkas lemma at an assertion over atoms of both sorts:
        # the Int and Real treatments differ, so no sort is guessed.
        graph = proof_to_lean._validate_graph(self.source, self.certificate)
        mixed = next(node for node in graph.assertions
                     if {graph.decl(term).range for term in proof_to_lean._reachable(graph, node)[0]}
                     >= {"Int", "Real"})
        lemma = next(node for node in _th_lemma_nodes(self.certificate)
                     if self.certificate["declarations"][self.certificate["nodes"][node]["declaration"]]
                     ["parameters"][0] == "farkas" and node > mixed)
        tampered = copy.deepcopy(self.certificate)
        tampered["nodes"][lemma]["arguments"][-1] = mixed
        graph = proof_to_lean._validate_graph(self.source, tampered)
        for check in (proof_to_lean._check_th_lemma, proof_to_lean._opaque_tactic):
            with self.subTest(check=check.__name__):
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError,
                                            "arithmetic step over both Int and Real atoms at node %d" % lemma):
                    check(graph, lemma)

    def test_conditions_of_ites_are_not_atoms_of_the_step(self):
        # An ite is an atom of the linear forms: a farkas lemma over it takes
        # the ite's sort whatever its condition's atoms are.
        for name, numeric in _OTHER_SORT_CONDITIONS.items():
            source = LIRA_INPUTS[name]
            for core in ("clause-log", "legacy"):
                with self.subTest(name=name, core=core):
                    certificate = _export(source, core)
                    graph = proof_to_lean._validate_graph(source, certificate)
                    ites = {node for node in range(len(graph.nodes))
                            if graph.kind(node) == z3.Z3_OP_ITE and graph.is_arith(node)}
                    self.assertTrue(ites)
                    steps = [node for node in _th_lemma_nodes(certificate)
                             if graph.decl(node).parameters[0] == "farkas"
                             and ites & proof_to_lean._reachable(graph, graph.conclusion(node))[0]]
                    self.assertTrue(steps)
                    for step in steps:
                        self.assertEqual(proof_to_lean._lemma_numeric(graph, step), numeric)
                    proof_to_lean.reconstruct(source, certificate)

    def test_ites_of_one_table_keep_their_sort_in_normalized_rewrites(self):
        # (ite p 1 2) over Int and (ite p 1.0 2.0) over Real tabulate alike;
        # each atom's linear form must still range over the ite of its sort.
        source = wide_mixed_rewrite_instance(ites=True)
        text = proof_to_lean.reconstruct(source, _export(source, "clause-log"))
        self.assertIn("private theorem normalized_rewrite_", text)
        atoms = [line for line in text.splitlines() if "let _atom" in line]
        self.assertTrue(any("@ite Int" in line for line in atoms))
        self.assertTrue(any("@ite Rat" in line for line in atoms))
        for line in atoms:
            with self.subTest(atom=line):
                self.assertFalse("@ite Int" in line and ": Rat" in line, line)
                self.assertFalse("@ite Rat" in line and ": Int" in line, line)

    def test_clause_log_numerals_are_read_by_their_spelling(self):
        # The log prints numerals without a sort: in an input over both sorts
        # a decimal point marks a Real numeral, its absence an Int one.
        context = z3.Context()
        assertions, fragment = proof_certificate.parse_assertions(self.source, context, integer=True)
        self.assertEqual(fragment, "qf_lira")
        terms = proof_clause_log._Terms(context, assertions)
        self.assertTrue(z3.is_int(terms.build("3")))
        self.assertTrue(z3.is_real(terms.build("3.0")))
        self.assertEqual(terms.build(["+", "n", "1"]).sexpr(), "(+ n 1)")
        self.assertEqual(terms.build(["<=", "x", ["/", "3.0", "2.0"]]).sexpr(), "(<= x (/ 3.0 2.0))")
        # An Int numeral against a Real term is coerced by z3py, so no input
        # atom matches it.
        self.assertIn("to_real", terms.build(["<=", "x", "1"]).sexpr())


def _check_in_lean(test, source, core):
    """Export, reconstruct, and kernel-check a qf_lira input; return the certificate and the Lean text."""
    certificate = _export(source, core)
    test.assertEqual(certificate["fragment"], "qf_lira")
    text, report = lean_test_support.check(test, source, certificate)
    statement = text.split("theorem unsat", 1)[1].split(": False :=", 1)[0]
    test.assertEqual(statement.count("    (_h"), len(certificate["assertions"]))
    test.assertIn("(_vars : Nat -> Rat) (_ivars : Nat -> Int)", statement)
    test.assertTrue(_STANDARD_AXIOMS in report or "does not depend on any axioms" in report, report)
    return certificate, text


class TestMixedLeanIntegration(unittest.TestCase):
    """End-to-end: both proof cores, certificate, Lean reconstruction, kernel check."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")

    def check(self, source, core):
        return _check_in_lean(self, source, core)[0]

    def test_documented_lira_inputs_verify_on_both_cores(self):
        lean_test_support.prefetch((source, _export(source, core)) for source in LIRA_INPUTS.values()
                                    for core in ("clause-log", "legacy"))
        hints = set()
        for name, source in LIRA_INPUTS.items():
            for core in ("clause-log", "legacy"):
                with self.subTest(name=name, core=core):
                    certificate = self.check(source, core)
                    if core == "clause-log":
                        hints |= _hints(certificate)
        self.assertLessEqual({"farkas", "cut", "arith"}, hints)

    def test_wide_rewrite_over_both_sorts_verifies_through_the_normalized_path(self):
        source = wide_mixed_rewrite_instance()
        certificate = self.check(source, "clause-log")
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertIn("private theorem normalized_rewrite_", text)
        self.assertIn("_ivars 0", text)
        self.assertIn("_vars 5", text)
        # Int and Real ites of one value table, each keyed by its own sort.
        source = wide_mixed_rewrite_instance(ites=True)
        text = proof_to_lean.reconstruct(source, self.check(source, "clause-log"))
        self.assertIn("private theorem normalized_rewrite_", text)

    def test_pinned_random_instances_verify_on_both_cores(self):
        for seed in MIXED_SEEDS:
            source = random_mixed_instance(seed)
            self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % seed)
            for core in ("clause-log", "legacy"):
                with self.subTest(seed=seed, core=core):
                    self.check(source, core)

    def test_pinned_random_instances_with_ites_over_the_other_sort_verify_on_both_cores(self):
        runs = []
        for seed in CROSS_ITE_SEEDS:
            source = random_mixed_instance(seed, ites=0.3)
            self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % seed)
            self.assertRegex(source, r"\(ite \([<>=]+ \(\+ \(\* \S+ x")
            runs += [(seed, core, source, _export(source, core)) for core in ("clause-log", "legacy")]
        lean_test_support.prefetch((source, certificate) for _, _, source, certificate in runs)
        for seed, core, source, _ in runs:
            with self.subTest(seed=seed, core=core):
                self.check(source, core)


class TestCastValidation(unittest.TestCase):
    """Validation without Lean of to_real: its encoding, the cast facts, and what stays rejected."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")
        cls.source = CAST_INPUTS["cast_tightening"]
        cls.certificate = _export(cls.source, "clause-log")

    def test_to_real_is_int_cast_and_lemmas_get_cast_facts(self):
        self.assertIn({"kind": z3.Z3_OP_TO_REAL, "name": "to_real", "domain": ["Int"], "range": "Real",
                       "parameters": []}, self.certificate["declarations"])
        text = proof_to_lean.reconstruct(self.source, self.certificate)
        self.assertIn("-- Real variables are encoded as Rat (_vars) and Int variables as Int (_ivars), "
                      "to_real is Int.cast into Rat", text)
        self.assertRegex(text, r"\(_ivars : Nat -> Int\) : Rat := \(\(\(term_\d+ _atoms _vars _ivars\) : Int\) : Rat\)")
        for lemma in ("_int_cast_le", "_int_cast_lt", "_int_cast_eq"):
            self.assertIn("private theorem %s (s t : Int)" % lemma, text)
        # The farkas lemma over x = n, (not (<= n 0)), x < 1 transports the
        # Int atom into Rat and pushes the casts before grind. The fact is
        # stated over the definitions of the atom's sides, folded, reverted
        # before the lemma's unfold and introduced again after it.
        self.assertRegex(text, r"have (_c\d+) := _int_cast_le \(term_(\d+) _atoms _vars _ivars\) "
                               r"\(term_(\d+) _atoms _vars _ivars\)\n\s+revert \1\n\s+unfold [^\n]*\n\s+intro \1\n"
                               r"\s+push_cast at \*")
        self.assertIn("(_ivars : Nat -> Int) : Int := _ivars 1\n", text)
        # A certificate without to_real states none of this.
        text = proof_to_lean.reconstruct(LIRA_INPUTS["lira_ite"], _export(LIRA_INPUTS["lira_ite"], "clause-log"))
        self.assertNotIn("_int_cast_le", text)
        self.assertNotIn("push_cast", text)

    def test_facts_over_nested_ites_are_stated_folded(self):
        # The cast facts (_c), the integrality facts (_r, _q), and the
        # excluded-middle facts of Boolean arguments (_b) of lemmas over two
        # chains of eight nested Int ites are stated over the definitions,
        # folded, reverted before the lemma's unfold, and introduced again
        # after it, like the ite gates. Written out, they made 15.6 MB
        # (real), 16.0 MB (function), and 8.2 MB (predicate) of Lean text;
        # Lean ran out of memory or heartbeats.
        # The fact prefixes each certificate must state. The legacy proofs of
        # function and predicate reach none of these facts, so they are only
        # held to the size bound and the shape of any fact they state. The
        # floor bounds (_f, _u) are matched too; the structural _f names of
        # uf certificates are stated with ":", the floor bounds with ":=".
        expected = {("real", "clause-log"): {"_c"}, ("real", "legacy"): {"_c"},
                    ("function", "clause-log"): {"_c", "_q", "_r"}, ("function", "legacy"): set(),
                    ("predicate", "clause-log"): {"_b"}, ("predicate", "legacy"): set()}
        fact = r"have (_[bcuqr]\d+|_f\d+(?= :=)) (?::|:=)"
        for (compare, core), prefixes in expected.items():
            with self.subTest(compare=compare, core=core):
                source = cast_chains_instance(8, compare)
                text = proof_to_lean.reconstruct(source, _export(source, core))
                self.assertLess(len(text), 2000000)
                facts = re.findall(r"^ *(?:\| \()?%s (.*)$" % fact, text, re.M)
                self.assertLessEqual(prefixes, {name[:2] for name, _ in facts})
                for name, statement in facts:
                    self.assertNotIn("@ite", statement, name)
                    self.assertNotRegex(statement, r"_[iv]?vars \d", name)
                for block in [block for block in text.split("\n\n") if facts and "theorem" in block]:
                    names = re.findall(fact, block)
                    if names:
                        reverted = re.search(r"\n *revert ([\w ]+)\n *unfold [\w ]+\n *intro ([\w ]+)\n", block)
                        self.assertIsNotNone(reverted, block[:300])
                        self.assertEqual(reverted.group(1), reverted.group(2))
                        self.assertLessEqual(set(names), set(reverted.group(1).split()))

    def test_real_atoms_over_int_terms_are_tied_to_int_atoms(self):
        # 2n = 2m + 1 over the casts is an integer constraint: the cut gets
        # it as an Int atom, scaled to integer coefficients.
        source = CAST_INPUTS["cast_parity_cut"]
        certificate = _export(source, "clause-log")
        self.assertIn("cut", _hints(certificate))
        text = proof_to_lean.reconstruct(source, certificate)
        # Over the definitions, folded: the atom is unfolded down to the Int
        # terms of its form to be proved.
        self.assertRegex(text, r"have _r(\d+) : \(formula_\1 _atoms _vars _ivars\) <-> "
                               r"\(\(.*\(term_\d+ _atoms _vars _ivars\).*\) = \(\(0 : Int\)\)\) := "
                               r"Iff\.trans \(by unfold formula_\1 [^;]*; push_cast; grind\) Rat\.intCast_inj")

    def test_real_atoms_over_int_terms_key_by_their_meaning(self):
        # A Real atom over to_real alone is not tightened like an Int atom:
        # its key (_normalized_atom, used by wide normalized rewrites and ite
        # tables) must tighten it before taking the integer complement, so
        # -2n + 1/2 <= 0 keys as not (n <= 0), like the Int atom n >= 1.
        source = ("(set-logic QF_LIRA)\n(declare-const n Int)\n(declare-const x Real)\n"
                  "(assert (or (<= (+ (* (- 2.0) (to_real n)) 0.5) 0.0) (> x 1.0)))\n"
                  "(assert (< n 1))\n(assert (<= x 1.0))\n(assert (or (< (to_real n) 2.5) (> x 0.0)))\n"
                  "(check-sat)\n")
        for core in ("clause-log", "legacy"):
            graph = proof_to_lean._validate_graph(source, _export(source, core))
            checked = 0
            for node in range(len(graph.nodes)):
                kind, arguments = graph.kind(node), graph.arguments(node)
                if graph.is_term(node) or kind not in proof_to_lean._CAST_ATOMS or kind == z3.Z3_OP_EQ:
                    continue
                if not graph.is_arith(arguments[0]):
                    continue
                relation, terms, constant = proof_to_lean._atom_constraint(graph, node)
                if len(terms) != 1 or not graph.is_int(next(iter(terms))):
                    continue
                (relation_key, ordered, constant_key), negated = proof_to_lean._normalized_atom(
                    graph, node, lambda variable: (0, variable))
                (_, coefficient), = ordered
                for value in range(-4, 5):
                    exact = sum(c * value for c in terms.values()) + constant
                    expected = exact <= 0 if relation == "<=" else exact < 0
                    keyed = coefficient * value + constant_key
                    keyed = keyed <= 0 if relation_key == "<=" else keyed < 0
                    with self.subTest(core=core, node=node, n=value):
                        self.assertEqual(keyed != negated, expected)
                checked += 1
            self.assertGreater(checked, 0)

    def test_invalid_to_real_declarations_are_rejected(self):
        for domain, range_ in ((["Real"], "Real"), (["Int"], "Int"), (["Int", "Int"], "Real")):
            tampered = copy.deepcopy(self.certificate)
            declaration = next(d for d in tampered["declarations"] if d["name"] == "to_real")
            declaration["domain"], declaration["range"] = domain, range_
            with self.subTest(domain=domain, range=range_):
                with self.assertRaises(proof_to_lean.ReconstructionError):
                    proof_to_lean.reconstruct(self.source, tampered)

    def test_cuts_over_real_atoms_alone_are_rejected(self):
        # A cut rounds by integrality, so some literal must reach an Int
        # atom: retargeted at the assertion over the Real variable x and an
        # ite of Real sort (the step still reaches to_real under the ite),
        # the step is rejected, as the exporter rejects such a hint.
        source = """(set-logic QF_LIRA)
(declare-const n Int)
(declare-const m Int)
(declare-const x Real)
(declare-const p Bool)
(assert (or (< x (ite p (to_real n) 0.5)) (= (* 2.0 (to_real n)) (+ (* 2.0 (to_real m)) 1.0))))
(assert (>= x (ite p (to_real n) 0.5)))
"""
        certificate = _export(source, "clause-log")
        graph = proof_to_lean._validate_graph(source, certificate)
        lemma = next(node for node in _th_lemma_nodes(certificate)
                     if _parameters(certificate, node)[0] == "cut")
        target = next(node for node in graph.assertions if graph.kind(node) == z3.Z3_OP_GE)
        self.assertLess(target, lemma)
        tampered = copy.deepcopy(certificate)
        tampered["nodes"][lemma]["arguments"][-1] = target
        graph = proof_to_lean._validate_graph(source, tampered)
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError,
                                    "cut th-lemma over Real atoms alone at node %d" % lemma):
            proof_to_lean._check_th_lemma(graph, lemma)
        context = z3.Context()
        n, x = z3.Int("n", ctx=context), z3.Real("x", ctx=context)
        quarter = z3.RealVal("9/4", ctx=context)
        self.assertFalse(proof_clause_log.check_linear_hint("cut", [(1, z3.ToReal(n) == quarter)]))
        # A Real variable next to an Int term, or under a floor, may be
        # rounded through the Int term (Lean decides whether it is).
        self.assertFalse(proof_clause_log.check_linear_hint("cut", [(1, x + z3.ToReal(n) == quarter)]))
        half = x / 2
        self.assertFalse(proof_clause_log.check_linear_hint("cut", [(1, half == z3.ToReal(z3.ToInt(half)))]))
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "cut hint over Real atoms"):
            proof_clause_log.check_linear_hint("cut", [(1, x == quarter), (1, x <= 2 * x + quarter)])
        # As in the reconstructor, an Int term under a Real ite is opaque,
        # and an Int numeral is a constant, not an Int atom.
        p = z3.Bool("p", ctx=context)
        ite = z3.If(p, z3.ToReal(n), z3.RealVal("1/2", ctx=context))
        for literal in (x < ite, x + z3.ToReal(z3.IntVal(1, ctx=context)) == quarter):
            with self.subTest(literal=literal), self.assertRaisesRegex(proof_certificate.ProofExportError,
                                                                       "cut hint over Real atoms"):
                proof_clause_log.check_linear_hint("cut", [(1, literal)])


class TestFloorValidation(unittest.TestCase):
    """Validation without Lean of to_int and is_int: their encoding, the floor facts, and what stays rejected."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")
        cls.source = FLOOR_INPUTS["is_int_window"]
        cls.certificate = _export(cls.source, "clause-log")

    def test_to_int_is_rat_floor_and_lemmas_get_floor_facts(self):
        declarations = self.certificate["declarations"]
        self.assertIn({"kind": z3.Z3_OP_IS_INT, "name": "is_int", "domain": ["Real"], "range": "Bool",
                       "parameters": []}, declarations)
        self.assertIn({"kind": z3.Z3_OP_TO_INT, "name": "to_int", "domain": ["Real"], "range": "Int",
                       "parameters": []}, declarations)
        text = proof_to_lean.reconstruct(self.source, self.certificate)
        self.assertIn("-- Real variables are encoded as Rat (_vars) and Int variables as Int (_ivars), "
                      "to_real is Int.cast into Rat, to_int is Rat.floor", text)
        # is_int states its argument equal to the cast of its floor.
        self.assertIn("(((Rat.floor (term_0 _atoms _vars _ivars) : Int) : Rat) = (term_0 _atoms _vars _ivars))",
                      text)
        self.assertIn(": Int := (Rat.floor (term_", text)
        self.assertRegex(text, r"have _f(\d+) := Rat\.floor_le \(term_\1 _atoms _vars _ivars\)\n\s+have _u\1 := "
                               r"Rat\.lt_floor_add_one \(term_\1 _atoms _vars _ivars\)")
        self.assertIn("(_ivars : Nat -> Int) : Rat := _vars 0\n", text)
        # The Real atom (<= 3.0 (to_real (to_int x))) is an Int atom, cast
        # back into Rat to be tightened, over the floor's definition.
        floor = re.search(r"have _q\d+ := _int_cast_le \(.*\(term_(\d+) _atoms _vars _ivars\).*\) "
                          r"\(\(0 : Int\)\)", text)
        self.assertIsNotNone(floor)
        self.assertIn("def term_%s (_atoms : Nat -> Prop) (_vars : Nat -> Rat) (_ivars : Nat -> Int) : Int := "
                      "(Rat.floor (term_0 _atoms _vars _ivars))" % floor.group(1), text)

    def test_floors_of_terms_differing_by_an_integer_are_related(self):
        source = random_floor_instance(FLOOR_SEEDS[1])
        self.assertIsNotNone(source)
        text = proof_to_lean.reconstruct(source, _export(source, "clause-log"))
        self.assertRegex(text, r"have _d\d+_\d+ := congrArg \(fun \(_t : Int\) => \(\(_t : Int\) : Rat\)\) "
                               r"\(\(congrArg Rat\.floor \(show .* by push_cast; grind\)\)\.trans "
                               r"Rat\.floor_add_intCast\)")
        # Of the floors of x, x + 1/2, and x + 2 (the legacy certificate
        # keeps the input's terms, and the rewritten 2 + x and 1/2 + x),
        # only those differing by an integer are related.
        source = ("(declare-const x Real)\n"
                  "(assert (or (> (to_int x) (to_int (+ x 0.5))) (> (to_int x) (to_int (+ x 2.0)))))\n")
        graph = proof_to_lean._validate_graph(source, _export(source, "legacy"))
        floors = sorted({graph.arguments(node)[0] for node in range(len(graph.nodes))
                         if graph.kind(node) == z3.Z3_OP_TO_INT})
        self.assertGreaterEqual(len(floors), 3)
        indices = collections.defaultdict(int)  # every variable rendered as _vars 0
        facts = proof_to_lean._floor_shift_facts(graph, floors, indices, indices)
        self.assertTrue(any("(((((2 : Int))) : Int) : Rat)" in fact for fact in facts), facts)
        for fact in facts:
            with self.subTest(fact=fact):
                self.assertIn(fact.count("((1 : Rat) / (2 : Rat))"), (0, 2))

    def test_floor_of_an_integer_valued_term_is_that_term(self):
        source = FLOOR_INPUTS["is_int_of_int"]
        for core in ("clause-log", "legacy"):
            with self.subTest(core=core):
                text = proof_to_lean.reconstruct(source, _export(source, core))
                self.assertRegex(text, r"have _z\d+ := congrArg \(fun \(_t : Int\) => \(\(_t : Int\) : Rat\)\) "
                                       r"\(\(congrArg Rat\.floor \(show .* by push_cast; grind\)\)\.trans "
                                       r"\(Rat\.floor_intCast _\)\)")
        # Floors of Real variables get none.
        text = proof_to_lean.reconstruct(self.source, self.certificate)
        self.assertNotIn("Rat.floor_intCast", text)

    def test_floor_shift_pairs_are_capped(self):
        # 13 floors x + k/2: past the cap no pair is related, while the
        # floor of the integer-valued n + 1 is still stated.
        terms = ["(to_int (+ x %d.%d))" % (k // 2, 5 * (k % 2)) for k in range(1, 13)]
        source = ("(declare-const x Real)\n(declare-const n Int)\n(assert (or %s))\n"
                  "(assert (not (> (to_int (+ (to_real n) 1.0)) n)))\n"
                  % " ".join("(> %s 7)" % term for term in terms))
        graph = proof_to_lean._validate_graph(source, _export(source, "legacy"))
        floors = sorted({graph.arguments(node)[0] for node in range(len(graph.nodes))
                         if graph.kind(node) == z3.Z3_OP_TO_INT})
        self.assertGreater(len(floors), proof_to_lean._FLOOR_SHIFT_LIMIT)
        indices = collections.defaultdict(int)
        capped = proof_to_lean._floor_shift_facts(graph, floors, indices, indices)
        self.assertFalse([fact for fact in capped if fact.startswith("have _d")], capped)
        self.assertTrue([fact for fact in capped if fact.startswith("have _z")], capped)
        below = proof_to_lean._floor_shift_facts(graph, floors[:proof_to_lean._FLOOR_SHIFT_LIMIT], indices, indices)
        self.assertTrue([fact for fact in below if fact.startswith("have _d")], below)

    def test_is_int_definition_axioms_are_arith_hints(self):
        source = random_floor_instance(FLOOR_SEEDS[3])
        self.assertIsNotNone(source)
        certificate = _export(source, "clause-log")
        graph = proof_to_lean._validate_graph(source, certificate)
        axioms = [node for node in _th_lemma_nodes(certificate) if _parameters(certificate, node) == ["arith"]
                  and any(graph.kind(term) == z3.Z3_OP_IS_INT
                          for term in proof_to_lean._reachable(graph, graph.conclusion(node))[0])]
        self.assertGreaterEqual(len(axioms), 2)
        for node in axioms:
            proof_to_lean._check_th_lemma(graph, node)

    def test_invalid_floor_declarations_are_rejected(self):
        for name, domain, range_ in (("to_int", ["Int"], "Int"), ("to_int", ["Real"], "Real"),
                                     ("is_int", ["Int"], "Bool"), ("is_int", ["Real", "Real"], "Bool")):
            tampered = copy.deepcopy(self.certificate)
            declaration = next(d for d in tampered["declarations"] if d["name"] == name)
            declaration["domain"], declaration["range"] = domain, range_
            with self.subTest(name=name, domain=domain, range=range_):
                with self.assertRaises(proof_to_lean.ReconstructionError):
                    proof_to_lean.reconstruct(self.source, tampered)

    def test_integrality_cuts_through_floors_get_projection_facts(self):
        # x and x/2 integers, x in {3, 5}: the clause log's cut rounds
        # (= (* 0.5 x) (to_real (to_int (* 0.5 x)))), a Real atom over the
        # Real variable x. Eliminating x leaves 2 floor(x/2) = 5 (or 3) over
        # the floor alone, stated over Int through its cast lemma.
        source = FLOOR_INPUTS["is_int_parity"]
        certificate = _export(source, "clause-log")
        graph = proof_to_lean._validate_graph(source, certificate)
        cuts = [node for node in _th_lemma_nodes(certificate) if _parameters(certificate, node) == ["cut"]]
        self.assertTrue(cuts)
        indices = collections.defaultdict(int)
        for node in cuts:
            proof_to_lean._check_th_lemma(graph, node)
            facts = proof_to_lean._projection_facts(graph, node, indices, indices)
            with self.subTest(node=node):
                self.assertRegex(facts[0], r"have _p%d_0 := _int_cast_eq \(\(\(-?2 : Int\)\) \* "
                                           r"\(Rat\.floor .*\) \+ \(\(-?[35] : Int\)\)\) \(\(0 : Int\)\)" % node)
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertRegex(text, r"have _p\d+_0 := _int_cast_eq ")
        # A step whose constraints mention no Real atom gets none: the cast
        # parity cut is over Int terms alone (its own integrality facts).
        source = CAST_INPUTS["cast_parity_cut"]
        certificate = _export(source, "clause-log")
        graph = proof_to_lean._validate_graph(source, certificate)
        for node in _th_lemma_nodes(certificate):
            with self.subTest(node=node):
                self.assertEqual(proof_to_lean._projection_facts(graph, node, indices, indices), [])

    def test_projection_eliminates_real_atoms_exactly(self):
        # x - 5/4 and 3x/2 integral (seed 5's cut): eliminating x relates the
        # two floors a and b by 8b - 12a = 15, which has no Int solution.
        source = random_floor_instance(5)
        self.assertIsNotNone(source)
        for core in ("clause-log", "legacy"):
            certificate = _export(source, core)
            graph = proof_to_lean._validate_graph(source, certificate)
            indices = collections.defaultdict(int)
            facts = [fact for node in _th_lemma_nodes(certificate)
                     for fact in proof_to_lean._projection_facts(graph, node, indices, indices)]
            with self.subTest(core=core):
                # The legacy core states the equality as two inequalities.
                self.assertTrue(any(re.search(r"\(\(-?8 : Int\)\) \* .*\(\(-?12 : Int\)\) \* .*"
                                              r"\(\(-?15 : Int\)\)\) \(\(0 : Int\)\)$", fact)
                                    for fact in facts), facts)

    def test_projection_leaves_out_constraints_without_linear_form(self):
        # A premise without a linear form is left out rather than dropping
        # every fact: seed 5's legacy farkas still gets the projection of
        # its other premises with any one of them unreadable.
        source = random_floor_instance(5)
        certificate = _export(source, "legacy")
        graph = proof_to_lean._validate_graph(source, certificate)
        indices = collections.defaultdict(int)
        node = next(node for node in _th_lemma_nodes(certificate)
                    if proof_to_lean._projection_facts(graph, node, indices, indices))
        premises = [graph.conclusion(premise) for premise in graph.arguments(node)[:-1]]
        self.assertTrue(premises)
        original = proof_to_lean._polarity_constraint
        for broken in premises:
            def unreadable(graph, literal, polarity, broken=broken):
                if literal == broken:
                    raise proof_to_lean.ReconstructionError("no linear form")
                return original(graph, literal, polarity)
            with self.subTest(premise=broken), mock.patch.object(proof_to_lean, "_polarity_constraint", unreadable):
                self.assertTrue(proof_to_lean._projection_facts(graph, node, indices, indices))

    def test_projection_limit_stops_elimination_rounds(self):
        # The limit is checked before a round builds its rows, the first
        # round included: below the size of the parity cut's first round,
        # no fact is stated.
        source = FLOOR_INPUTS["is_int_parity"]
        certificate = _export(source, "clause-log")
        graph = proof_to_lean._validate_graph(source, certificate)
        indices = collections.defaultdict(int)
        cut = next(node for node in _th_lemma_nodes(certificate) if _parameters(certificate, node) == ["cut"])
        self.assertTrue(proof_to_lean._projection_facts(graph, cut, indices, indices))
        with mock.patch.object(proof_to_lean, "_PROJECTION_LIMIT", 1):
            self.assertEqual(proof_to_lean._projection_facts(graph, cut, indices, indices), [])


class TestFloorLeanIntegration(unittest.TestCase):
    """End-to-end through to_int and is_int: both proof cores, certificate, Lean reconstruction, kernel check."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")

    def test_documented_floor_inputs_verify_on_both_cores(self):
        lean_test_support.prefetch((source, _export(source, core)) for source in FLOOR_INPUTS.values()
                                    for core in ("clause-log", "legacy"))
        hints, congruences = set(), 0
        for name, source in FLOOR_INPUTS.items():
            for core in ("clause-log", "legacy"):
                with self.subTest(name=name, core=core):
                    certificate, text = _check_in_lean(self, source, core)
                    self.assertIn("Rat.floor_le", text)
                    if core == "clause-log":
                        hints |= _hints(certificate)
                    else:
                        congruences += text.count("congrArg (fun (_t : Rat) => Rat.floor _t)")
        # The to_int axioms are arith hints; farkas lemmas combine them.
        self.assertLessEqual({"farkas", "arith"}, hints)
        self.assertGreater(congruences, 0)

    def test_pinned_random_floor_instances_verify_on_both_cores(self):
        shifts = 0
        for seed in FLOOR_SEEDS:
            source = random_floor_instance(seed)
            self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % seed)
            for core in ("clause-log", "legacy"):
                with self.subTest(seed=seed, core=core):
                    shifts += "Rat.floor_add_intCast" in _check_in_lean(self, source, core)[1]
        self.assertGreaterEqual(shifts, 3)


class TestCastLeanIntegration(unittest.TestCase):
    """End-to-end through to_real: both proof cores, certificate, Lean reconstruction, kernel check."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")

    def test_documented_cast_inputs_verify_on_both_cores(self):
        lean_test_support.prefetch((source, _export(source, core)) for source in CAST_INPUTS.values()
                                    for core in ("clause-log", "legacy"))
        hints = set()
        for name, source in CAST_INPUTS.items():
            for core in ("clause-log", "legacy"):
                with self.subTest(name=name, core=core):
                    certificate, text = _check_in_lean(self, source, core)
                    self.assertIn("_int_cast_", text)
                    if core == "clause-log":
                        hints |= _hints(certificate)
        self.assertLessEqual({"farkas", "cut", "arith"}, hints)

    def test_pinned_random_cast_instances_verify_on_both_cores(self):
        hints, congruences = set(), 0
        for seed in CAST_SEEDS:
            source = random_cast_instance(seed)
            self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % seed)
            for core in ("clause-log", "legacy"):
                with self.subTest(seed=seed, core=core):
                    certificate, text = _check_in_lean(self, source, core)
                    if core == "clause-log":
                        hints |= _hints(certificate)
                    else:
                        congruences += text.count("congrArg (fun (_t : Int) => ((_t : Int) : Rat))")
        self.assertIn("cut", hints)
        self.assertGreater(congruences, 0)

    def test_nested_ite_chains_verify_through_folded_facts(self):
        # Eight nested Int ites per chain. With the cast, integrality, and
        # Boolean-argument facts written out, the clause-log certificates
        # failed: real ran out of kernel memory (218 s, 11.2 GB), predicate
        # out of heartbeats elaborating the facts (168 s). Folded, each
        # checks in 3 to 20 s under 3.1 GB (see _cast_facts).
        fragments = {"real": "qf_lira", "function": "qf_uflira", "predicate": "qf_uflia"}
        for compare, fragment in fragments.items():
            source = cast_chains_instance(8, compare)
            for core in ("clause-log", "legacy"):
                with self.subTest(compare=compare, core=core):
                    certificate = _export(source, core)
                    self.assertEqual(certificate["fragment"], fragment)
                    _, report = lean_test_support.check(self, source, certificate)
                    self.assertTrue(_STANDARD_AXIOMS in report or "does not depend on any axioms" in report, report)


if __name__ == "__main__":
    unittest.main()
