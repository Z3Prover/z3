############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Tests for constant arrays over an uninterpreted or Bool index sort in the
# Lean reconstruction, certified through the sat.smt clause log.
# ((as const (Array I E)) v) is Lean's constant function. Over Int and Real
# indices Z3 relates it to other arrays through default values, which need
# an infinite index type; over an uninterpreted sort, which may be finite,
# there are none, and the sort is a Lean type of its own
# (proof_to_lean._index_sorts) unless it is all of the carrier: over one
# carrier (= (store (const v) i w) (store (const w) i w)) contradicts (not
# (= v w)), though the input has a model in which I has one element. Z3's
# rewriter makes such arrays of sets ((setminus s s), a subset as (=
# (setminus a b) empty)), so those inputs were rejected before.
# Validation without Lean, and end-to-end checks that need the z3 executable
# and the pinned Lean toolchain.
############################################
import copy
from pathlib import Path
import random
import re
import subprocess
import sys
import tempfile
import unittest

import z3

_EXAMPLES = Path(__file__).resolve().parent
sys.path.insert(0, str(_EXAMPLES))
import proof_certificate
import lean_test_support
import proof_to_lean
from test_proof_to_lean_array import _check_in_lean, _export, _without_facts
from test_proof_to_lean_index_sort import _structure
from test_proof_to_lean_lia import _STANDARD_AXIOMS, _z3_available

_SORTS = """(declare-sort I 0)
(declare-sort E 0)
(declare-fun a () (Array I E))
(declare-fun s () (Array I Bool))
(declare-fun t () (Array I Bool))
(declare-fun i () I)
(declare-fun j () I)
(declare-fun v () E)
(declare-fun w () E)
"""
_CONST = "((as const (Array I E)) %s)"
_EMPTY = "((as const (Array I Bool)) false)"
_FULL = "((as const (Array I Bool)) true)"
_COLOR = "(declare-datatypes ((Color 0)) (((red) (green) (blue))))\n"

# Documented inputs, each unsatisfiable, with a constant array over the sort
# I next to the sort E: I is the Lean type _m.S0.
CONSTANT_SORT_INPUTS = {
    "read_of_a_constant_array": _SORTS + "(assert (not (= (select %s i) v)))\n(check-sat)\n" % (_CONST % "v"),
    "read_past_a_store": _SORTS + """(assert (not (= (select (store %s i w) j) v)))
(assert (not (= i j)))
(check-sat)
""" % (_CONST % "v"),
    "array_equal_to_a_constant_array": _SORTS + """(assert (= a %s))
(assert (not (= (select a i) v)))
(check-sat)
""" % (_CONST % "v"),
    # The rewriter compares two constant arrays by their values, which Lean
    # proves by reading both at an index of the sort (_index_witness).
    "constant_arrays_of_distinct_values": _SORTS + """(assert (= %s %s))
(assert (not (= v w)))
(check-sat)
""" % (_CONST % "v", _CONST % "w"),
    "the_empty_set_is_not_full": _SORTS + "(assert (= v w))\n(assert (= %s %s))\n(check-sat)\n" % (_EMPTY, _FULL),
    "member_of_the_empty_set": _SORTS + """(assert (= v w))
(assert (= s %s))
(assert (select s i))
(check-sat)
""" % _EMPTY,
    "insert_into_the_empty_set": _SORTS + "(assert (= v w))\n(assert (= (store %s i true) %s))\n(check-sat)\n" % (
        _EMPTY, _EMPTY),
    # Constant arrays the rewriter makes: (setminus t t) is the empty set,
    # (union s (complement s)) the full one, and a subset the equality of a
    # difference with the empty set.
    "equal_to_a_difference_with_itself": _SORTS + """(assert (= v w))
(assert (= s (setminus t t)))
(assert (select s i))
(check-sat)
""",
    "equal_to_a_union_with_the_complement": _SORTS + """(assert (= v w))
(assert (= (union s (complement s)) t))
(assert (not (select t i)))
(check-sat)
""",
    "subset_next_to_a_sort": _SORTS + """(assert (= v w))
(assert (subset s t))
(assert (select s i))
(assert (not (select t i)))
(check-sat)
""",
    "subset_of_an_insert": _SORTS + """(assert (= v w))
(assert (subset (store s i true) t))
(assert (not (select t i)))
(check-sat)
""",
    "subsets_are_transitive": _SORTS + """(declare-fun u () (Array I Bool))
(assert (= v w))
(assert (subset s t))
(assert (subset t u))
(assert (not (subset s u)))
(check-sat)
""",
    "full_below_a_set": _SORTS + """(assert (= v w))
(assert (subset %s s))
(assert (not (select s i)))
(check-sat)
""" % _FULL,
    "equal_differences": _SORTS + """(assert (= v w))
(assert (= (setminus s t) (setminus t t)))
(assert (select s i))
(assert (not (select t i)))
(check-sat)
""",
    # Extensionality, a constant array as an argument, and nested arrays.
    "extensionality_with_a_constant_array": _SORTS + """(assert (not (= a %s)))
(assert (= a (store %s i v)))
(check-sat)
""" % (_CONST % "v", _CONST % "v"),
    "constant_array_under_a_function": _SORTS + """(declare-fun f ((Array I E)) E)
(assert (= v w))
(assert (not (= (f %s) (f %s))))
(check-sat)
""" % (_CONST % "v", _CONST % "w"),
    "constant_array_of_constant_arrays": _SORTS + """(declare-fun n () (Array I (Array I E)))
(assert (= n ((as const (Array I (Array I E))) %s)))
(assert (not (= (select (select n i) j) v)))
(check-sat)
""" % (_CONST % "v"),
    # Each sort indexes constant arrays into the other: two types, no other sort.
    "two_index_sorts": """(declare-sort I 0)
(declare-sort J 0)
(declare-fun i () I)
(declare-fun j () J)
(declare-fun v () I)
(declare-fun w () J)
(assert (or (not (= (select ((as const (Array I J)) w) i) w)) (not (= (select ((as const (Array J I)) v) j) v))))
(check-sat)
""",
    # A constant array of an enumeration: its reads are its value, a constructor.
    "constant_array_of_an_enumeration": _COLOR + """(declare-sort I 0)
(declare-fun i () I)
(declare-fun k () Color)
(assert (not (= (select ((as const (Array I Color)) k) i) red)))
(assert (not (= k green)))
(assert (not (= k blue)))
(check-sat)
""",
}
# The boundary of the carrier's exception: I is the only sort, but a function
# takes an argument of another kind (a Bool, an Int, an array), which is
# injected into the carrier, so the carrier holds more than I and I is a
# type of its own all the same.
_ONLY_SORT = """(declare-sort I 0)
(declare-fun v () I)
(declare-fun w () I)
(declare-fun f (%s) I)
(assert (= ((as const (Array I I)) v) ((as const (Array I I)) w)))
(assert (not (= v w)))
(assert (= (f %s) v))
(check-sat)
"""
CONSTANT_SORT_INPUTS.update({
    "the_only_sort_next_to_a_bool_argument": _ONLY_SORT % ("Bool", "true"),
    "the_only_sort_next_to_an_int_argument": _ONLY_SORT % ("Int", "0"),
    "the_only_sort_next_to_an_array_argument": _ONLY_SORT % ("(Array I I)", "((as const (Array I I)) v)"),
})
_INDEX_SORTS = {name: ("I",) for name in CONSTANT_SORT_INPUTS}
_INDEX_SORTS["two_index_sorts"] = ("I", "J")

# The index sort alone in the carrier (it stays _m.U), and Bool indices
# (Prop): no type of its own.
CARRIER_INPUTS = {
    "constant_arrays_over_the_only_sort": """(declare-sort I 0)
(declare-fun v () I)
(declare-fun w () I)
(assert (= ((as const (Array I I)) v) ((as const (Array I I)) w)))
(assert (not (= v w)))
(check-sat)
""",
    # (REJECTED_SUBSET_INPUTS["over_a_sort"] of test_proof_to_lean_subset.py before.)
    "subset_over_the_only_sort": """(declare-sort U 0)
(declare-fun a () (Array U Bool))
(declare-fun b () (Array U Bool))
(declare-fun u () U)
(assert (subset a b))
(assert (select a u))
(assert (not (select b u)))
(check-sat)
""",
    "equal_to_a_difference_with_itself_over_the_only_sort": """(declare-sort I 0)
(declare-fun s () (Array I Bool))
(declare-fun t () (Array I Bool))
(declare-fun i () I)
(assert (= s (setminus t t)))
(assert (select s i))
(check-sat)
""",
    "read_over_bool_indices": """(declare-fun p () Bool)
(assert (not (select ((as const (Array Bool Bool)) true) p)))
(check-sat)
""",
    "array_over_bool_indices_equal_to_a_constant_array": """(declare-fun a () (Array Bool Int))
(declare-fun p () Bool)
(assert (= a ((as const (Array Bool Int)) 3)))
(assert (> (select a p) 3))
(check-sat)
""",
    "constant_arrays_over_bool_indices_of_distinct_values": """(declare-fun x () Int)
(assert (= ((as const (Array Bool Int)) x) ((as const (Array Bool Int)) 3)))
(assert (> x 3))
(check-sat)
""",
    # (REJECTED_SUBSET_INPUTS["over_bool_indices"] before.)
    "subset_over_bool_indices": """(declare-fun a () (Array Bool Bool))
(declare-fun b () (Array Bool Bool))
(assert (subset a b))
(assert (select a true))
(assert (not (select b true)))
(check-sat)
""",
    "constant_array_of_an_enumeration_over_bool_indices": _COLOR + """(declare-fun c () (Array Bool Color))
(declare-fun p () Bool)
(assert (= c ((as const (Array Bool Color)) red)))
(assert (= (select c p) green))
(check-sat)
""",
}
_FRAGMENTS = {"the_only_sort_next_to_an_int_argument": "qf_uflia",
              "array_over_bool_indices_equal_to_a_constant_array": "qf_uflia",
              "constant_arrays_over_bool_indices_of_distinct_values": "qf_uflia"}

# Inputs that stay rejected, with the error and its message. The last two
# depend on what Z3 does with the input (the rewriter's quantifier, the array
# solver's default term): if Z3 changes there, the input is no longer
# rejected for that reason and needs replacing, not the pipeline.
REJECTED_INPUTS = {
    # A model's constant array over array indices is constant on the
    # embedded indices only, not Lean's constant function.
    "indexed_by_arrays": ("""(declare-fun x () (Array Int Int))
(assert (not (select ((as const (Array (Array Int Int) Bool)) true) x)))
(check-sat)
""", proof_certificate.ProofExportError, r"constant arrays indexed by arrays are not supported: "
                                         r"Array\(Array\(Int, Int\), Bool\)$"),
    # A finite index sort has no default values.
    "default_value_over_a_sort": (_SORTS + """(assert (= a %s))
(assert (not (= (default a) v)))
(check-sat)
""" % (_CONST % "v"), proof_certificate.ProofExportError,
                                  r"default values are supported over Int and Real indices only: Array\(I, E\)$"),
    # Z3's rewriter expands an equality between stores over constant arrays
    # over an index sort that may be finite into a quantified formula.
    "stores_compared_with_a_constant_array": (_SORTS + """(assert (= (store %s i w) %s))
(assert (not (= v w)))
(check-sat)
""" % (_CONST % "v", _CONST % "v"), proof_certificate.ProofExportError,
                                              r"^quantifiers are not supported in the clause log: forall$"),
    # The array solver's own default value of a constant array of an
    # enumeration, (= red (default (const red))), over the sort.
    "solver_default_over_a_sort": (_COLOR + """(declare-sort I 0)
(declare-fun c () (Array I Color))
(declare-fun i () I)
(assert (= c ((as const (Array I Color)) red)))
(assert (not (= (select c i) red)))
(check-sat)
""", proof_to_lean.ReconstructionError, r"^invalid default declaration$"),
}

# Satisfiable with one index (v and w are of another sort): Z3 answers sat,
# so the rewriter does not compare these stores by default values.
ONE_INDEX_SATISFIABLE = _SORTS + """(assert (= (store %s i w) (store %s i w)))
(assert (not (= v w)))
(check-sat)
""" % (_CONST % "v", _CONST % "w")

# The same two assertions behind a false one: Z3 logs them as written and
# refutes the input by the first alone, and the equality of the stores and
# the disequality are hypotheses of the theorem all the same.
ONE_ELEMENT_INDEX_SORT = """(declare-sort I 0)
(declare-sort E 0)
(declare-fun i () I)
(declare-fun v () E)
(declare-fun w () E)
(declare-fun p () Bool)
(assert (and p (not p)))
(assert (= (store %s i w) (store %s i w)))
(assert (not (= v w)))
(check-sat)
""" % (_CONST % "v", _CONST % "w")


def random_constant_sort_instance(seed, index="I", depth=2):
    """Random constraints over arrays and sets with constant arrays over a sort, or None if sat or undecided.

    index is "I" (the sort I next to the element sort E), "alone" (arrays
    from I to I, the only sort), or "Bool". Two to five assertions over
    members of set terms (the empty and the full set, unions,
    intersections, differences, complements, inserts and removals, ites),
    equalities of elements (constants, a function of an index, reads of
    array terms: constants, constant arrays, stores, ites), of arrays, of
    sets, and of indices (constants and, over a sort, ites), subsets, and a
    predicate over the elements. Inputs without a constant array are left
    out.
    """
    rng = random.Random(seed)
    alone = index == "alone"
    sort = "Bool" if index == "Bool" else "I"
    elem = "I" if alone else "E"
    lines = [] if sort == "Bool" else ["(declare-sort I 0)"]
    if not alone:
        lines.append("(declare-sort E 0)")
    indices = ["p", "r"] if sort == "Bool" else ["i", "j"]
    lines += ["(declare-fun %s () %s)" % (name, sort) for name in indices]
    elements = indices if alone else ["e1", "e2"]
    if not alone:
        lines += ["(declare-fun %s () E)" % name for name in elements]
    lines += ["(declare-fun g (%s) %s)" % (sort, elem), "(declare-fun q (%s) Bool)" % elem]
    lines += ["(declare-fun %s () (Array %s %s))" % (name, sort, elem) for name in ("a", "b")]
    lines += ["(declare-fun %s () (Array %s Bool))" % (name, sort) for name in ("s0", "s1")]
    empty, full = ("((as const (Array %s Bool)) %s)" % (sort, value) for value in ("false", "true"))

    def position(d):
        choice = rng.randrange(4 if d and sort != "Bool" else 2)
        if choice < 2:
            return indices[choice]
        if choice == 2 and alone:
            return element(d - 1)
        return "(ite %s %s %s)" % (atom(d - 1), position(d - 1), position(d - 1))

    def element(d):
        choice = rng.randrange(5 if d else 2)
        if choice < 2:
            return elements[choice]
        if choice == 2:
            return "(g %s)" % position(d - 1)
        return "(select %s %s)" % (array(d - 1), position(d - 1))

    def array(d):
        choice = rng.randrange(7 if d else 3)
        if choice < 2:
            return ("a", "b")[choice]
        if choice in (2, 3):
            return "((as const (Array %s %s)) %s)" % (sort, elem, element(max(d - 1, 0)))
        if choice in (4, 5):
            return "(store %s %s %s)" % (array(d - 1), position(d - 1), element(d - 1))
        return "(ite %s %s %s)" % (atom(d - 1), array(d - 1), array(d - 1))

    def term(d):
        choice = rng.randrange(10 if d else 4)
        if choice < 2:
            return ("s0", "s1")[choice]
        if choice in (2, 3):
            return (empty, full)[choice - 2]
        if choice == 4:
            return "(union %s %s)" % (term(d - 1), term(d - 1))
        if choice == 5:
            return "(intersection %s %s)" % (term(d - 1), term(d - 1))
        if choice == 6:
            return "(setminus %s %s)" % (term(d - 1), term(d - 1))
        if choice == 7:
            return "(complement %s)" % term(d - 1)
        if choice == 8:
            return "(store %s %s %s)" % (term(d - 1), position(d - 1), rng.choice(("true", "false")))
        return "(ite %s %s %s)" % (atom(d - 1), term(d - 1), term(d - 1))

    def atom(d):
        choice = rng.randrange(9 if d else 5)
        if choice < 2:
            return "(select %s %s)" % (term(d), position(d))
        if choice == 2:
            return "(= %s %s)" % (element(d), element(d))
        if choice == 3:
            return "(q %s)" % element(d)
        if choice == 4:
            return "(= %s %s)" % (position(0), position(0))
        if choice == 5:
            return "(= %s %s)" % (array(d), array(d))
        if choice == 6:
            return "(= %s %s)" % (term(d), term(d))
        if choice == 7:
            return "(subset %s %s)" % (term(d), term(d))
        return "(= %s %s)" % (position(d), position(d))

    def literal():
        return atom(depth) if rng.randrange(2) else "(not %s)" % atom(depth)

    for _ in range(rng.randrange(2, 6)):
        lines.append("(assert %s)" % (literal() if rng.randrange(3) else "(or %s %s)" % (literal(), literal())))
    lines.append("(check-sat)")
    source = "\n".join(lines) + "\n"
    if "as const" not in source:
        return None
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set("timeout", 10000)
    solver.from_string(source)
    return source if solver.check() == z3.unsat else None


# Pinned unsatisfiable seeds of random_constant_sort_instance, by index, each
# with an equality of arrays read at an index of the sort. Over I: 290 and
# 461 constant arrays of elements, 599 an extensionality witness, 643, 799,
# and 1108 subsets and pointwise facts.
CONSTANT_SORT_SEEDS = {"I": (290, 461, 599, 643, 799, 1108), "alone": (199, 501), "Bool": (290, 457, 599)}

_STRUCTURE = ["  U : Type", "  elems : Nat -> U", "  funs : Nat -> List U -> U", "  preds : Nat -> List U -> Prop",
              "  bool : Prop -> U", "  S0 : Type", "  s0_nonempty : Nonempty S0", "  s0_elems : Nat -> S0",
              "  s0_funs : Nat -> List U -> S0", "  s0_inj : S0 -> U", "  arrs_s0u : Nat -> S0 -> U"]
# The facts of a comparison at the witness index, and the default-value
# facts they stand in for over Int and Real indices.
_WITNESS_FACT = re.compile(r"have _(e\d+ : .* -> _select .* := congrArg \(fun _x => _select _x "
                           r"|dc\d+ := _select_const )")
_DEFAULT_FACT = re.compile(r"_default_const|_default_store|_default [_(]")


def _source(name):
    return CONSTANT_SORT_INPUTS.get(name) or CARRIER_INPUTS[name]


def _proofs(text):
    """The text after the definitions of the prelude: the terms, lemmas, and the theorem."""
    return text[text.index("\ndef term_"):] if "\ndef term_" in text else text[text.index("\ndef formula_"):]


class TestConstantSortValidation(unittest.TestCase):
    """Validation without Lean: which sorts get a type of their own, the encoding, and what stays rejected."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")
        cls.certificates = {name: _export(_source(name)) for name in list(CONSTANT_SORT_INPUTS) + list(CARRIER_INPUTS)}
        cls.texts = {name: proof_to_lean.reconstruct(_source(name), certificate)
                     for name, certificate in cls.certificates.items()}

    def test_which_sorts_get_a_type_of_their_own(self):
        for name, certificate in self.certificates.items():
            with self.subTest(name=name):
                graph = proof_to_lean._validate_graph(_source(name), certificate)
                self.assertEqual(graph.index_sorts, _INDEX_SORTS.get(name, ()))
                self.assertTrue(any(d["kind"] == z3.Z3_OP_CONST_ARRAY for d in certificate["declarations"]))
                indices = {proof_to_lean._array_components(d["range"])[0] for d in certificate["declarations"]
                           if d["kind"] == z3.Z3_OP_CONST_ARRAY}
                self.assertEqual(graph.constant_indices, indices)
                self.assertNotIn("sorry", self.texts[name])
                self.assertNotIn("axiom ", self.texts[name])

    def test_encoding(self):
        text = self.texts["read_of_a_constant_array"]
        self.assertIn('-- Uninterpreted sort "I" is the type _m.S0 of its own, the index type of the constant '
                      "arrays: constants _m.s0_elems, functions _m.s0_funs, arguments of functions and predicates "
                      "injected into _m.U by _m.s0_inj.", text)
        self.assertIn('-- Uninterpreted sort "E" is the type _m.U;', text)
        self.assertEqual(_structure(text), _STRUCTURE)
        self.assertRegex(text, r" : \(_m\.S0 -> _m\.U\) := \(@_const_array _m\.S0 _m\.U \(term_\d+ _atoms _m\)\)\n")
        # The empty set the rewriter makes of a difference, and of a subset.
        for name in ("equal_to_a_difference_with_itself", "subset_next_to_a_sort"):
            self.assertRegex(self.texts[name], r" : \(_m\.S0 -> Prop\) := \(@_const_array _m\.S0 Prop \(formula_")
        self.assertIn("_subset_eq", self.texts["subset_next_to_a_sort"])
        # The header names both reasons where the input's operators are over the sort too.
        for name in ("equal_to_a_union_with_the_complement", "subset_next_to_a_sort"):
            self.assertIn('-- Uninterpreted sort "I" is the type _m.S0 of its own, the index type of the pointwise '
                          "maps and constant arrays: constants _m.s0_elems,", self.texts[name])
        # Nested, and two sorts indexing constant arrays into each other.
        text = self.texts["constant_array_of_constant_arrays"]
        self.assertRegex(text, r":= \(@_const_array _m\.S0 \(_m\.S0 -> _m\.U\) \(term_\d+ _atoms _m\)\)\n")
        text = self.texts["two_index_sorts"]
        self.assertIn("  arrs_s0s1 : Nat -> S0 -> S1", text)
        self.assertIn("  arrs_s1s0 : Nat -> S1 -> S0", text)
        self.assertIn("(@_const_array _m.S0 _m.S1 ", text)
        self.assertIn("(@_const_array _m.S1 _m.S0 ", text)
        # The only sort stays the carrier, Bool indices are Prop.
        text = self.texts["constant_arrays_over_the_only_sort"]
        self.assertIn('-- Uninterpreted sort "I" is the type _m.U;', text)
        self.assertIn("(@_const_array _m.U _m.U ", text)
        self.assertNotIn("S0", text)
        text = self.texts["constant_arrays_over_bool_indices_of_distinct_values"]
        self.assertIn("(@_const_array Prop Int ", text)
        self.assertNotIn("S0", text)
        text = self.texts["constant_array_of_an_enumeration_over_bool_indices"]
        self.assertIn("(@_const_array Prop _m.U ", text)

    def test_compared_arrays_are_read_at_an_index_of_the_sort(self):
        """No default value over these sorts: an equality of arrays is read at one index, a constant array too."""
        for name, witness in (("constant_arrays_of_distinct_values", "(_m.s0_elems 0)"),
                              ("the_empty_set_is_not_full", "(_m.s0_elems 0)"),
                              ("constant_arrays_over_the_only_sort", "(_m.elems 0)"),
                              ("constant_arrays_over_bool_indices_of_distinct_values", "True")):
            with self.subTest(name=name):
                lines = [line.strip() for line in self.texts[name].split("\n")]
                equalities = [line for line in lines if re.match(r"have _e\d+ : ", line)]
                constants = [line for line in lines if re.match(r"have _dc\d+ := ", line)]
                self.assertTrue(equalities)
                for line in equalities:
                    self.assertRegex(line, r"^have _e\d+ : \(.*\) = \(.*\) -> _select \(.*\) %s = _select \(.*\) %s := "
                                           r"congrArg \(fun _x => _select _x %s\)$" % ((re.escape(witness),) * 3))
                self.assertGreaterEqual(len(constants), 2)
                for line in constants:
                    self.assertRegex(line, r"^have _dc\d+ := _select_const \(I := [^)]*\) .* %s$" % re.escape(witness))
        # No default-value fact outside the prelude in any of the certificates.
        for name, text in self.texts.items():
            with self.subTest(name=name):
                self.assertNotRegex(_proofs(text), _DEFAULT_FACT)

    def test_int_indices_keep_their_default_values(self):
        source = """(declare-fun x () Int)
(assert (= ((as const (Array Int Int)) x) ((as const (Array Int Int)) 3)))
(assert (> x 3))
(check-sat)
"""
        certificate = _export(source)
        graph = proof_to_lean._validate_graph(source, certificate)
        self.assertEqual(graph.constant_indices, frozenset())
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertRegex(text, r"have _e\d+ : .* -> _default _int_unbounded ")
        self.assertRegex(text, r"have _dc\d+ := _default_const \(I := Int\) _int_unbounded ")
        self.assertNotRegex(text, _WITNESS_FACT)

    def test_rejected_inputs(self):
        for name, (source, error, message) in REJECTED_INPUTS.items():
            with self.subTest(name=name):
                with self.assertRaisesRegex(error, message):
                    proof_to_lean.reconstruct(source, _export(source))
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "^sat: no unsat proof exists$"):
            _export(ONE_INDEX_SATISFIABLE)

    def _rejects(self, name, mutate, message):
        certificate = copy.deepcopy(self.certificates[name])
        mutate(certificate)
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, message):
            proof_to_lean.reconstruct(_source(name), certificate)

    def test_tampered_certificates_are_rejected(self):
        def constant(certificate):
            return next(d for d in certificate["declarations"] if d["kind"] == z3.Z3_OP_CONST_ARRAY)

        def value_of_the_index_sort(certificate):
            constant(certificate)["domain"] = ["I"]

        def indexed_by_arrays(certificate):
            # The constant array relabelled one over array indices.
            constant(certificate).update(domain=["E"], range="(Array (Array I E) E)")

        def default_value(certificate):
            # A default value of the array sort the constant array is of.
            certificate["declarations"].append({"kind": z3.Z3_OP_ARRAY_DEFAULT, "name": "default",
                                                "domain": ["(Array I E)"], "range": "E", "parameters": []})

        def merged_sorts(certificate):
            # The index sort merged with the element sort: one carrier, were this the input's signature.
            for declaration in certificate["declarations"]:
                declaration["range"] = declaration["range"].replace("I", "E")
                declaration["domain"] = [sort.replace("I", "E") for sort in declaration["domain"]]

        name = "read_of_a_constant_array"
        self._rejects(name, value_of_the_index_sort, "^invalid constant array declaration$")
        self._rejects(name, indexed_by_arrays, "^invalid constant array declaration$")
        self._rejects(name, default_value, "^invalid default declaration$")
        self._rejects(name, merged_sorts, "does not match the original input")

    def test_pinned_seeds_are_unsatisfiable(self):
        for index, seeds in CONSTANT_SORT_SEEDS.items():
            for seed in seeds:
                with self.subTest(index=index, seed=seed):
                    source = random_constant_sort_instance(seed, index=index)
                    self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % seed)
                    graph = proof_to_lean._validate_graph(source, _export(source))
                    self.assertEqual(graph.index_sorts, ("I",) if index == "I" else ())
                    self.assertEqual(graph.constant_indices, {"Bool" if index == "Bool" else "I"})


# The model of ONE_ELEMENT_INDEX_SORT's equality of stores and disequality,
# and the reason one carrier has none (filled with the namespace, the two
# hypotheses' definitions, and the indices of v and w in _m.elems).
_ONE_INDEX_MODEL = """
namespace %(namespace)s

def _one_index : Interpretation where
  U := Bool
  elems := fun n => decide (n = %(v)d)
  funs := fun _ _ => true
  preds := fun _ _ => True
  bool := fun _ => true
  S0 := Unit
  s0_nonempty := Nonempty.intro ()
  s0_elems := fun _ => ()
  s0_funs := fun _ _ => ()
  s0_inj := fun _ => true
  arrs_s0u := fun _ _ => true

theorem _one_index_equality (_atoms : Nat -> Prop) : %(equality)s _atoms _one_index := by
  show _store (_const_array Unit (decide (%(v)d = %(v)d))) () (decide (%(w)d = %(v)d))
    = _store (_const_array Unit (decide (%(w)d = %(v)d))) () (decide (%(w)d = %(v)d))
  funext x
  cases x
  simp [_store]

theorem _one_index_disequality (_atoms : Nat -> Prop) : %(disequality)s _atoms _one_index := by
  show Not ((decide (%(v)d = %(v)d) : Bool) = decide (%(w)d = %(v)d))
  decide

theorem _one_carrier_contradiction (U : Type) (i v w : U)
    (h : _store (_const_array U v) i w = _store (_const_array U w) i w) (d : Not (v = w)) : False := by
  have key : forall x : U, Not (x = i) -> False := by
    intro x hx
    have hx' := congrFun h x
    simp [_store, _const_array, hx] at hx'
    exact d hx'
  by_cases h1 : v = i
  . exact key w (fun h2 => d (h1.trans h2.symm))
  . exact key v h1

end %(namespace)s
"""


class TestConstantSortLeanIntegration(unittest.TestCase):
    """End-to-end: clause log, certificate, Lean reconstruction, kernel check."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")

    def test_documented_inputs_verify(self):
        inputs = {**CONSTANT_SORT_INPUTS, **CARRIER_INPUTS}
        lean_test_support.prefetch((source, _export(source)) for source in inputs.values())
        for name, source in inputs.items():
            with self.subTest(name=name):
                _check_in_lean(self, source, _FRAGMENTS.get(name, "qf_uf"))

    def test_pinned_random_instances_verify(self):
        sources = []
        for index, seeds in CONSTANT_SORT_SEEDS.items():
            for seed in seeds:
                source = random_constant_sort_instance(seed, index=index)
                self.assertIsNotNone(source, "seed %d (%s) is no longer unsatisfiable" % (seed, index))
                sources.append((index, seed, source, _export(source)))
        lean_test_support.prefetch((source, certificate) for _, _, source, certificate in sources)
        for index, seed, source, certificate in sources:
            with self.subTest(index=index, seed=seed):
                _, report = lean_test_support.check(self, source, certificate)
                self.assertTrue(_STANDARD_AXIOMS in report or "does not depend on any axioms" in report, report)

    def test_the_reads_at_an_index_are_needed(self):
        """Without the facts at the witness index each of these fails in Lean, with grind failing."""
        for name in ("constant_arrays_of_distinct_values", "the_empty_set_is_not_full",
                     "constant_arrays_over_the_only_sort", "constant_arrays_over_bool_indices_of_distinct_values"):
            with self.subTest(name=name):
                source = _source(name)
                text = proof_to_lean.reconstruct(source, _export(source))
                self.assertTrue(any(_WITNESS_FACT.match(line.strip()) for line in text.split("\n")), text)
                with tempfile.TemporaryDirectory() as directory:
                    output = Path(directory) / "facts.lean"
                    output.write_text(_without_facts(text, _WITNESS_FACT.match))
                    result = subprocess.run([str(proof_to_lean._CHECK_LEAN), str(output)], text=True,
                                            capture_output=True)
                report = result.stdout + result.stderr
                self.assertNotEqual(result.returncode, 0, report)
                errors = [line for line in report.split("\n") if "error:" in line]
                self.assertTrue(errors, report)
                for error in errors:
                    self.assertIn("`grind` failed", error)

    def test_a_one_element_index_sort_is_an_instance(self):
        """The theorem's hypotheses hold in a model whose index sort has one element and whose other sort has two.

        The equality of the stores says that I has one element when v and w
        differ. The interpretation _one_index is that model: S0 is Unit, U
        is Bool. Over one carrier the same two statements are contradictory
        (_one_carrier_contradiction, with the file's own _store and
        _const_array), so a theorem stating them over _m.U alone would say
        nothing about this input.
        """
        source = ONE_ELEMENT_INDEX_SORT
        text = proof_to_lean.reconstruct(source, _export(source))
        self.assertEqual(_structure(text), _STRUCTURE)
        elements = {name: int(index) for index, name in re.findall(r'^-- Element (\d+): "(\w+)"$', text, re.M)}
        self.assertEqual(set(elements), {"i", "v", "w"})
        # The hypotheses in assertion order: the false one, the equality of the stores, the disequality.
        hypotheses = re.findall(r"^    \(_h\d+ : \((formula_\d+) _atoms _m\)\)$", text, re.M)
        self.assertEqual(len(hypotheses), 3)
        equality, disequality = hypotheses[1:]
        self.assertRegex(text, r"\ndef %s .* := \(\(term_\d+ _atoms _m\) = \(term_\d+ _atoms _m\)\)\n" % equality)
        self.assertRegex(text, r"\ndef %s .* := \(Not \(formula_\d+ _atoms _m\)\)\n" % disequality)
        namespace = lean_test_support.namespace(source)
        theorems = ("_one_index_equality", "_one_index_disequality", "_one_carrier_contradiction")
        model = _ONE_INDEX_MODEL % {"namespace": namespace, "equality": equality, "disequality": disequality,
                                    "v": elements["v"], "w": elements["w"]}
        _, report = lean_test_support.check(self, source, text=text + model, theorems=("unsat",) + theorems)
        self.assertNotIn("sorryAx", report)
        for theorem in ("unsat",) + theorems:
            axioms = re.search(r"'%s\.%s' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
                               % (re.escape(namespace), theorem), report)
            self.assertIsNotNone(axioms, report)
            self.assertLessEqual(set(filter(None, re.split(r",\s*", axioms.group(1) or ""))),
                                 set(re.split(r",\s*", _STANDARD_AXIOMS.strip("[]"))), report)


if __name__ == "__main__":
    unittest.main()
