############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Tests for maps, set operators, and subsets over arrays indexed by an
# uninterpreted sort in the Lean reconstruction, certified through the
# sat.smt clause log.
# The uninterpreted sorts are one Lean type, _m.U, which is faithful while
# arrays are only read, stored into, and compared. A pointwise function is
# not: over one carrier (= (store a i true) (complement (store a i false)))
# contradicts (not (= e1 e2)) over another sort, though the input has a
# model in which the index sort has one element. So the index sort of such
# arrays is a Lean type of its own (proof_to_lean._index_sorts) unless it is
# all of the carrier anyway.
# Validation without Lean, and end-to-end checks that need the z3 executable
# and the pinned Lean toolchain.
############################################
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
import lean_test_support
import proof_to_lean
from test_proof_to_lean_array import ARRAY_INPUTS, _check_in_lean, _export
from test_proof_to_lean_lia import _STANDARD_AXIOMS, _z3_available

_SORTS = """(declare-sort I 0)
(declare-sort E 0)
(declare-fun a () (Array I Bool))
(declare-fun b () (Array I Bool))
(declare-fun i () I)
(declare-fun j () I)
(declare-fun e () E)
"""

# Documented inputs, each unsatisfiable, in which the index sort of a map or
# set operator is not the only inhabitant of the carrier: its Lean type is
# _m.S0. (ARRAY_INPUTS has four more: map_over_sort, map_distinct,
# equality_map_commutes, map_under_function.)
INDEX_SORT_INPUTS = {
    # A second sort with a function over it.
    "sets_next_to_a_sort": _SORTS + """(declare-fun f (E) E)
(assert (select (intersection a b) i))
(assert (or (not (select a i)) (not (= (f e) (f e)))))
(check-sat)
""",
    # Terms of the index sort as arguments: injected into the carrier by _m.s0_inj.
    "index_as_argument": _SORTS + """(declare-fun g (I) E)
(assert (= i j))
(assert (select (union a b) i))
(assert (or (not (= (g i) (g j))) (and (not (select a j)) (not (select b j)))))
(check-sat)
""",
    # A function into the index sort: the family _m.s0_funs.
    "function_into_the_index_sort": _SORTS + """(declare-fun h (E) I)
(assert (select (complement a) (h e)))
(assert (select a (h e)))
(check-sat)
""",
    # No second sort, but a predicate over Bool, whose arguments the carrier holds.
    "predicate_over_bool_next_to_sets": """(declare-sort I 0)
(declare-fun a () (Array I Bool))
(declare-fun b () (Array I Bool))
(declare-fun i () I)
(declare-fun r (Bool) Bool)
(assert (r (select (union a b) i)))
(assert (not (select a i)))
(assert (not (select b i)))
(assert (not (r false)))
(check-sat)
""",
    # An equality of sets the euf solver decides by commutativity, next to two elements of another sort.
    "set_equality_next_to_a_sort": _SORTS + """(declare-fun e2 () E)
(assert (not (= e e2)))
(assert (not (= (union a b) (union b a))))
(check-sat)
""",
    # Two index sorts: _m.S0 and _m.S1.
    "two_index_sorts": """(declare-sort I 0)
(declare-sort J 0)
(declare-fun a () (Array I Bool))
(declare-fun b () (Array J Bool))
(declare-fun i () I)
(declare-fun j () J)
(assert (select (complement a) i))
(assert (select (complement b) j))
(assert (or (select a i) (select b j)))
(check-sat)
""",
    # An array into the index sort, indexed by the other sort: _m.U -> _m.S0.
    "elements_of_the_index_sort": _SORTS + """(declare-fun m () (Array E I))
(assert (select (complement a) (select m e)))
(assert (select a (select (store m e (select m e)) e)))
(check-sat)
""",
    "ite_over_the_index_sort": _SORTS + """(declare-fun q (E) Bool)
(assert (select (complement a) (ite (q e) i j)))
(assert (select a i))
(assert (select a j))
(check-sat)
""",
    # A mapped function taking elements of the index sort.
    "mapped_function_over_the_index_sort": """(declare-sort I 0)
(declare-sort E 0)
(declare-fun g (I) E)
(declare-fun a () (Array I I))
(declare-fun c () (Array I E))
(declare-fun i () I)
(assert (= c ((_ map g) a)))
(assert (not (= (select c i) (g (select a i)))))
(check-sat)
""",
    # No second sort, but a mapped predicate over Bool: the carrier holds the injected members.
    "mapped_predicate_over_bool": """(declare-sort I 0)
(declare-fun r (Bool) Bool)
(declare-fun a () (Array I Bool))
(declare-fun i () I)
(assert (select ((_ map r) a) i))
(assert (not (r (select a i))))
(check-sat)
""",
    # The extensionality witness of two sets, an index chosen with _m.s0_nonempty.
    "extensionality_over_the_index_sort": _SORTS + """(declare-fun q (E) Bool)
(assert (q e))
(assert (not (= (intersection a (union a b)) a)))
(check-sat)
""",
    # Sets as arguments of a function: injected into the carrier by the map of their Lean type.
    "sets_under_a_function": _SORTS + """(declare-fun c () (Array I Bool))
(declare-fun f ((Array I Bool)) E)
(assert (= (union a b) c))
(assert (not (= (f (union b a)) (f c))))
(check-sat)
""",
    # Int arguments and results next to the sets (qf_uflia).
    "int_arithmetic_next_to_sets": """(declare-sort I 0)
(declare-fun a () (Array I Bool))
(declare-fun i () I)
(declare-fun n (I) Int)
(declare-fun k (Int) I)
(assert (select (complement a) (k (+ (n i) 1))))
(assert (select a (k (+ 1 (n i)))))
(check-sat)
""",
    # A subset the rewriter decides (the others over a sort are rejected, see the subset tests).
    "subset_next_to_a_sort": _SORTS + """(declare-fun q (E) Bool)
(assert (not (subset (intersection a b) a)))
(assert (q e))
(check-sat)
""",
    # A subset and no map or set operator: the subset alone gives the sort its type.
    "subset_alone_next_to_a_sort": _SORTS + """(declare-fun q (E) Bool)
(assert (q e))
(assert (not (subset a a)))
(check-sat)
""",
    # No second sort, and a predicate over Bool that is mapped but never applied.
    "mapped_only_predicate_over_bool": """(declare-sort I 0)
(declare-fun r (Bool) Bool)
(declare-fun a () (Array I Bool))
(declare-fun b () (Array I Bool))
(assert (= a b))
(assert (not (= ((_ map r) a) ((_ map r) b))))
(check-sat)
""",
    # No second uninterpreted sort, but an enumeration, whose constructors inhabit the carrier.
    "enumeration_next_to_sets": """(declare-sort I 0)
(declare-datatypes ((Color 0)) (((red) (green))))
(declare-fun a () (Array I Bool))
(declare-fun c () (Array I Color))
(declare-fun i () I)
(assert (select (complement a) i))
(assert (or (select a i) (and (not (= (select c i) red)) (not (= (select c i) green)))))
(check-sat)
""",
}
_FRAGMENTS = {"int_arithmetic_next_to_sets": "qf_uflia", "int_indices_next_to_sorts": "qf_uflia"}

# The index sort alone in the carrier: the encoding without a type of its own.
ALONE_INPUTS = {
    "sets_over_the_only_sort": """(declare-sort I 0)
(declare-fun a () (Array I Bool))
(declare-fun b () (Array I Bool))
(declare-fun i () I)
(declare-fun g (I I) I)
(declare-fun q (I) Bool)
(assert (select (intersection a b) (g i i)))
(assert (or (not (select a (g i i))) (and (q i) (not (q i)))))
(check-sat)
""",
    # Maps over Int indices next to sorts: Int is its own type already.
    "int_indices_next_to_sorts": """(declare-sort I 0)
(declare-sort E 0)
(declare-fun a () (Array Int Bool))
(declare-fun m () (Array I E))
(declare-fun i () I)
(assert (select (complement a) 1))
(assert (or (select a 1) (not (= (select m i) (select m i)))))
(check-sat)
""",
}

# The input of the module's header. Its first assertion is false, so Z3 logs
# the others as written and refutes the input by the first alone; the set
# equality and the disequality are hypotheses of the theorem all the same.
ONE_ELEMENT_INDEX_SORT = """(declare-sort I 0)
(declare-sort E 0)
(declare-fun a () (Array I Bool))
(declare-fun i () I)
(declare-fun e1 () E)
(declare-fun e2 () E)
(declare-fun p () Bool)
(assert (and p (not p)))
(assert (= (store a i true) (complement (store a i false))))
(assert (not (= e1 e2)))
(check-sat)
"""

# Sets indexed by an enumeration, which the exporter rejects.
ENUMERATION_INDEX = """(declare-datatypes ((Color 0)) (((red) (green))))
(declare-fun a () (Array Color Bool))
(assert (select (complement a) red))
(assert (select a red))
(check-sat)
"""


def random_index_sort_instance(seed):
    """Random constraints over sets indexed by a sort I next to a sort E, or None if sat or undecided.

    Three to six assertions over members of set terms (unions,
    intersections, differences, complements, inserts and removals, ites) at
    index terms (constants, a function of E, a read of an array from E to
    I, ites), equalities of sets, of indices, and of terms of E (constants,
    a function of I, a function of sets), a predicate over E, and a
    predicate over Bool.
    """
    rng = random.Random(seed)
    sets = ["s%d" % k for k in range(3)]
    lines = ["(declare-sort I 0)", "(declare-sort E 0)", "(declare-fun i () I)", "(declare-fun j () I)",
             "(declare-fun e1 () E)", "(declare-fun e2 () E)", "(declare-fun g (I) E)", "(declare-fun h (E) I)",
             "(declare-fun f ((Array I Bool)) E)", "(declare-fun q (E) Bool)", "(declare-fun r (Bool) Bool)",
             "(declare-fun m () (Array E I))"]
    lines += ["(declare-fun %s () (Array I Bool))" % name for name in sets]

    def index(depth):
        choice = rng.randrange(6 if depth else 2)
        if choice < 2:
            return ("i", "j")[choice]
        if choice == 2:
            return "(h %s)" % element(depth - 1)
        if choice == 3:
            return "(select m %s)" % element(depth - 1)
        if choice == 4:
            return "(ite %s %s %s)" % (atom(depth - 1), index(depth - 1), index(depth - 1))
        return rng.choice(("i", "j"))

    def element(depth):
        choice = rng.randrange(5 if depth else 2)
        if choice < 2:
            return ("e1", "e2")[choice]
        if choice == 2:
            return "(g %s)" % index(depth - 1)
        if choice == 3:
            return "(f %s)" % term(depth - 1)
        return rng.choice(("e1", "e2"))

    def term(depth):
        choice = rng.randrange(9 if depth else 3)
        if choice < 3:
            return sets[choice]
        if choice == 3:
            return "(union %s %s)" % (term(depth - 1), term(depth - 1))
        if choice == 4:
            return "(intersection %s %s)" % (term(depth - 1), term(depth - 1))
        if choice == 5:
            return "(setminus %s %s)" % (term(depth - 1), term(depth - 1))
        if choice == 6:
            return "(complement %s)" % term(depth - 1)
        if choice == 7:
            return "(store %s %s %s)" % (term(depth - 1), index(depth - 1), rng.choice(("true", "false")))
        return "(ite %s %s %s)" % (atom(depth - 1), term(depth - 1), term(depth - 1))

    def atom(depth):
        choice = rng.randrange(8 if depth else 5)
        if choice < 3:
            return "(select %s %s)" % (term(depth), index(depth))
        if choice == 3:
            return "(= %s %s)" % (element(depth), element(depth))
        if choice == 4:
            return "(q %s)" % element(depth)
        if choice == 5:
            return "(= %s %s)" % (index(depth), index(depth))
        if choice == 6:
            return "(= %s %s)" % (term(depth), term(depth))
        return "(r %s)" % atom(depth - 1)

    def literal():
        return atom(2) if rng.randrange(2) else "(not %s)" % atom(2)

    for _ in range(rng.randrange(3, 7)):
        lines.append("(assert %s)" % (literal() if rng.randrange(3) else "(or %s %s)" % (literal(), literal())))
    lines.append("(check-sat)")
    source = "\n".join(lines) + "\n"
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set("timeout", 10000)
    solver.from_string(source)
    return source if solver.check() == z3.unsat else None


# Pinned unsatisfiable seeds of random_index_sort_instance, each with the
# index sort as a type of its own. 5 and 99: an ite between indices, a read
# of the array into the index sort, sets as arguments, pointwise facts.
# 237 and 1006: the extensionality witness of two sets. 333 and 409: indices
# as arguments (the injection) and functions into the index sort as well.
INDEX_SORT_SEEDS = (5, 99, 237, 333, 409, 1006)

# The sorts with a type of their own, by input.
_INDEX_SORTS = {name: ("I",) for name in INDEX_SORT_INPUTS}
_INDEX_SORTS.update({"two_index_sorts": ("I", "J"), "map_over_sort": ("I",), "map_distinct": ("I",),
                     "equality_map_commutes": ("I",), "map_under_function": ("E",)})
_STRUCTURE = ["  U : Type", "  elems : Nat -> U", "  funs : Nat -> List U -> U", "  preds : Nat -> List U -> Prop",
              "  bool : Prop -> U", "  S0 : Type", "  s0_nonempty : Nonempty S0", "  s0_elems : Nat -> S0",
              "  s0_funs : Nat -> List U -> S0", "  s0_inj : S0 -> U", "  arrs_s0b : Nat -> S0 -> Prop"]


def _source(name):
    return INDEX_SORT_INPUTS.get(name) or ALONE_INPUTS.get(name) or ARRAY_INPUTS[name]


def _structure(text):
    """The fields of the interpretation structure a certificate declares."""
    lines = text.split("\n")
    start = lines.index("structure Interpretation where")
    return lines[start + 1:lines.index("", start)]


class TestIndexSortValidation(unittest.TestCase):
    """Validation without Lean: which sorts get a type of their own, and the encoding."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")
        cls.certificates = {name: _export(_source(name)) for name in list(_INDEX_SORTS) + list(ALONE_INPUTS)}
        cls.texts = {name: proof_to_lean.reconstruct(_source(name), certificate)
                     for name, certificate in cls.certificates.items()}

    def test_which_sorts_get_a_type_of_their_own(self):
        for name, certificate in self.certificates.items():
            with self.subTest(name=name):
                graph = proof_to_lean._validate_graph(_source(name), certificate)
                self.assertEqual(graph.index_sorts, _INDEX_SORTS.get(name, ()))
                self.assertNotIn("sorry", self.texts[name])
                self.assertNotIn("axiom ", self.texts[name])

    def test_the_index_sort_alone_stays_the_carrier(self):
        """Without another inhabitant of the carrier the index sort is _m.U, as before."""
        text = self.texts["sets_over_the_only_sort"]
        self.assertIn('-- Uninterpreted sort "I" is the type _m.U;', text)
        self.assertIn("  arrs_ub : Nat -> U -> Prop", text)
        self.assertNotIn("S0", text)
        # Maps over Int indices: Lean's Int, whatever the carrier holds.
        text = self.texts["int_indices_next_to_sorts"]
        self.assertIn('-- Uninterpreted sorts "E", "I" are the one type _m.U;', text)
        self.assertIn("  arrs_ib : Nat -> Int -> Prop", text)
        self.assertNotIn("S0", text)

    def test_encoding(self):
        text = self.texts["sets_next_to_a_sort"]
        self.assertIn('-- Uninterpreted sort "I" is the type _m.S0 of its own, the index type of the pointwise '
                      "maps: constants _m.s0_elems, functions _m.s0_funs, arguments of functions and predicates "
                      "injected into _m.U by _m.s0_inj.", text)
        self.assertIn('-- Uninterpreted sort "E" is the type _m.U;', text)
        self.assertIn('-- Array sorts "(Array I Bool)" are functions _m.S0 -> Prop (_m.arrs_s0b);', text)
        self.assertEqual(_structure(text), _STRUCTURE)
        # A constant of the index sort, and one of the other sort.
        self.assertRegex(text, r"\ndef term_\d+ \(_atoms : Nat -> Prop\) \(_m : Interpretation\) : _m\.S0 := "
                               r"_m\.s0_elems \d+\n")
        self.assertRegex(text, r"\ndef term_\d+ \(_atoms : Nat -> Prop\) \(_m : Interpretation\) : _m\.U := "
                               r"_m\.elems \d+\n")
        self.assertRegex(text, r" : \(_m\.S0 -> Prop\) := \(_map2 And \(term_")
        # Arguments of the index sort are injected; a function into it is of its own family.
        text = self.texts["index_as_argument"]
        self.assertRegex(text, r" : _m\.U := _m\.funs 0 \[\(_m\.s0_inj \(term_\d+ _atoms _m\)\)\]\n")
        text = self.texts["function_into_the_index_sort"]
        self.assertRegex(text, r" : _m\.S0 := _m\.s0_funs 0 \[\(term_\d+ _atoms _m\)\]\n")
        text = self.texts["int_arithmetic_next_to_sets"]
        self.assertRegex(text, r" : _m\.S0 := _m\.s0_funs \d+ \[\(_m\.int \(term_\d+ _atoms _vars _m\)\)\]\n")
        self.assertRegex(text, r" : Int := _m\.ifuns \d+ \[\(_m\.s0_inj \(term_\d+ _atoms _vars _m\)\)\]\n")
        # An ite between indices, an array into the index sort, the elements a mapped function takes.
        self.assertRegex(self.texts["ite_over_the_index_sort"], r" : _m\.S0 := \(@ite _m\.S0 \(formula_")
        text = self.texts["elements_of_the_index_sort"]
        self.assertIn("  arrs_us0 : Nat -> U -> S0", text)
        self.assertRegex(text, r" : \(_m\.U -> _m\.S0\) := _m\.arrs_us0 \d+\n")
        text = self.texts["mapped_function_over_the_index_sort"]
        self.assertIn("(_map1 (fun (_v0 : _m.S0) => (_m.funs 0 [(_m.s0_inj _v0)])) (term_", text)
        self.assertIn("  arrs_s0s0 : Nat -> S0 -> S0", text)
        text = self.texts["mapped_predicate_over_bool"]
        self.assertIn("(_map1 (fun (_v0 : Prop) => (_m.preds 0 [(_m.bool _v0)])) (term_", text)
        # Sets as arguments, and the extensionality witness chosen in the index sort.
        text = self.texts["sets_under_a_function"]
        self.assertIn("  arrs_s0b_inj : (S0 -> Prop) -> U", text)
        self.assertRegex(text, r" : _m\.U := _m\.funs 0 \[\(_m\.arrs_s0b_inj \(term_\d+ _atoms _m\)\)\]\n")
        text = self.texts["extensionality_over_the_index_sort"]
        self.assertIn("(_array_diff _m.s0_nonempty (term_", text)
        self.assertNotIn("_m.nonempty", text)
        self.assertNotIn("  nonempty : Nonempty U", text)
        # Two index sorts, in the order of their names.
        text = self.texts["two_index_sorts"]
        self.assertIn('-- Uninterpreted sort "I" is the type _m.S0 of its own', text)
        self.assertIn('-- Uninterpreted sort "J" is the type _m.S1 of its own', text)
        self.assertIn("  arrs_s0b : Nat -> S0 -> Prop", text)
        self.assertIn("  arrs_s1b : Nat -> S1 -> Prop", text)
        self.assertNotIn("is the type _m.U", text)
        self.assertIn("-- No other uninterpreted sort: the type _m.U carries only the arguments", text)
        # The earlier documented inputs: elements of the other sort stay in the carrier.
        text = self.texts["map_over_sort"]
        self.assertIn("  arrs_s0u : Nat -> S0 -> U", text)
        self.assertIn("(_map2 (fun (_v0 : _m.U) (_v1 : _m.U) => (_m.funs 0 [_v0, _v1])) (term_", text)
        text = self.texts["map_under_function"]
        self.assertIn('-- Uninterpreted sort "E" is the type _m.S0 of its own', text)
        self.assertIn("  arrs_s0b_inj : (S0 -> Prop) -> U", text)

    def test_tampered_certificates_are_rejected(self):
        """The sorts are the input's: a certificate cannot merge the index sort with another."""
        source = INDEX_SORT_INPUTS["sets_next_to_a_sort"]
        certificate = copy.deepcopy(self.certificates["sets_next_to_a_sort"])
        for declaration in certificate["declarations"]:
            declaration["range"] = {"E": "I"}.get(declaration["range"], declaration["range"])
            declaration["domain"] = [{"E": "I"}.get(sort, sort) for sort in declaration["domain"]]
        graph = proof_to_lean._validate_graph(source, certificate)
        self.assertEqual(graph.index_sorts, ())  # I alone, were this the input's signature
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "does not match the original input"):
            proof_to_lean.reconstruct(source, certificate)

    def test_an_enumeration_as_index_sort_is_rejected(self):
        """An enumeration cannot be a type of its own: its constructors and case fields are over _m.U.

        The exporter's parser rejects arrays indexed by an enumeration, so no
        input reaches the reconstructor's guard; it is run here with the
        input's sort I classified as an enumeration.
        """
        with self.assertRaisesRegex(proof_certificate.ProofExportError, r"unsupported sort: Array\(Color, Bool\)"):
            _export(ENUMERATION_INDEX)
        source = INDEX_SORT_INPUTS["sets_next_to_a_sort"]
        with mock.patch.object(proof_to_lean, "is_enumeration_sort", lambda sort: sort.name() == "I"), \
                mock.patch.object(proof_to_lean, "enumeration_constructors", lambda sort: []):
            with self.assertRaisesRegex(proof_to_lean.ReconstructionError,
                                        "indexed by an enumeration are not supported: I$"):
                proof_to_lean.reconstruct(source, self.certificates["sets_next_to_a_sort"])

    def test_pinned_seeds_are_unsatisfiable(self):
        for seed in INDEX_SORT_SEEDS:
            source = random_index_sort_instance(seed)
            self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % seed)
            graph = proof_to_lean._validate_graph(source, _export(source))
            self.assertEqual(graph.index_sorts, ("I",), seed)


# The model of ONE_ELEMENT_INDEX_SORT's set equality and disequality, and the
# reason one carrier has none (filled with the namespace, the two hypotheses'
# definitions, and the indices of e1 and e2 in _m.elems).
_ONE_INDEX_MODEL = """
namespace %(namespace)s

def _one_index : Interpretation where
  U := Bool
  elems := fun n => decide (n = %(e1)d)
  funs := fun _ _ => true
  preds := fun _ _ => True
  bool := fun _ => true
  S0 := Unit
  s0_nonempty := Nonempty.intro ()
  s0_elems := fun _ => ()
  s0_funs := fun _ _ => ()
  s0_inj := fun _ => true
  arrs_s0b := fun _ _ => True

theorem _one_index_set_equality (_atoms : Nat -> Prop) : %(equality)s _atoms _one_index := by
  show _store (fun _ : Unit => True) () True = _map1 Not (_store (fun _ : Unit => True) () False)
  funext x
  cases x
  simp [_store, _map1]

theorem _one_index_disequality (_atoms : Nat -> Prop) : %(disequality)s _atoms _one_index := by
  show Not ((decide (%(e1)d = %(e1)d) : Bool) = decide (%(e2)d = %(e1)d))
  decide

theorem _one_carrier_contradiction (U : Type) (a : U -> Prop) (i e1 e2 : U)
    (h : _store a i True = _map1 Not (_store a i False)) (d : Not (e1 = e2)) : False := by
  have key : forall x : U, Not (x = i) -> False := by
    intro x hx
    have hx' := congrFun h x
    simp [_store, _map1, hx] at hx'
  by_cases h1 : e1 = i
  . exact key e2 (fun h2 => d (h1.trans h2.symm))
  . exact key e1 h1

end %(namespace)s
"""


class TestIndexSortLeanIntegration(unittest.TestCase):
    """End-to-end: clause log, certificate, Lean reconstruction, kernel check."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")

    def test_documented_inputs_verify(self):
        inputs = {**INDEX_SORT_INPUTS, **ALONE_INPUTS}
        lean_test_support.prefetch((source, _export(source)) for source in inputs.values())
        for name, source in inputs.items():
            with self.subTest(name=name):
                _check_in_lean(self, source, _FRAGMENTS.get(name, "qf_uf"))

    def test_pinned_random_instances_verify(self):
        sources = []
        for seed in INDEX_SORT_SEEDS:
            source = random_index_sort_instance(seed)
            self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % seed)
            sources.append((seed, source, _export(source)))
        lean_test_support.prefetch((source, certificate) for _, source, certificate in sources)
        for seed, source, certificate in sources:
            with self.subTest(seed=seed):
                _, report = lean_test_support.check(self, source, certificate)
                self.assertTrue(_STANDARD_AXIOMS in report or "does not depend on any axioms" in report, report)

    def test_a_one_element_index_sort_is_an_instance(self):
        """The theorem's hypotheses hold in a model whose index sort has one element and whose other sort has two.

        The set equality says that I has one element, the disequality that E
        has two. The interpretation _one_index is that model: S0 is Unit, U
        is Bool. Over one carrier the same two statements are contradictory
        (_one_carrier_contradiction, with the file's own _store and _map1),
        so a theorem stating them over _m.U alone would say nothing about
        this input.
        """
        source = ONE_ELEMENT_INDEX_SORT
        text = proof_to_lean.reconstruct(source, _export(source))
        self.assertEqual(_structure(text), _STRUCTURE)
        elements = {name: int(index) for index, name in re.findall(r'^-- Element (\d+): "(\w+)"$', text, re.M)}
        self.assertEqual(set(elements), {"i", "e1", "e2"})
        # The hypotheses in assertion order: the false one, the set equality, the disequality.
        hypotheses = re.findall(r"^    \(_h\d+ : \((formula_\d+) _atoms _m\)\)$", text, re.M)
        self.assertEqual(len(hypotheses), 3)
        equality, disequality = hypotheses[1:]
        self.assertRegex(text, r"\ndef %s .* := \(\(term_\d+ _atoms _m\) = \(term_\d+ _atoms _m\)\)\n" % equality)
        self.assertRegex(text, r"\ndef %s .* := \(Not \(formula_\d+ _atoms _m\)\)\n" % disequality)
        namespace = lean_test_support.namespace(source)
        theorems = ("_one_index_set_equality", "_one_index_disequality", "_one_carrier_contradiction")
        model = _ONE_INDEX_MODEL % {"namespace": namespace, "equality": equality, "disequality": disequality,
                                    "e1": elements["e1"], "e2": elements["e2"]}
        _, report = lean_test_support.check(self, source, text=text + model, theorems=("unsat",) + theorems)
        for theorem in theorems:
            self.assertIn("'%s.%s'" % (namespace, theorem), report)
        self.assertNotIn("sorryAx", report)


if __name__ == "__main__":
    unittest.main()
