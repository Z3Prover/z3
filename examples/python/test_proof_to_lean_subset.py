############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Tests for (subset a b) over sets (arrays with Bool elements) in the Lean
# reconstruction, certified through the sat.smt clause log.
# Lean reads (subset a b) as _subset a b, every member of a is one of b. Z3's
# rewriter makes (= (setminus a b) empty) of it, the map of and over a and
# the complement of b compared with the constant array of false; the theorem
# _subset_eq is that step, and the sets the rewriter then compares member by
# member get the pointwise facts of proof_to_lean._pointwise_map_facts.
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
import proof_clause_log
import lean_test_support
import proof_to_lean
from test_proof_to_lean_array import _check_in_lean, _declarations, _export, _without_facts
from test_proof_to_lean_lia import _STANDARD_AXIOMS, _hints, _z3_available

_SETS = """(declare-fun a () (Array Int Bool))
(declare-fun b () (Array Int Bool))
(declare-fun c () (Array Int Bool))
"""
_EMPTY = "((as const (Array Int Bool)) false)"
_FULL = "((as const (Array Int Bool)) true)"

# Documented inputs with subset, each unsatisfiable. All were rejected by the
# exporter before ("unsupported propositional operator: subset").
SUBSET_INPUTS = {
    # The rewriter's (= ((_ map and) a ((_ map not) b)) empty) is tied to
    # the assertion by a rewrite (_subset_eq), and a member of a outside b
    # refutes it by reads of the map and of the empty set.
    "member_outside": _SETS + """(assert (subset a b))
(assert (select a 1))
(assert (not (select b 1)))
(check-sat)
""",
    "member_outside_at_a_variable": _SETS + """(declare-fun i () Int)
(assert (subset a b))
(assert (subset b c))
(assert (select a i))
(assert (not (select c i)))
(check-sat)
""",
    "transitive": _SETS + """(assert (subset a b))
(assert (subset b c))
(assert (not (subset a c)))
(check-sat)
""",
    "antisymmetric": _SETS + """(assert (subset a b))
(assert (subset b a))
(assert (not (= a b)))
(check-sat)
""",
    "union_of_subsets": _SETS + """(assert (subset a c))
(assert (subset b c))
(assert (not (subset (union a b) c)))
(check-sat)
""",
    "below_an_intersection": _SETS + """(assert (subset c a))
(assert (subset c b))
(assert (not (subset c (intersection a b))))
(check-sat)
""",
    "equated_with_a_union": _SETS + """(assert (= a (union b c)))
(assert (not (subset b a)))
(check-sat)
""",
    # The difference is empty at every member (a fact _pws : _subset a b, by
    # an auxiliary theorem over the members). The rewriter decides the first
    # and the two below a set of their own; the others keep its equality.
    "reflexive": _SETS + """(assert (not (subset a a)))
(check-sat)
""",
    "intersection_below_its_set": _SETS + """(assert (not (subset (intersection a b) a)))
(check-sat)
""",
    "difference_below_its_set": _SETS + """(assert (not (subset (setminus a b) a)))
(check-sat)
""",
    "below_its_union": _SETS + """(assert (not (subset a (union a b))))
(check-sat)
""",
    "empty_below_any": _SETS + "(assert (not (subset %s a)))\n(check-sat)\n" % _EMPTY,
    "any_below_full": _SETS + "(assert (not (subset a %s)))\n(check-sat)\n" % _FULL,
    # Decided false: the difference is full at every member, so the subset
    # fails at any index (_pwsn, the index sort inhabited).
    "full_below_empty": _SETS + "(assert (subset %s %s))\n(check-sat)\n" % (_FULL, _EMPTY),
    "everything_below_nothing": _SETS + """(assert (subset (union a (complement a)) (setminus b b)))
(check-sat)
""",
    # Decided false at a stored index: the rewriter pulls the store out of
    # the map and compares it with the empty set there (_pwsn at 1).
    "full_below_a_removal": _SETS + "(assert (subset %s (store a 1 false)))\n(check-sat)\n" % _FULL,
    "an_insert_below_its_removal": _SETS + "(assert (subset (store a 1 true) (store a 1 false)))\n(check-sat)\n",
    "an_insert_below_empty": _SETS + """(declare-fun i () Int)
(assert (subset (store a i true) (setminus b b)))
(check-sat)
""",
    # False at a stored index, but the rewriter does not pull a store out
    # from under a union and keeps its equality: the failure at the index
    # (_pwsn) next to the difference stated equal to the union (_pws).
    "inserts_under_a_union_below_empty": _SETS + """(assert (subset (union (store a 0 true) (store b 1 true)) %s))
(check-sat)
""" % _EMPTY,
    # Decided false by the default values: the difference is full off the
    # stored indices, so the subset fails at an index that is none of them
    # (_pwsn at an index outside the list of the stored ones).
    "full_below_a_singleton": "(assert (subset %s (store %s 0 true)))\n(check-sat)\n" % (_FULL, _EMPTY),
    "full_below_a_pair": """(declare-fun i () Int)
(assert (subset %s (store (store %s 0 true) i true)))
(check-sat)
""" % (_FULL, _EMPTY),
    "full_below_a_singleton_of_reals": """(assert (subset ((as const (Array Real Bool)) true)
                (store ((as const (Array Real Bool)) false) 0.5 true)))
(check-sat)
""",
    # Constant arrays of Boolean values other than true and false: the
    # rewriter folds the subset to a formula over the values, which the
    # subset is at any index (_pwsv).
    "between_constant_arrays": """(declare-fun p () Bool)
(assert (subset ((as const (Array Int Bool)) p) ((as const (Array Int Bool)) (not p))))
(assert p)
(check-sat)
""",
    "between_constant_arrays_of_two_values": """(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (not (subset ((as const (Array Int Bool)) (and p q)) ((as const (Array Int Bool)) p))))
(check-sat)
""",
    # The rewriter simplifies the difference to another set than the map
    # _subset_eq writes (a itself for a minus the empty set, the complement
    # of a for that minus a, (intersection a b) for a minus a complement):
    # the two are stated equal (_pws : _map2 And a (_map1 Not ...) = ...).
    "below_empty": _SETS + """(declare-fun i () Int)
(assert (subset a %s))
(assert (select a i))
(check-sat)
""" % _EMPTY,
    "complement_below_its_set": _SETS + """(assert (subset (complement a) a))
(assert (not (select a 0)))
(check-sat)
""",
    "below_a_complement": _SETS + """(assert (subset a (complement b)))
(assert (select a 3))
(assert (select b 3))
(check-sat)
""",
    "below_a_double_complement": _SETS + """(assert (subset a (complement (complement b))))
(assert (select a 3))
(assert (not (select b 3)))
(check-sat)
""",
    "of_an_insert": _SETS + """(assert (subset (store a 2 true) b))
(assert (not (select b 2)))
(check-sat)
""",
    "of_an_insert_at_a_variable": _SETS + """(declare-fun i () Int)
(assert (subset (store a i true) b))
(assert (not (select b i)))
(check-sat)
""",
    "two_levels": _SETS + """(declare-fun d () (Array Int Bool))
(assert (subset (union a b) (intersection c d)))
(assert (select b 7))
(assert (not (select d 7)))
(check-sat)
""",
    # A subset below connectives, and as a Boolean argument of a function.
    "under_a_disjunction": _SETS + """(declare-fun p () Bool)
(assert (or p (subset a b)))
(assert (not p))
(assert (select a 0))
(assert (not (select b 0)))
(check-sat)
""",
    "under_an_ite": _SETS + """(declare-fun p () Bool)
(assert (ite p (subset a b) (subset a c)))
(assert (select a 0))
(assert (not (select b 0)))
(assert (not (select c 0)))
(check-sat)
""",
    "as_a_boolean_argument": _SETS + """(declare-fun f (Bool) Int)
(assert (= a b))
(assert (not (= (f (subset a c)) (f (subset b c)))))
(check-sat)
""",
    # Subset against what Z3 makes of it, and against the full implication map.
    "is_an_empty_difference": _SETS + "(assert (not (= (subset a b) (= (setminus a b) %s))))\n(check-sat)\n" % _EMPTY,
    "is_a_full_implication": _SETS + "(assert (not (= (subset a b) (= ((_ map =>) a b) %s))))\n(check-sat)\n" % _FULL,
    "real_indices": """(declare-fun a () (Array Real Bool))
(declare-fun b () (Array Real Bool))
(assert (subset a b))
(assert (select a 0.5))
(assert (not (select b 0.5)))
(check-sat)
""",
    # Over an uninterpreted index sort a subset the rewriter decides
    # verifies (no constant array is left in the certificate). Decided
    # false, it fails at the value of the interpretation's first constant
    # (_m.elems 0: the carrier is not stated nonempty otherwise).
    "decided_over_a_sort": """(declare-sort U 0)
(declare-fun a () (Array U Bool))
(assert (not (subset a a)))
(check-sat)
""",
    "decided_false_over_a_sort": """(declare-sort U 0)
(declare-fun a () (Array U Bool))
(assert (subset (union a (complement a)) (setminus a a)))
(check-sat)
""",
    # After an assertion that simplifies to false Z3 logs the others as
    # written, and its array solver states the subset's own axiom, (subset a
    # b) against (= (setminus a b) empty), as two array lemmas.
    "after_false": _SETS + """(assert (= 1 2))
(assert (subset a b))
(assert (select a 1))
(check-sat)
""",
    "after_false_over_operators": _SETS + """(assert (= 1 2))
(assert (subset (union a b) (complement c)))
(assert (not (subset (store a 1 true) b)))
(check-sat)
""",
}
# Sets of integers are qf_uflia (the index sort is Int).
_FRAGMENTS = {"real_indices": "qf_uflra", "full_below_a_singleton_of_reals": "qf_uflra",
              "decided_over_a_sort": "qf_uf", "decided_false_over_a_sort": "qf_uf"}
_SET_SORTS = {"qf_uflia": "(Array Int Bool)", "qf_uflra": "(Array Real Bool)", "qf_uf": "(Array U Bool)"}

# Inputs with subset that stay rejected, with the error. The first four by
# the exporter (a pseudo-Boolean constraint counts Boolean variables only;
# sets indexed by bit-vectors or an enumeration are no supported sort);
# the others by the reconstructor, whose certificate cannot
# carry the constant array of the rewriter's (= (setminus a b) empty) over
# an index sort that may be finite (constant arrays are Int- or
# Real-indexed, see proof_to_lean._declaration).
REJECTED_SUBSET_INPUTS = {
    "sets_of_sets": ("""(declare-fun a () (Array (Array Int Bool) Bool))
(assert (not (subset a a)))
(check-sat)
""", proof_certificate.ProofExportError, "maps and set operators over arrays indexed by arrays are not supported"),
    "next_to_pseudo_boolean": (_SETS + """(declare-fun p () Bool)
(assert ((_ at-most 0) p (subset a b)))
(assert (subset a b))
(check-sat)
""", proof_certificate.ProofExportError, "pseudo-Boolean arguments must be Boolean variables or their negations"),
    "over_bit_vectors": ("""(declare-fun a () (Array (_ BitVec 2) Bool))
(assert (not (subset a a)))
(check-sat)
""", proof_certificate.ProofExportError, r"^unsupported sort: Array\(BitVec\(2\), Bool\) "),
    "over_an_enumeration": ("""(declare-datatypes ((C 0)) (((red) (green))))
(declare-fun a () (Array C Bool))
(assert (not (subset a a)))
(check-sat)
""", proof_certificate.ProofExportError, r"^unsupported sort: Array\(C, Bool\) "),
    "over_a_sort": ("""(declare-sort U 0)
(declare-fun a () (Array U Bool))
(declare-fun b () (Array U Bool))
(declare-fun u () U)
(assert (subset a b))
(assert (select a u))
(assert (not (select b u)))
(check-sat)
""", proof_to_lean.ReconstructionError, "invalid constant array declaration"),
    "over_bool_indices": ("""(declare-fun a () (Array Bool Bool))
(declare-fun b () (Array Bool Bool))
(assert (subset a b))
(assert (select a true))
(assert (not (select b true)))
(check-sat)
""", proof_to_lean.ReconstructionError, "invalid constant array declaration"),
}


def random_subset_instance(seed, unsimplified=False):
    """Random constraints with subset over four sets of integers, or None if sat.

    Two to five assertions: a subset between set terms (unions,
    intersections, differences, complements, inserts and removals, the
    empty and the full set), plain, negated, or in a disjunction with a
    member, members read at 0, 1, i, or j, and equalities between a set and
    a set term. With unsimplified, the first assertion is (= 1 2): Z3 then
    logs the others as written and its array solver states each subset's
    own axiom (the input is unsatisfiable whatever the others are).
    """
    rng = random.Random(seed)
    sets = ["s%d" % k for k in range(4)]
    indices = ["i", "j", "0", "1"]
    lines = ["(declare-fun i () Int)", "(declare-fun j () Int)"]
    lines += ["(declare-fun %s () (Array Int Bool))" % name for name in sets]
    if unsimplified:
        lines.append("(assert (= 1 2))")

    def term(depth):
        choice = rng.randrange(9 if depth else 3)
        if choice < 3:
            return rng.choice(sets)
        if choice == 3:
            return "(union %s %s)" % (term(depth - 1), term(depth - 1))
        if choice == 4:
            return "(intersection %s %s)" % (term(depth - 1), term(depth - 1))
        if choice == 5:
            return "(setminus %s %s)" % (term(depth - 1), term(depth - 1))
        if choice == 6:
            return "(complement %s)" % term(depth - 1)
        if choice == 7:
            return "(store %s %s %s)" % (term(depth - 1), rng.choice(indices), rng.choice(("true", "false")))
        return "((as const (Array Int Bool)) %s)" % rng.choice(("true", "false"))

    def member():
        return "(select %s %s)" % (rng.choice(sets), rng.choice(indices))

    for _ in range(rng.randrange(2, 6)):
        kind = rng.randrange(8)
        subset = "(subset %s %s)" % (term(2), term(2)) if kind % 2 else "(subset %s %s)" % (term(1), term(1))
        if kind < 3:
            lines.append("(assert %s)" % subset)
        elif kind == 3:
            lines.append("(assert (not %s))" % subset)
        elif kind == 4:
            lines.append("(assert (or %s %s))" % (subset, member()))
        elif kind == 5:
            lines.append("(assert %s)" % member())
        elif kind == 6:
            lines.append("(assert (not %s))" % member())
        else:
            lines.append("(assert (= %s %s))" % (rng.choice(sets), term(1)))
    lines.append("(check-sat)")
    source = "\n".join(lines) + "\n"
    if unsimplified:
        return source
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set("timeout", 10000)
    solver.from_string(source)
    return source if solver.check() == z3.unsat else None


# Pinned unsatisfiable seeds of random_subset_instance. 17: a subset decided
# false at every index. 103: one decided true. 105: a difference the
# rewriter simplifies to another map. 628 and 1472: a subset decided false
# at a stored index, the two Lean failures of the first sweep of seeds
# 1-1500 (iteration 129's macOS build) before that fact was stated. 1791
# and 2233: a subset that fails at a stored index while the rewriter keeps
# its equality (a store under a union), and 2769: one decided false by the
# default values, the three Lean failures of seeds 1501-3000 before those
# facts were stated. Of the 1105 unsatisfiable seeds of 1-5000, 1104
# verify; seed 1089 does not: the replay ties the clause of its subset to
# another assertion equivalent to it (a set equated with the full set), a
# rewrite between two set equalities that fails without subset too.
SUBSET_SEEDS = (17, 103, 105, 628, 1472, 1791, 2233, 2769)
# Seeds of random_subset_instance(seed, unsimplified=True), which are all
# unsatisfiable: subsets logged as written with the array solver's axioms.
# Seeds 1-400 all verify.
UNSIMPLIFIED_SUBSET_SEEDS = (2, 5, 11)


def _lines(text, pattern):
    """The tactic lines of a Lean text that match pattern at their start."""
    compiled = re.compile(pattern)
    return [line.lstrip(" |(") for line in text.split("\n") if compiled.match(line.lstrip(" |("))]


def _steps(text):
    """The tactic lines of each private theorem of a Lean text, by the theorem's name."""
    steps, name = {}, None
    for line in text.split("\n"):
        match = re.match(r"private theorem (\S+)", line)
        if match:
            name = match.group(1)
        elif name is not None and line.strip():
            steps.setdefault(name, []).append(line.lstrip(" |("))
    return steps


class TestSubsetValidation(unittest.TestCase):
    """Validation without Lean: classification, the log, the replay, the encoding, and rejections."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")
        cls.certificates = {name: _export(source) for name, source in SUBSET_INPUTS.items()}
        cls.texts = {name: proof_to_lean.reconstruct(SUBSET_INPUTS[name], certificate)
                     for name, certificate in cls.certificates.items()}

    def test_fragments_and_declarations(self):
        for name, certificate in self.certificates.items():
            with self.subTest(name=name):
                self.assertEqual(certificate["fragment"], _FRAGMENTS.get(name, "qf_uflia"))
                subsets = _declarations(certificate, z3.Z3_OP_SET_SUBSET)
                self.assertEqual(len(subsets), 1)
                sort = _SET_SORTS[_FRAGMENTS.get(name, "qf_uflia")]
                self.assertEqual(subsets[0], {"kind": z3.Z3_OP_SET_SUBSET, "name": "subset",
                                              "domain": [sort, sort], "range": "Bool", "parameters": []})

    def test_the_log_holds_the_rewriters_equality(self):
        """Z3 logs (= (setminus a b) empty) over maps for a subset, and the subset itself after a false assertion."""
        executable = proof_certificate.default_z3_executable()
        log = proof_clause_log.run_clause_log(executable, SUBSET_INPUTS["member_outside"].replace("(check-sat)", ""),
                                              60)
        self.assertNotIn("subset", log)
        self.assertIn("(_ map (and (Bool Bool) Bool))", log)
        self.assertIn("((as const (Array Int Bool)) false)", log)
        certificate = self.certificates["member_outside"]
        self.assertEqual(certificate["rule_counts"].get("rewrite"), 1)
        self.assertEqual(len(_declarations(certificate, z3.Z3_OP_CONST_ARRAY)), 1)
        log = proof_clause_log.run_clause_log(executable, SUBSET_INPUTS["after_false"].replace("(check-sat)", ""), 60)
        self.assertIn("(subset a b)", log)
        self.assertIn("(setminus a b)", log)
        # The array solver's axiom of the subset, one clause each way.
        self.assertEqual(len(re.findall(r"\(define-const \$\d+ Proof \(array ", log)), 2)
        self.assertEqual(_hints(self.certificates["after_false"]), {"array"})
        self.assertEqual(self.certificates["after_false"]["rule_counts"].get("th-lemma"), 2)

    def test_the_replay_reads_subset(self):
        context = z3.Context()
        assertions, _ = proof_certificate.parse_assertions(_SETS + """(declare-fun e () (Array Int Int))
(declare-fun r () (Array Real Bool))
(assert (select a 0))
(assert (select b (select e 0)))
(assert (select c 0))
(assert (select r 0.0))
(check-sat)
""", context, integer=True)
        terms = proof_clause_log._Terms(context, assertions)
        built = terms.build(["subset", "a", ["union", "b", "c"]])
        self.assertEqual(built.decl().kind(), z3.Z3_OP_SET_SUBSET)
        self.assertEqual(built.sexpr(), "(subset a ((as union (Array Int Bool)) b c))")
        self.assertEqual(terms.build(["subset", "r", "r"]).decl().kind(), z3.Z3_OP_SET_SUBSET)
        for sexpr in (["subset", "a"], ["subset", "a", "b", "c"], ["subset", "a", "r"], ["subset", "a", "0"],
                      ["subset", "0", "a"], ["subset", "e", "e"]):
            with self.subTest(sexpr=sexpr):
                with self.assertRaisesRegex(proof_certificate.ProofExportError,
                                            "^unsupported operator in the clause log: subset$"):
                    terms.build(sexpr)
        # Z3 itself rejects a subset of arrays that are not sets.
        with self.assertRaisesRegex(z3.Z3Exception, "expecting boolean range"):
            z3.parse_smt2_string("(declare-fun e () (Array Int Int))(assert (subset e e))", ctx=context)

    def test_rejected_inputs(self):
        for name, (source, error, message) in REJECTED_SUBSET_INPUTS.items():
            with self.subTest(name=name):
                with self.assertRaisesRegex(error, message):
                    proof_to_lean.reconstruct(source, _export(source))
        # The legacy proof object certifies no arrays, so no subset.
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "arrays are certified through the clause log"):
            proof_certificate.export_certificate(SUBSET_INPUTS["member_outside"], None)

    def test_encoding(self):
        definition = "def _subset {I : Type} (a b : I -> Prop) : Prop := forall _i : I, a _i -> b _i"
        rewrite = ("private theorem _subset_eq {I : Type} (a b : I -> Prop) :\n"
                   "    _subset a b = (_map2 And a (_map1 Not b) = _const_array I False) := by")
        for name, text in self.texts.items():
            with self.subTest(name=name):
                self.assertEqual(text.count(definition), 1)
                self.assertEqual(len(re.findall(r"^def formula_\d+ .* := \(_subset \(term_\d+ [^()]*\) "
                                                r"\(term_\d+ [^()]*\)\)$", text, re.M)),
                                 SUBSET_INPUTS[name].count("(subset "))
                # The rewriter's form is stated only next to a constant array
                # (the empty set of that form), where _const_array is defined.
                constants = bool(_declarations(self.certificates[name], z3.Z3_OP_CONST_ARRAY))
                self.assertEqual(text.count(rewrite), int(constants))
                self.assertEqual(bool(_lines(text, r"have _sb\d+ := _subset_eq ")), constants)
                self.assertNotIn("sorry", text)
                self.assertNotIn("axiom ", text)
        for name in ("reflexive", "intersection_below_its_set", "difference_below_its_set", "decided_over_a_sort",
                     "decided_false_over_a_sort"):
            self.assertNotIn("_const_array", self.texts[name])
        # Without subset the prelude has neither.
        source = SUBSET_INPUTS["member_outside"].replace("(subset a b)", "(= (setminus a b) %s)" % _EMPTY)
        text = proof_to_lean.reconstruct(source, _export(source))
        self.assertNotIn("_subset", text)

    def test_subset_facts(self):
        """The facts of a subset: the rewriter's form, and what the difference is member by member."""
        term = r"\(\(term_\d+ _atoms _vars _m\)\)"
        # Tied to the rewriter's equality by _subset_eq alone.
        text = self.texts["member_outside"]
        # (Node numbers follow the order Z3 logs the clauses in: not pinned.)
        def all_match(lines, pattern):
            self.assertTrue(lines)
            for line in lines:
                self.assertRegex(line, pattern)

        all_match(_lines(text, r"have _sb\d+ "), r"^have _sb\d+ := _subset_eq %s %s$" % (term, term))
        # The map of that equality is the difference as _subset_eq writes it.
        all_match(_lines(text, r"have _pws"), r"^have _pws\d+ : _map2 And %s \(_map1 Not %s\) = %s := "
                                              r"funext \(fun _i => rfl\)$" % (term, term, term))
        # Decided true: the subset itself, the same set twice by the identity.
        all_match(_lines(self.texts["reflexive"], r"have _pws"),
                  r"^have _pws\d+ : _subset (%s) \1 := fun _i => fun _h => _h$" % term)
        text = self.texts["intersection_below_its_set"]
        self.assertRegex(text, r"\nprivate theorem rewrite_\d+_pw0 \(_p0 _p1 : Prop\) :\n"
                               r"    \(\(And _p0 _p1\) -> _p0\) := by grind\n")
        all_match(_lines(text, r"have _pws"),
                  r"^have _pws\d+ : _subset %s %s := fun _i => \(rewrite_\d+_pw0 \(_select %s _i\) "
                  r"\(_select %s _i\)\)$" % (term, term, term, term))
        self.assertRegex(self.texts["below_its_union"], r"have _pws\d+ : _subset %s %s := fun _i => "
                                                        r"\(rewrite_\d+_pw\d+ " % (term, term))
        # Decided false at any index, and at a stored one.
        text = self.texts["full_below_empty"]
        self.assertIn(" :\n    (And True (Not False)) := by grind\n", text)
        facts = _lines(text, r"have _pwsn")
        self.assertTrue(facts)
        for fact in facts:
            self.assertRegex(fact, r"^have _pwsn\d+ : _subset %s %s -> False := fun _h => Nonempty.elim "
                                   r"\(Nonempty.intro \(0 : Int\)\) \(fun _i => \(rewrite_\d+_pw0\).2 "
                                   r"\(_h _i \(rewrite_\d+_pw0\).1\)\)$" % (term, term))
        text = self.texts["full_below_a_removal"]
        self.assertIn(" (_p0 _p1 : Prop) :\n    (_p0 -> (And True (Not (@ite Prop _p0 (Classical.propDecidable _) "
                      "False _p1)))) := by grind\n", text)
        facts = _lines(text, r"have _pwsn")
        self.assertTrue(facts)
        one = r"\(\(\(1 : Int\)\)\)"
        for fact in facts:
            self.assertRegex(fact, r"^have _pwsn\d+ : _subset %s %s -> False := fun _h => \(\(rewrite_\d+_pw\d+ "
                                   r"\(%s = %s\) \(_select %s %s\)\) rfl\).2 "
                                   r"\(_h %s \(\(rewrite_\d+_pw\d+ .*\) rfl\).1\)$"
                             % (term, term, one, one, term, one, one))
        # The difference simplified to another map: the two stated equal.
        for name in ("below_empty", "complement_below_its_set", "below_a_double_complement"):
            facts = _lines(self.texts[name], r"have _pws\d+ : _map2")
            self.assertTrue(facts, name)
            for fact in facts:
                self.assertRegex(fact, r"^have _pws\d+ : _map2 And %s \(_map1 Not %s\) = %s := funext \(fun _i => "
                                       r"propext \(rewrite_\d+_pw\d+ .*\)\)$" % (term, term, term))
        self.assertIn(" (_p0 : Prop) :\n    (Iff (And _p0 (Not False)) _p0) := by grind\n", self.texts["below_empty"])
        # False at a stored index under a union, where the rewriter keeps its
        # equality: the failure at the index and the difference's equality.
        text = self.texts["inserts_under_a_union_below_empty"]
        all_match(_lines(text, r"have _pwsn"), r"^have _pwsn\d+ : _subset %s %s -> False := fun _h => "
                                               r"\(\(rewrite_\d+_pw\d+ .*\) rfl\)\.2 " % (term, term))
        all_match(_lines(text, r"have _pws\d+ : _map2"),
                  r"^have _pws\d+ : _map2 And %s \(_map1 Not %s\) = %s := funext \(fun _i => "
                  r"propext \(rewrite_\d+_pw\d+ .*\)\)$" % (term, term, term))
        # Decided false by the default values: at an index off the stored ones.
        text = self.texts["full_below_a_pair"]
        self.assertIn(" (_p0 _p1 : Prop) :\n    ((Not _p0) -> (Not _p1) -> (And True (Not ", text)
        all_match(_lines(text, r"have _pwsn"),
                  r"^have _pwsn\d+ : _subset %s %s -> False := fun _h => Exists.elim \(_int_unbounded "
                  r"\(\[\(\(\(0 : Int\)\)\), \(_vars 0\)\] : List Int\)\) \(fun _i _f => "
                  r"\(\(rewrite_\d+_pw\d+ \(_i = \(\(\(0 : Int\)\)\)\) \(_i = \(_vars 0\)\)\) "
                  r"\(fun _e => _f \(_e ▸ List.Mem.head _\)\) "
                  r"\(fun _e => _f \(_e ▸ List.Mem.tail _ \(List.Mem.head _\)\)\)\)\.2 \(_h _i .*\.1\)\)$"
                  % (term, term))
        all_match(_lines(self.texts["full_below_a_singleton_of_reals"], r"have _pwsn"),
                  r"^have _pwsn\d+ : .* Exists.elim \(_rat_unbounded \(\[.*\] : List Rat\)\) ")
        # Constant arrays of values: the subset is the implication between them.
        all_match(_lines(self.texts["between_constant_arrays"], r"have _pwsv"),
                  r"^have _pwsv\d+ : _subset %s %s = \(\(_atoms 0\) -> \(\(Not \(_atoms 0\)\)\)\) := "
                  r"propext \(Iff.intro \(fun _h => Nonempty.elim \(Nonempty.intro \(0 : Int\)\) "
                  r"\(fun _i => _h _i\)\) \(fun _h _ => _h\)\)$" % (term, term))
        # Over an uninterpreted index sort the carrier's inhabitant is a
        # constant's value: the interpretation has no nonempty field here.
        text = self.texts["decided_false_over_a_sort"]
        self.assertNotIn("nonempty : Nonempty U", text)
        sort_term = r"\(\(term_\d+ _atoms _m\)\)"
        all_match(_lines(text, r"have _pwsn"),
                  r"^have _pwsn\d+ : _subset %s %s -> False := fun _h => Nonempty.elim "
                  r"\(Nonempty.intro \(_m.elems 0\)\) \(fun _i => " % (sort_term, sort_term))
        # An euf lemma is a congruence: relabelled as one, the array solver's
        # subset axiom gets no subset fact.
        self.assertEqual(len(_lines(self.texts["after_false"], r"have _sb\d+ ")), 2)
        relabelled = copy.deepcopy(self.certificates["after_false"])
        for declaration in relabelled["declarations"]:
            if declaration["name"] == "th-lemma":
                declaration["parameters"] = ["euf"]
        self.assertFalse(_lines(proof_to_lean.reconstruct(SUBSET_INPUTS["after_false"], relabelled),
                                r"have _sb\d+ "))

    def test_array_lemmas_over_subset(self):
        """The array solver's subset axiom passes the array lemma check; other atoms are still rejected."""
        certificate = self.certificates["after_false"]
        graph = proof_to_lean._validate_graph(SUBSET_INPUTS["after_false"], certificate)
        lemmas = [node for node in range(len(graph.nodes)) if graph.kind(node) == z3.Z3_OP_PR_TH_LEMMA]
        self.assertEqual(len(lemmas), 2)
        for node in lemmas:
            self.assertEqual(graph.decl(node).parameters, ("array",))
            literals = graph.clause(graph.conclusion(node))
            atoms = [graph.arguments(literal)[0] if graph.kind(literal) == z3.Z3_OP_NOT else literal
                     for literal in literals]
            self.assertEqual(sorted(graph.kind(atom) for atom in atoms),
                             sorted([z3.Z3_OP_SET_SUBSET, z3.Z3_OP_EQ]))
            proof_to_lean._check_th_lemma(graph, node)
        text = self.texts["after_false"]
        self.assertEqual(len(_lines(text, r"have _sb\d+ := _subset_eq ")), 2)
        # A lemma over a member alone is not an array axiom instance.
        tampered = copy.deepcopy(certificate)
        member = next(index for index, node in enumerate(tampered["nodes"])
                      if tampered["declarations"][node["declaration"]]["kind"] == z3.Z3_OP_SELECT)
        tampered["nodes"][lemmas[0]]["arguments"] = [member]
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "array th-lemma literals must be equalities"):
            proof_to_lean.reconstruct(SUBSET_INPUTS["after_false"], tampered)

    def _rejects(self, name, mutate, message):
        certificate = copy.deepcopy(self.certificates[name])
        mutate(certificate)
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, message):
            proof_to_lean.reconstruct(SUBSET_INPUTS[name], certificate)

    def test_tampered_subsets_are_rejected(self):
        def subset(certificate):
            return next(d for d in certificate["declarations"] if d["kind"] == z3.Z3_OP_SET_SUBSET)

        def field(key, value):
            def mutate(certificate):
                subset(certificate)[key] = value
            return mutate

        def swapped(certificate):
            node = next(node for node in certificate["nodes"]
                        if certificate["declarations"][node["declaration"]]["kind"] == z3.Z3_OP_SET_SUBSET)
            node["arguments"].reverse()

        def relabelled(kind, name):
            def mutate(certificate):
                declaration = subset(certificate)
                declaration["kind"], declaration["name"] = kind, name
            return mutate

        sets = "(Array Int Bool)"
        for mutate in (field("name", "superset"), field("name", "="), field("domain", [sets]),
                       field("domain", [sets, sets, sets]), field("domain", [sets, "Bool"]),
                       field("domain", ["Bool", "Bool"]), field("domain", ["Int", "Int"]),
                       field("domain", [sets, "(Array Int Int)"]), field("domain", ["(Array Int Int)"] * 2),
                       field("domain", ["(Array (Array Int Bool) Bool)"] * 2)):
            self._rejects("member_outside", mutate, "invalid subset declaration|unsupported array sort")
        self._rejects("member_outside", field("parameters", ["0"]), "invalid or parameterized native declaration")
        self._rejects("member_outside", field("range", "Int"), "unsupported arithmetic declaration")
        self._rejects("member_outside", field("range", sets), "unsupported array declaration")
        # Another statement than the input's.
        self._rejects("member_outside", swapped, "certificate assertions do not match the original input")
        self._rejects("member_outside", relabelled(z3.Z3_OP_EQ, "="),
                      "certificate assertions do not match the original input")
        self._rejects("member_outside", relabelled(z3.Z3_OP_DISTINCT, "distinct"),
                      "certificate assertions do not match the original input")

    def test_pinned_seeds_are_unsatisfiable(self):
        for seed in SUBSET_SEEDS:
            source = random_subset_instance(seed)
            self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % seed)
            self.assertIn("(subset ", source)
        # The route of seeds 628 and 1472: a subset decided false at a stored index.
        for seed in (628, 1472):
            source = random_subset_instance(seed)
            text = proof_to_lean.reconstruct(source, _export(source))
            self.assertTrue(_lines(text, r"have _pwsn\d+ : _subset .* rfl\)\.1\)$"), seed)
        # 1791 and 2233: that failure next to the equality the rewriter keeps.
        for seed in (1791, 2233):
            source = random_subset_instance(seed)
            text = proof_to_lean.reconstruct(source, _export(source))
            both = [name for name, lines in _steps(text).items()
                    if any(re.match(r"have _pwsn\d+ : _subset .* rfl\)\.1\)$", line) for line in lines)
                    and any(re.match(r"have _pws\d+ : _map2 ", line) for line in lines)]
            self.assertTrue(both, seed)
        # 2769: a subset decided false by the default values.
        source = random_subset_instance(2769)
        text = proof_to_lean.reconstruct(source, _export(source))
        self.assertTrue(_lines(text, r"have _pwsn\d+ : _subset .* Exists.elim \(_int_unbounded "))


class TestSubsetLeanIntegration(unittest.TestCase):
    """End-to-end: clause log, certificate, Lean reconstruction, kernel check."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")

    def test_documented_inputs_verify(self):
        lean_test_support.prefetch((source, _export(source)) for source in SUBSET_INPUTS.values())
        for name, source in SUBSET_INPUTS.items():
            with self.subTest(name=name):
                _check_in_lean(self, source, _FRAGMENTS.get(name, "qf_uflia"))

    def test_pinned_random_instances_verify(self):
        sources = []
        for seed in SUBSET_SEEDS:
            source = random_subset_instance(seed)
            self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % seed)
            sources.append((seed, source, _export(source)))
        for seed in UNSIMPLIFIED_SUBSET_SEEDS:
            source = random_subset_instance(seed, unsimplified=True)
            certificate = _export(source)
            self.assertTrue(_declarations(certificate, z3.Z3_OP_SET_SUBSET), seed)
            sources.append((seed, source, certificate))
        lean_test_support.prefetch((source, certificate) for _, source, certificate in sources)
        for seed, source, certificate in sources:
            with self.subTest(seed=seed):
                self.assertEqual(certificate["fragment"], "qf_uflia")
                _, report = lean_test_support.check(self, source, certificate)
                self.assertTrue(_STANDARD_AXIOMS in report or "does not depend on any axioms" in report, report)

    def test_subset_facts_are_needed(self):
        """Without its subset facts each of these fails in Lean, with grind failing."""
        def check(text):
            with tempfile.TemporaryDirectory() as directory:
                output = Path(directory) / "facts.lean"
                output.write_text(text)
                result = subprocess.run([str(proof_to_lean._CHECK_LEAN), str(output)], text=True,
                                        capture_output=True)
            return result.returncode, result.stdout + result.stderr

        for name, fact in (("member_outside", r"have _sb\d+ := "), ("reflexive", r"have _pws\d+ : _subset "),
                           ("intersection_below_its_set", r"have _pws\d+ : _subset "),
                           ("full_below_empty", r"have _pwsn\d+ : "),
                           # (full_below_a_removal is proved from the difference's equality too.)
                           ("an_insert_below_its_removal", r"have _pwsn\d+ : "),
                           ("below_empty", r"have _pws\d+ : _map2 "),
                           ("complement_below_its_set", r"have _pws\d+ : _map2 "),
                           ("inserts_under_a_union_below_empty", r"have _pws\d+ : _map2 "),
                           ("full_below_a_singleton", r"have _pwsn\d+ : "),
                           ("between_constant_arrays", r"have _pwsv\d+ : "),
                           ("decided_false_over_a_sort", r"have _pwsn\d+ : "),
                           ("after_false", r"have _sb\d+ := ")):
            with self.subTest(name=name):
                source = SUBSET_INPUTS[name]
                text = proof_to_lean.reconstruct(source, _export(source))
                pattern = re.compile(r"^\s*" + fact)
                self.assertTrue(any(map(pattern.match, text.split("\n"))), text)
                code, report = check(_without_facts(text, pattern.match))
                self.assertNotEqual(code, 0, report)
                errors = [line for line in report.split("\n") if "error:" in line]
                self.assertTrue(errors, report)
                for error in errors:
                    self.assertIn("`grind` failed", error)


if __name__ == "__main__":
    unittest.main()
