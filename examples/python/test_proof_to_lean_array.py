############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Tests for the QF_AX slice of the Lean reconstruction: arrays from one
# uninterpreted sort to another, certified through the sat.smt clause log.
# An array is a function _m.U -> _m.U (array constants are the family
# _m.arrs), select is _select, store the classical update _store, and the
# array solver's extensionality witness (_ array-ext 0) is _array_diff, an
# index where two different arrays differ. The array solver's axiom
# instances (array hints) are proved by grind with the facts _store_apply
# and _array_ext instantiated per lemma. Validation without Lean, and
# end-to-end checks that need the z3 executable and the pinned Lean
# toolchain.
############################################
import copy
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import z3

_EXAMPLES = Path(__file__).resolve().parent
sys.path.insert(0, str(_EXAMPLES))
import proof_certificate
import proof_clause_log
import proof_to_lean
from test_proof_to_lean_lia import _STANDARD_AXIOMS, _hints, _z3_available

_DECLARATIONS = """(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a () (Array Index Element))
(declare-fun b () (Array Index Element))
(declare-fun i () Index)
(declare-fun j () Index)
(declare-fun e () Element)
(declare-fun f () Element)
"""

# Documented QF_AX inputs, each refuted by a different array axiom.
ARRAY_INPUTS = {
    # Read over write at the written index: the store axiom
    # (= (select (store a i e) i) e), which the array solver propagates.
    # (Z3's rewriter would simplify a read of the store term itself.)
    "read_own_write": "(set-logic QF_AX)\n" + _DECLARATIONS + """(assert (= b (store a i e)))
(assert (= (select b i) f))
(assert (not (= e f)))
(check-sat)
""",
    # Read over write at another index: i = j or the read sees a.
    "read_other_index": "(set-logic QF_AX)\n" + _DECLARATIONS + """(assert (not (= i j)))
(assert (= b (store a i e)))
(assert (not (= (select b j) (select a j))))
(check-sat)
""",
    # Writes at two different indices commute: extensionality (the array-ext
    # witness) and select over store at both indices.
    "store_commutes": "(set-logic QF_AX)\n" + _DECLARATIONS + """(assert (not (= i j)))
(assert (not (= (store (store a i e) j f) (store (store a j f) i e))))
(check-sat)
""",
    # Writing back what was read leaves the array unchanged: extensionality.
    "write_back_read": "(set-logic QF_AX)\n" + _DECLARATIONS + """(assert (= e (select a i)))
(assert (not (= (store a i e) a)))
(check-sat)
""",
    # Two arrays equal after the same write differ at most at that index.
    "store_injective_elsewhere": "(set-logic QF_AX)\n" + _DECLARATIONS + """(assert (= (store a i e) (store b i e)))
(assert (not (= i j)))
(assert (not (= (select a j) (select b j))))
(check-sat)
""",
    # An ite over arrays, and an uninterpreted function over the elements.
    "array_ite_and_function": "(set-logic QF_AUF)\n" + _DECLARATIONS + """(declare-fun g (Element) Element)
(declare-fun p () Bool)
(assert (= (select a i) e))
(assert (= (select b i) e))
(assert (not (= (g (select (ite p a b) i)) (g e))))
(check-sat)
""",
    # Two array sorts over the same index sort.
    "two_array_sorts": "(set-logic QF_AX)\n" + _DECLARATIONS + """(declare-sort Key 0)
(declare-fun c () (Array Index Key))
(declare-fun k () Key)
(assert (= (select (store c i k) j) (select c j)))
(assert (= (select (store a i e) j) f))
(assert (= i j))
(assert (not (= (select a i) f)))
(assert (not (= (select (store c j k) i) k)))
(check-sat)
""",
    # A predicate over arrays (injected into the carrier by _m.arrs_inj):
    # Z3 proves it by a th-lemma cnf step, not a rewrite, whose lemma needs
    # the store identity _store_select.
    "predicate_over_arrays": "(set-logic QF_AUF)\n" + _DECLARATIONS + """(declare-fun p ((Array Index Element)) Bool)
(assert (p a))
(assert (not (p (store a i (select a i)))))
(check-sat)
""",
    # Arrays next to integer arithmetic over an element function (qf_uflia).
    "arrays_with_integer_weights": "(set-logic QF_AUFLIA)\n" + _DECLARATIONS + """(declare-fun w (Element) Int)
(assert (= (select (store a i e) j) f))
(assert (= i j))
(assert (> (w f) (+ (w e) 2)))
(check-sat)
""",
    # The smtlib-sample QF_AX family storeinv (Armando, Bonacina, Ranise,
    # Schulz, PDPAR'05), z3test storeinv_t2_np_nf_ai_00001_001: swapping
    # one entry between two arrays twice gives arrays equal to each other
    # only if the originals were.
    "storeinv_t2_00001": """(set-logic QF_AX)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a1 () (Array Index Element))
(declare-fun a2 () (Array Index Element))
(declare-fun i1 () Index)
(assert (= (store a2 i1 (select a1 i1)) (store a1 i1 (select a2 i1))))
(assert (not (= a1 a2)))
(check-sat)
""",
    # z3test swap_t1_np_nf_ai_00006_006 (same family): a sequence of swaps
    # through two paths ends in the same array.
    "swap_t1_00006_006": """(set-logic QF_AX)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a1 () (Array Index Element))
(declare-fun i0 () Index)
(declare-fun i1 () Index)
(declare-fun i3 () Index)
(declare-fun i4 () Index)
(declare-fun i5 () Index)
(assert (let ((?v_0 (select a1 i1))) (let ((?v_1 (store (store a1 i1 ?v_0) i1 ?v_0))) (let ((?v_2 (store (store ?v_1 i3 (select ?v_1 i5)) i5 (select ?v_1 i3)))) (let ((?v_3 (store (store ?v_2 i5 (select ?v_2 i0)) i0 (select ?v_2 i5)))) (let ((?v_6 (select ?v_3 i1)) (?v_7 (select ?v_3 i5))) (let ((?v_4 (store (store ?v_3 i1 ?v_7) i5 ?v_6))) (let ((?v_5 (store (store ?v_4 i5 (select ?v_4 i1)) i1 (select ?v_4 i5))) (?v_8 (store (store ?v_3 i5 ?v_6) i1 ?v_7))) (let ((?v_9 (store (store ?v_8 i5 (select ?v_8 i1)) i1 (select ?v_8 i5)))) (not (= (store (store ?v_5 i4 (select ?v_5 i5)) i5 (select ?v_5 i4)) (store (store ?v_9 i5 (select ?v_9 i4)) i4 (select ?v_9 i5)))))))))))))
(check-sat)
""",
}
# Arrays over Int and Real (QF_ALIA, QF_AUFLIA): Int and Real index and
# element sorts are Int and Rat in Lean, so reads of Int arrays are atoms of
# the linear forms and indices are arithmetic terms.
_INT_ARRAYS = """(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
"""
ARITHMETIC_ARRAY_INPUTS = {
    # Read over write at another index, then a Farkas step over the reads.
    "int_read_other_index": "(set-logic QF_ALIA)\n" + _INT_ARRAYS + """(assert (= b (store a i 5)))
(assert (> (select b j) (+ (select a j) 2)))
(assert (not (= i j)))
(check-sat)
""",
    # Read over write at an index equal by arithmetic, not syntactically.
    "int_index_arithmetic": "(set-logic QF_ALIA)\n" + _INT_ARRAYS + """(assert (= j (+ i 1)))
(assert (< (select (store a (+ i 1) 7) j) 7))
(check-sat)
""",
    # Writes at two different Int indices commute: an extensionality witness
    # over Int, chosen with Lean's own inhabitant of Int.
    "int_store_commutes": "(set-logic QF_ALIA)\n" + _INT_ARRAYS + """(assert (< i j))
(assert (not (= (store (store a i 1) j 2) (store (store a j 2) i 1))))
(check-sat)
""",
    # Real indices and elements (qf_uflra).
    "real_read_own_write": """(set-logic QF_AUFLRA)
(declare-fun r () (Array Real Real))
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= y (* 2.0 x)))
(assert (> (select (store r (+ x x) 1.5) y) 2.0))
(check-sat)
""",
    # Int indices into an uninterpreted element sort, and an uninterpreted
    # index sort into Int elements, next to each other.
    "mixed_index_and_element_sorts": "(set-logic QF_AUFLIA)\n" + _DECLARATIONS + """(declare-fun c () (Array Int Element))
(declare-fun w () (Array Index Int))
(declare-fun k () Int)
(declare-fun m () Int)
(assert (= (select (store c k e) m) f))
(assert (<= m k))
(assert (>= m k))
(assert (= i j))
(assert (or (not (= e f)) (> (select w i) (select w j))))
(check-sat)
""",
    # Int indices into Real elements (qf_uflira).
    "int_indices_real_elements": """(set-logic QF_AUFLIRA)
(declare-fun r () (Array Int Real))
(declare-fun n () Int)
(assert (>= (select r n) 0.5))
(assert (<= (+ (select r n) (select (store r (+ n 1) 0.0) n)) 0.75))
(check-sat)
""",
    # A function over arrays: equal arrays have equal images.
    "function_over_arrays": "(set-logic QF_AUFLIA)\n" + _INT_ARRAYS + """(declare-fun sk ((Array Int Int) (Array Int Int)) Int)
(assert (= b (store a i (select a i))))
(assert (not (= (sk a b) (sk a a))))
(check-sat)
""",
    # A predicate over an uninterpreted and an Int array: each Lean array
    # type has its own injection, and the cnf lemma needs _store_select.
    "predicate_over_two_array_types": "(set-logic QF_AUFLIA)\n" + _DECLARATIONS + """(declare-fun c () (Array Int Int))
(declare-fun p ((Array Index Element) (Array Int Int)) Bool)
(declare-fun n () Int)
(assert (p a c))
(assert (not (p (store a i (select a i)) (store c n (select c n)))))
(check-sat)
""",
    # A predicate over an overwritten Int array: the cnf lemma needs
    # _store_store.
    "predicate_over_overwritten_array": "(set-logic QF_AUFLIA)\n" + _INT_ARRAYS + """(declare-fun p ((Array Int Int)) Bool)
(assert (p (store a i 3)))
(assert (not (p (store (store a i 2) i 3))))
(check-sat)
""",
    # z3test regressions/smt2/z3.20.smt2: a store that leaves its array
    # unchanged writes the value already there.
    "z3_20": """(set-option :auto-config true)
(set-option :produce-models true)

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const a1 (Array Int Int))
(declare-const a2 (Array Int Int))
(declare-const a3 (Array Int Int))
(assert (= (select a1 x) x))
(assert (= (store a1 x y) a1))
(assert (not (= x y)))
(check-sat)
""",
    # The smtlib-sample QF_AUFLIA family swap (Armando, Bonacina, Ranise,
    # Schulz, PDPAR'05), z3test swap_t1_pp_sf_ai_00003_002: sk is the
    # benchmark's extensionality Skolem function, an Int function over two
    # arrays.
    "swap_t1_pp_00003_002": """(set-logic QF_AUFLIA)
(declare-fun a_207 () (Array Int Int))
(declare-fun a_208 () (Array Int Int))
(declare-fun a_210 () (Array Int Int))
(declare-fun a_212 () (Array Int Int))
(declare-fun a_214 () (Array Int Int))
(declare-fun a_215 () (Array Int Int))
(declare-fun a_216 () (Array Int Int))
(declare-fun a_217 () (Array Int Int))
(declare-fun a_219 () (Array Int Int))
(declare-fun a_220 () (Array Int Int))
(declare-fun e_206 () Int)
(declare-fun e_209 () Int)
(declare-fun e_211 () Int)
(declare-fun e_213 () Int)
(declare-fun e_218 () Int)
(declare-fun e_222 () Int)
(declare-fun e_223 () Int)
(declare-fun i_221 () Int)
(declare-fun a1 () (Array Int Int))
(declare-fun i0 () Int)
(declare-fun i2 () Int)
(declare-fun sk ((Array Int Int) (Array Int Int)) Int)
(assert (= a_207 (store a1 i0 e_206)))
(assert (= a_208 (store a_207 i0 e_206)))
(assert (= a_210 (store a_208 i0 e_209)))
(assert (= a_212 (store a_210 i2 e_211)))
(assert (= a_214 (store a_212 i2 e_213)))
(assert (= a_215 (store a_214 i2 e_213)))
(assert (= a_216 (store a_208 i2 e_211)))
(assert (= a_217 (store a_216 i0 e_209)))
(assert (= a_219 (store a_217 i2 e_218)))
(assert (= a_220 (store a_219 i2 e_218)))
(assert (= e_206 (select a1 i0)))
(assert (= e_209 (select a_208 i2)))
(assert (= e_211 (select a_208 i0)))
(assert (= e_213 (select a_212 i2)))
(assert (= e_218 (select a_217 i2)))
(assert (= e_222 (select a_215 i_221)))
(assert (= e_223 (select a_220 i_221)))
(assert (= i_221 (sk a_215 a_220)))
(assert (not (= e_222 e_223)))
(check-sat)
""",
}
ARRAY_INPUTS.update(ARITHMETIC_ARRAY_INPUTS)
# The fragment of each documented input (the others are qf_uf).
_FRAGMENTS = {"arrays_with_integer_weights": "qf_uflia", "real_read_own_write": "qf_uflra",
              "int_indices_real_elements": "qf_uflira"}
_FRAGMENTS.update((name, "qf_uflia") for name in ARITHMETIC_ARRAY_INPUTS if name not in _FRAGMENTS)


def _export(source):
    return proof_certificate.export_clause_log_certificate(source)


def _declarations(certificate, kind):
    return [d for d in certificate["declarations"] if d["kind"] == kind]


class TestArrayValidation(unittest.TestCase):
    """Validation without Lean: classification, rejections, the replay, and the encoding."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")
        cls.certificates = {name: _export(source) for name, source in ARRAY_INPUTS.items()}

    def test_fragments(self):
        for name, certificate in self.certificates.items():
            with self.subTest(name=name):
                self.assertEqual(certificate["fragment"], _FRAGMENTS.get(name, "qf_uf"))

    def test_unsupported_arrays_are_rejected(self):
        context = z3.Context()
        rejected = {
            "(declare-sort I 0)(declare-fun a () (Array I Bool))(declare-fun i () I)(assert (select a i))":
                "unsupported propositional operator: select",
            "(declare-fun a () (Array Bool Int))(declare-fun b () (Array Bool Int))(assert (not (= a b)))":
                "only arrays over uninterpreted sorts, Int, and Real",
            "(declare-sort I 0)(declare-fun a () (Array I I I))(declare-fun i () I)"
            "(assert (not (= (select a i i) (select a i i))))": "only arrays over uninterpreted sorts",
            "(declare-sort I 0)(declare-fun a () (Array I (Array I I)))(declare-fun i () I)"
            "(assert (not (= (select (select a i) i) i)))": "unsupported array operator: select",
            "(declare-sort I 0)(declare-fun a () (Array I (Array I I)))(declare-fun b () (Array I (Array I I)))"
            "(assert (not (= a b)))": "only arrays over uninterpreted sorts",
            "(declare-sort I 0)(declare-fun e () I)(declare-fun i () I)"
            "(assert (not (= (select ((as const (Array I I)) e) i) e)))": "unsupported array operator",
            "(declare-fun a () (Array Int Int))(assert (= (select ((as const (Array Int Int)) 0) 1) 1))":
                "unsupported array operator",
            # A function into an array sort (functions over arrays are supported).
            "(declare-sort I 0)(declare-fun h (I) (Array I I))(declare-fun i () I)"
            "(assert (not (= (h i) (h i))))": "uninterpreted functions over",
            "(declare-fun h ((Array Int Bool)) Int)(declare-fun a () (Array Int Bool))"
            "(assert (> (h a) (h a)))": "uninterpreted functions over",
            # A quoted sort name that imitates the certificate's array sort names.
            "(declare-sort I 0)(declare-sort |(Array I I)| 0)(declare-fun x () |(Array I I)|)"
            "(assert (not (= x x)))": "unsupported uninterpreted sort name",
        }
        for source, message in rejected.items():
            with self.subTest(source=source):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, message):
                    proof_certificate.parse_assertions(source + "(check-sat)", context, integer=True)

    def test_the_legacy_core_rejects_arrays_explicitly(self):
        for name in ("read_own_write", "int_read_other_index", "function_over_arrays"):
            with self.subTest(name=name):
                with self.assertRaisesRegex(proof_certificate.ProofExportError,
                                            "arrays are certified through the clause log"):
                    proof_certificate.export_certificate(ARRAY_INPUTS[name])

    def test_arithmetic_array_encoding(self):
        """Int and Real index and element sorts are Int and Rat; each Lean array type has its own family."""
        text = proof_to_lean.reconstruct(ARRAY_INPUTS["int_store_commutes"], self.certificates["int_store_commutes"])
        self.assertIn("  arrs_ii : Nat -> Int -> Int", text)
        self.assertIn('-- Array sorts "(Array Int Int)" are functions Int -> Int (_m.arrs_ii)', text)
        self.assertIn("-- No uninterpreted sort: the type _m.U carries only the arguments of the functions", text)
        # The witness over Int indices chooses with Int's own inhabitant: no
        # nonempty field.
        self.assertIn(":= (_array_diff (Nonempty.intro (0 : Int)) (term_", text)
        self.assertIn(":= _array_ext (Nonempty.intro (0 : Int)) ((term_", text)
        self.assertNotIn("nonempty", text)
        self.assertNotIn("arrs :", text)
        mixed = proof_to_lean.reconstruct(ARRAY_INPUTS["mixed_index_and_element_sorts"],
                                          self.certificates["mixed_index_and_element_sorts"])
        for field in ("  arrs_iu : Nat -> Int -> U", "  arrs_ui : Nat -> U -> Int"):
            self.assertIn(field, mixed)
        real = proof_to_lean.reconstruct(ARRAY_INPUTS["real_read_own_write"], self.certificates["real_read_own_write"])
        self.assertIn("  arrs_rr : Nat -> Rat -> Rat", real)
        lira = proof_to_lean.reconstruct(ARRAY_INPUTS["int_indices_real_elements"],
                                         self.certificates["int_indices_real_elements"])
        self.assertIn("  arrs_ir : Nat -> Int -> Rat", lira)
        # An array argument of a function is injected into the carrier.
        function = proof_to_lean.reconstruct(ARRAY_INPUTS["function_over_arrays"],
                                             self.certificates["function_over_arrays"])
        self.assertIn("  arrs_ii_inj : (Int -> Int) -> U", function)
        self.assertIn("_m.ifuns 0 [(_m.arrs_ii_inj (term_", function)
        # A predicate over arrays of two Lean types: one injection each, and
        # its th-lemma cnf step (not a rewrite) is offered the store
        # identities.
        predicate = proof_to_lean.reconstruct(ARRAY_INPUTS["predicate_over_two_array_types"],
                                              self.certificates["predicate_over_two_array_types"])
        for field in ("  arrs_inj : (U -> U) -> U", "  arrs_ii_inj : (Int -> Int) -> U"):
            self.assertIn(field, predicate)
        self.assertIn("_m.preds 0 [(_m.arrs_inj (term_", predicate)
        self.assertIn("private theorem th_lemma_", predicate)
        self.assertNotIn("private theorem rewrite_", predicate)
        self.assertIn("simp only [", predicate)
        for each in (text, mixed, real, lira, function, predicate):
            self.assertNotIn("sorry", each)
            self.assertNotIn("axiom ", each)

    def test_reads_of_int_arrays_are_linear_atoms(self):
        """A Farkas lemma over reads of an Int array is checked over the reads as atoms."""
        certificate = self.certificates["int_read_other_index"]
        graph = proof_to_lean._validate_graph(ARRAY_INPUTS["int_read_other_index"], certificate)
        farkas = [node for node in range(len(graph.nodes)) if graph.kind(node) == z3.Z3_OP_PR_TH_LEMMA
                  and graph.decl(node).parameters[0] == "farkas"]
        self.assertTrue(farkas)
        reads = {node for node in range(len(graph.nodes)) if graph.kind(node) == z3.Z3_OP_SELECT}
        for node in farkas:
            terms = {}
            for literal in graph.clause(graph.conclusion(node)):
                atom = graph.arguments(literal)[0] if graph.kind(literal) == z3.Z3_OP_NOT else literal
                proof_to_lean._linear_term(graph, graph.arguments(atom)[0], 1, terms)
            self.assertTrue(set(terms) & reads)

    def test_tampered_arithmetic_arrays_are_rejected(self):
        def declaration(certificate, kind):
            return next(d for d in certificate["declarations"] if d["kind"] == kind)

        def select_into_real(certificate):
            declaration(certificate, z3.Z3_OP_SELECT)["range"] = "Real"

        def bool_elements(certificate):
            for d in certificate["declarations"]:
                d["domain"] = ["(Array Int Bool)" if s == "(Array Int Int)" else s for s in d["domain"]]
                if d["range"] == "(Array Int Int)":
                    d["range"] = "(Array Int Bool)"

        def farkas_as_array_lemma(certificate):
            # A Farkas lemma over reads of Int arrays: its inequalities are
            # not the (dis)equalities of an array axiom instance.
            for d in certificate["declarations"]:
                if d["name"] == "th-lemma" and d["parameters"][:1] == ["farkas"]:
                    d["parameters"] = ["array"]

        self._rejects("int_read_other_index", select_into_real, "invalid select declaration|wrong argument sort")
        self._rejects("int_read_other_index", bool_elements, "unsupported array sort")
        self._rejects("int_read_other_index", farkas_as_array_lemma, "array th-lemma literals must be equalities")

    def test_array_lemmas_are_equality_clauses(self):
        lemmas = {}
        for name, certificate in self.certificates.items():
            declarations, nodes = certificate["declarations"], certificate["nodes"]
            for node in nodes:
                declaration = declarations[node["declaration"]]
                if declaration["name"] == "th-lemma" and declaration["parameters"] == ["array"]:
                    lemmas.setdefault(name, []).append(node["arguments"][-1])
        self.assertLessEqual({"read_own_write", "read_other_index", "store_commutes", "write_back_read"},
                             set(lemmas))
        # The store axiom is a unit clause, the propagated equality itself
        # (its hint lists that equality, not its complement).
        certificate = self.certificates["read_own_write"]
        declarations, nodes = certificate["declarations"], certificate["nodes"]
        kinds = [declarations[nodes[clause]["declaration"]]["kind"] for clause in lemmas["read_own_write"]]
        self.assertIn(z3.Z3_OP_EQ, kinds)

    def test_extensionality_witnesses_reach_the_certificate(self):
        for name in ("store_commutes", "write_back_read", "storeinv_t2_00001"):
            with self.subTest(name=name):
                witnesses = _declarations(self.certificates[name], z3.Z3_OP_ARRAY_EXT)
                self.assertEqual(len(witnesses), 1)
                self.assertEqual(witnesses[0]["name"], "array-ext")
                self.assertEqual(witnesses[0]["parameters"], [])

    def test_encoding(self):
        text = proof_to_lean.reconstruct(ARRAY_INPUTS["store_commutes"], self.certificates["store_commutes"])
        self.assertIn("  arrs : Nat -> U -> U", text)
        self.assertIn("  nonempty : Nonempty U", text)
        self.assertIn("-- Array 0: \"a\"", text)
        self.assertIn(":= (_store (term_", text)
        self.assertIn(":= (_array_diff _m.nonempty (term_", text)
        self.assertIn(":= _array_ext _m.nonempty ((term_", text)
        self.assertIn(":= _store_apply ((term_", text)
        # Array terms stay folded in the lemmas, each store related to its
        # body by one definitional step.
        self.assertRegex(text, r"have _t[0-9]+ : \(term_[0-9]+ _atoms _m\) = \(_store \(\(term_")
        self.assertNotIn("sorry", text)
        self.assertNotIn("axiom ", text)
        # Without an extensionality witness there is no nonempty field.
        text = proof_to_lean.reconstruct(ARRAY_INPUTS["read_own_write"], self.certificates["read_own_write"])
        self.assertNotIn("nonempty", text)
        two = proof_to_lean.reconstruct(ARRAY_INPUTS["two_array_sorts"], self.certificates["two_array_sorts"])
        self.assertIn('-- Array sorts "(Array Index Element)", "(Array Index Key)" are functions', two)

    def test_sort_header_comments(self):
        """The header names the carriers once and claims no missing sort, with or without arrays."""
        text = proof_to_lean.reconstruct(ARRAY_INPUTS["read_own_write"], self.certificates["read_own_write"])
        self.assertIn('-- Uninterpreted sorts "Element", "Index" are the one type _m.U;', text)
        self.assertIn('-- Array sorts "(Array Index Element)" are functions', text)
        self.assertNotIn("No uninterpreted sort", text)
        source = """(declare-sort S 0)
(declare-fun a () S)
(declare-fun b () S)
(declare-fun f (S) S)
(assert (= a b))
(assert (not (= (f a) (f b))))
(check-sat)
"""
        for export in (_export, proof_certificate.export_certificate):
            with self.subTest(export=export.__name__):
                text = proof_to_lean.reconstruct(source, export(source))
                self.assertIn('-- Uninterpreted sort "S" is the type _m.U;', text)
                self.assertNotIn("No uninterpreted sort", text)
                self.assertNotIn("Array sorts", text)

    def _rejects(self, name, mutate, message):
        certificate = copy.deepcopy(self.certificates[name])
        mutate(certificate)
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, message):
            proof_to_lean.reconstruct(ARRAY_INPUTS[name], certificate)

    def test_tampered_array_declarations_are_rejected(self):
        def declaration(certificate, kind):
            return next(d for d in certificate["declarations"] if d["kind"] == kind)

        def swap_store_domain(certificate):
            store = declaration(certificate, z3.Z3_OP_STORE)
            store["domain"] = [store["domain"][0], store["domain"][2], store["domain"][1]]

        def select_into_index(certificate):
            declaration(certificate, z3.Z3_OP_SELECT)["range"] = "Index"

        def rename_array_sort(certificate):
            for d in certificate["declarations"]:
                d["domain"] = ["(Array Element Index)" if s == "(Array Index Element)" else s for s in d["domain"]]
                if d["range"] == "(Array Index Element)":
                    d["range"] = "(Array Element Index)"

        def parenthesized_sort(certificate):
            for d in certificate["declarations"]:
                if d["range"] == "(Array Index Element)":
                    d["range"] = "(Array Index Element"

        self._rejects("read_other_index", swap_store_domain, "invalid store declaration")
        self._rejects("read_other_index", select_into_index, "invalid select declaration|wrong argument sort")
        self._rejects("read_other_index", rename_array_sort, "invalid store declaration")
        self._rejects("read_other_index", parenthesized_sort, "unsupported sort")

    def test_array_lemmas_over_other_atoms_are_rejected(self):
        certificate = self.certificates["arrays_with_integer_weights"]
        graph = proof_to_lean._validate_graph(ARRAY_INPUTS["arrays_with_integer_weights"], certificate)
        farkas = [node for node in range(len(graph.nodes)) if graph.kind(node) == z3.Z3_OP_PR_TH_LEMMA
                  and graph.decl(node).parameters[0] == "farkas"]
        self.assertTrue(farkas)
        relabeled = copy.deepcopy(certificate)
        declaration = relabeled["nodes"][farkas[0]]["declaration"]
        relabeled["declarations"][declaration]["parameters"] = ["array"]
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "array th-lemma literals must be equalities"):
            proof_to_lean.reconstruct(ARRAY_INPUTS["arrays_with_integer_weights"], relabeled)

    def test_the_replay_reads_array_terms(self):
        context = z3.Context()
        assertions, _ = proof_certificate.parse_assertions(ARRAY_INPUTS["store_injective_elsewhere"], context)
        terms = proof_clause_log._Terms(context, assertions)
        self.assertEqual(terms.sorts, {"Index", "Element"})
        terms.define("$1", ["Array", "Index", "Element"], ["store", "a", "i", "e"])
        terms.define("$2", "Index", [["_", "array-ext", "0"], "$1", "b"])
        witness = terms.build("$2")
        self.assertTrue(z3.is_app_of(witness, z3.Z3_OP_ARRAY_EXT))
        read = terms.build(["select", "$1", "$2"])
        self.assertEqual(str(read.sort()), "Element")
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "has sort"):
            terms.define("$3", ["Array", "Element", "Index"], ["store", "a", "i", "e"])
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "array-ext over"):
            terms.build([["_", "array-ext", "0"], "i", "j"])


def _check_in_lean(test, source, fragment):
    """Export through the clause log, reconstruct, and kernel-check; return the certificate."""
    certificate = _export(source)
    test.assertEqual(certificate["fragment"], fragment)
    with tempfile.TemporaryDirectory() as directory:
        output = Path(directory) / "checked.lean"
        proof_to_lean.check_and_write(source, certificate, output)
        text = output.read_text()
        namespace = "Z3Proofs.NativeCertificate.p" + hashlib.sha256(source.encode()).hexdigest()
        output.write_text(text + "\n#print axioms %s.unsat\n" % namespace)
        result = subprocess.run([str(proof_to_lean._CHECK_LEAN), str(output)], text=True, capture_output=True)
        test.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        report = " ".join(result.stdout.split())
        test.assertTrue(_STANDARD_AXIOMS in report or "does not depend on any axioms" in report, report)
    return certificate


class TestArrayLeanIntegration(unittest.TestCase):
    """End-to-end: clause log, certificate, Lean reconstruction, kernel check."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")

    def test_documented_inputs_verify(self):
        hints = set()
        for name, source in ARRAY_INPUTS.items():
            with self.subTest(name=name):
                hints |= _hints(_check_in_lean(self, source, _FRAGMENTS.get(name, "qf_uf")))
        self.assertLessEqual({"array", "euf"}, hints)

    def test_array_facts_are_needed(self):
        """Without the _store_apply and _array_ext facts grind cannot prove the array lemmas."""
        for name in ("store_commutes", "int_store_commutes"):
            with self.subTest(name=name):
                source = ARRAY_INPUTS[name]
                text = proof_to_lean.reconstruct(source, _export(source))
                stripped = "\n".join(line for line in text.split("\n")
                                     if ":= _store_apply " not in line and ":= _array_ext " not in line)
                self.assertNotEqual(stripped, text)
                with tempfile.TemporaryDirectory() as directory:
                    output = Path(directory) / "stripped.lean"
                    output.write_text(stripped)
                    result = subprocess.run([str(proof_to_lean._CHECK_LEAN), str(output)], text=True,
                                            capture_output=True)
                report = result.stdout + result.stderr
                self.assertNotEqual(result.returncode, 0, report)
                # Every error is grind (after omega, over Int) failing on an
                # array lemma, not a dangling reference to a removed fact.
                errors = [line for line in report.split("\n") if "error:" in line]
                self.assertTrue(errors, report)
                for error in errors:
                    self.assertIn("`grind` failed", error)


if __name__ == "__main__":
    unittest.main()
