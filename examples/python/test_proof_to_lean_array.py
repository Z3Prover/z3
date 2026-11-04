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
# The fragment of each documented input (the others are qf_uf).
_FRAGMENTS = {"arrays_with_integer_weights": "qf_uflia"}


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
            "(declare-fun a () (Array Int Int))(assert (= (select a 0) 1))(assert (= (select a 0) 2))":
                "unsupported arithmetic operator: select",
            "(declare-fun a () (Array Int Int))(declare-fun b () (Array Int Int))(assert (not (= a b)))":
                "only arrays from one uninterpreted sort to another",
            "(declare-sort I 0)(declare-fun a () (Array I Bool))(declare-fun i () I)(assert (select a i))":
                "unsupported propositional operator: select",
            "(declare-sort I 0)(declare-fun a () (Array I I I))(declare-fun i () I)"
            "(assert (not (= (select a i i) (select a i i))))": "only arrays from one uninterpreted sort",
            "(declare-sort I 0)(declare-fun a () (Array I (Array I I)))(declare-fun i () I)"
            "(assert (not (= (select (select a i) i) i)))": "unsupported array operator: select",
            "(declare-sort I 0)(declare-fun a () (Array I (Array I I)))(declare-fun b () (Array I (Array I I)))"
            "(assert (not (= a b)))": "only arrays from one uninterpreted sort",
            "(declare-sort I 0)(declare-fun e () I)(declare-fun i () I)"
            "(assert (not (= (select ((as const (Array I I)) e) i) e)))": "unsupported array operator",
            "(declare-sort I 0)(declare-fun a () (Array I I))(declare-fun h ((Array I I)) I)(declare-fun i () I)"
            "(assert (not (= (h a) (h (store a i (select a i))))))": "uninterpreted functions over",
            # A quoted sort name that imitates the certificate's array sort names.
            "(declare-sort I 0)(declare-sort |(Array I I)| 0)(declare-fun x () |(Array I I)|)"
            "(assert (not (= x x)))": "unsupported uninterpreted sort name",
        }
        for source, message in rejected.items():
            with self.subTest(source=source):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, message):
                    proof_certificate.parse_assertions(source + "(check-sat)", context, integer=True)

    def test_the_legacy_core_rejects_arrays_explicitly(self):
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "arrays are certified through the clause log"):
            proof_certificate.export_certificate(ARRAY_INPUTS["read_own_write"])

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
        source = ARRAY_INPUTS["store_commutes"]
        text = proof_to_lean.reconstruct(source, _export(source))
        stripped = "\n".join(line for line in text.split("\n")
                             if ":= _store_apply " not in line and ":= _array_ext " not in line)
        self.assertNotEqual(stripped, text)
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "stripped.lean"
            output.write_text(stripped)
            result = subprocess.run([str(proof_to_lean._CHECK_LEAN), str(output)], text=True, capture_output=True)
        report = result.stdout + result.stderr
        self.assertNotEqual(result.returncode, 0, report)
        # Every error is grind failing on an array lemma, not a dangling
        # reference to a removed fact.
        errors = [line for line in report.split("\n") if "error:" in line]
        self.assertTrue(errors, report)
        for error in errors:
            self.assertIn("`grind` failed", error)


if __name__ == "__main__":
    unittest.main()
