############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Native certificate validation and Lean source reconstruction tests.
############################################
import copy
from collections import Counter
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import z3

_EXAMPLES = Path(__file__).resolve().parent
sys.path.insert(0, str(_EXAMPLES))
import proof_certificate
import proof_to_lean


LITERAL = "(declare-const p Bool)(assert p)(assert (not p))"
CLAUSE = """\
(declare-const p Bool)(declare-const q Bool)(declare-const r Bool)
(assert (or p q r))(assert (not p))(assert (not q))(assert (not r))
"""
REWRITE = """\
(declare-const p Bool)(declare-const q Bool)
(assert (or p q))(assert (=> p q))(assert (not q))
"""
CONJUNCTION = """\
(declare-const p Bool)(declare-const q Bool)
(assert (and p q))(assert (not p))
"""
STRUCTURAL = """\
(declare-const p Bool)(declare-const q Bool)
(assert (not (or (not p) q)))(assert (not (and p (not q))))
"""
UNSUPPORTED = """\
(declare-const p Bool)(declare-const q Bool)
(assert (or p q))(assert (or (not p) q))
(assert (or p (not q)))(assert (or (not p) (not q)))
"""


def make_certificate(source, steps):
    """Build synthetic native-format steps over genuinely parsed Boolean ASTs.

    Original assertions are steps 0..n-1. Further steps are triples of
    (rule, earlier proof-step indices, SMT-LIB conclusion).
    """
    context = z3.Context(proof=True)
    original = proof_certificate.parse_propositional_assertions(source, context)
    extended = proof_certificate._assertion_commands(source)
    extended += "".join("(assert %s)" % conclusion for _, _, conclusion in steps)
    formulas = proof_certificate.parse_propositional_assertions(extended, context)
    solver = z3.Solver(ctx=context)
    solver.add(z3.BoolVal(False, ctx=context))
    assert solver.check() == z3.unsat
    certificate = proof_certificate._encode_proof(formulas, solver.proof())
    assert certificate["proof"] == len(certificate["nodes"]) - 1
    certificate["nodes"].pop()
    certificate["declarations"].pop()
    formula_roots = certificate["assertions"]
    certificate["assertions"] = formula_roots[:len(original)]
    proof_nodes, declarations = [], {}

    def add_step(rule, premises, conclusion):
        kind = {"asserted": z3.Z3_OP_PR_ASSERTED,
                "mp": z3.Z3_OP_PR_MODUS_PONENS,
                "rewrite": z3.Z3_OP_PR_REWRITE,
                "refl": z3.Z3_OP_PR_REFLEXIVITY,
                "symm": z3.Z3_OP_PR_SYMMETRY,
                "trans": z3.Z3_OP_PR_TRANSITIVITY,
                "monotonicity": z3.Z3_OP_PR_MONOTONICITY,
                "and-elim": z3.Z3_OP_PR_AND_ELIM,
                "not-or-elim": z3.Z3_OP_PR_NOT_OR_ELIM,
                "unit-resolution": z3.Z3_OP_PR_UNIT_RESOLUTION}[rule]
        domain = ("Proof",) * len(premises) + ("Bool",)
        key = (kind, domain)
        if key not in declarations:
            declarations[key] = len(certificate["declarations"])
            certificate["declarations"].append({
                "kind": kind, "name": rule, "domain": list(domain),
                "range": "Proof", "parameters": [],
            })
        certificate["nodes"].append({
            "declaration": declarations[key],
            "arguments": [proof_nodes[premise] for premise in premises] + [conclusion],
        })
        proof_nodes.append(len(certificate["nodes"]) - 1)

    for formula in certificate["assertions"]:
        add_step("asserted", [], formula)
    for (rule, premises, _), formula in zip(steps, formula_roots[len(original):]):
        add_step(rule, premises, formula)
    certificate["proof"] = proof_nodes[-1]
    certificate["rule_counts"] = dict(Counter(
        certificate["declarations"][certificate["nodes"][node]["declaration"]]["name"]
        for node in proof_nodes))
    certificate.update({
        "format": "z3-native-proof-dag", "format_version": 1,
        "z3_version": z3.get_full_version(), "fragment": "propositional",
        "result": "unsat", "verification": "unverified", "source_smt2": source,
    })
    return certificate


class TestProofToLean(unittest.TestCase):
    def setUp(self):
        self.certificate = proof_certificate.export_certificate(LITERAL)

    def test_real_native_refutations_generate_explicit_proof_terms(self):
        for source in [LITERAL, CLAUSE, REWRITE, CONJUNCTION, STRUCTURAL,
                       "(assert false)", "(assert (not true))"]:
            with self.subTest(source=source):
                certificate = proof_certificate.export_certificate(source)
                text = proof_to_lean.reconstruct(source, certificate)
                self.assertIn("theorem unsat", text)
                self.assertIn(": False :=", text)
                self.assertNotIn("sorry", text)
                self.assertNotIn("axiom ", text)
                self.assertNotIn("native_decide", text)
                self.assertNotIn("classical", text)
                self.assertEqual(text.count("  let _step_"), sum(certificate["rule_counts"].values()))

    def test_reconstruction_does_not_run_solver_search(self):
        for source in [LITERAL, REWRITE, CONJUNCTION, STRUCTURAL]:
            certificate = proof_certificate.export_certificate(source)
            with patch.object(z3.Solver, "check", side_effect=AssertionError("solver oracle invoked")):
                proof_to_lean.reconstruct(source, certificate)

    def test_mp_supports_implications_and_boolean_equalities(self):
        for relation in ["(=> p q)", "(= p q)"]:
            with self.subTest(relation=relation):
                source = "(declare-const p Bool)(declare-const q Bool)"
                source += "(assert p)(assert %s)(assert (not q))" % relation
                certificate = make_certificate(source, [
                    ("mp", [0, 1], "q"),
                    ("unit-resolution", [3, 2], "false"),
                ])
                text = proof_to_lean.reconstruct(source, certificate)
                self.assertEqual("Iff.mp" in text, relation.startswith("(= "))

    def test_incorrect_mp_steps_are_rejected_even_when_unused(self):
        source = "(declare-const p Bool)(declare-const q Bool)"
        source += """\
(assert p)(assert q)(assert (=> p q))(assert (= p q))
(assert (or p q))(assert false)
"""
        for premises, conclusion in [
            ([0, 2], "p"), ([1, 2], "q"), ([1, 3], "p"),
            ([0, 4], "q"), ([2, 0], "q"), ([0, 2], "false"),
        ]:
            with self.subTest(premises=premises, conclusion=conclusion):
                certificate = make_certificate(source, [
                    ("mp", premises, conclusion), ("asserted", [], "false"),
                ])
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "mp"):
                    proof_to_lean.reconstruct(source, certificate)

    def test_mp_and_rewrite_signatures_are_checked(self):
        original = proof_certificate.export_certificate(REWRITE)
        for rule, domains in [("mp", [[], ["Bool", "Proof", "Bool"], ["Proof", "Bool"]]),
                              ("rewrite", [[], ["Proof", "Bool"], ["Proof"]])]:
            for key, value in [("name", "forged")] + [("domain", domain) for domain in domains]:
                with self.subTest(rule=rule, key=key, value=value):
                    certificate = copy.deepcopy(original)
                    declaration = next(decl for decl in certificate["declarations"] if decl["name"] == rule)
                    declaration[key] = value
                    with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "invalid " + rule):
                        proof_to_lean.reconstruct(REWRITE, certificate)
        for rule, premises in [("mp", [0]), ("mp", [0, 1, 2]), ("rewrite", [0])]:
            certificate = make_certificate(LITERAL + "(assert false)", [
                (rule, premises, "false"),
            ])
            with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "invalid " + rule):
                proof_to_lean.reconstruct(LITERAL + "(assert false)", certificate)

    def test_rewrite_requires_a_boolean_equivalence(self):
        source = LITERAL + "(assert false)"
        for conclusion in ["p", "(=> p p)", "false"]:
            with self.subTest(conclusion=conclusion):
                certificate = make_certificate(source, [
                    ("rewrite", [], conclusion), ("asserted", [], "false"),
                ])
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "rewrite requires"):
                    proof_to_lean.reconstruct(source, certificate)

    def test_rewrite_lemmas_share_only_the_needed_atom_cases(self):
        source = "".join("(declare-const %s Bool)" % atom for atom in "pqrs")
        source += "(assert (or p q r s))(assert false)"
        certificate = make_certificate(source, [
            ("rewrite", [], "(= (not (not p)) p)"),
            ("rewrite", [], "(= (=> p q) (or q (not p)))"),
            ("asserted", [], "false"),
        ])
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertEqual(text.count("private theorem rewrite_"), 2)
        self.assertEqual(text.count("  refute_with_decidable"), 2)
        self.assertEqual(text.count("cases _d0"), 2)
        self.assertEqual(text.count("cases _d1"), 1)
        self.assertNotIn("cases _d2", text)
        self.assertNotIn("cases _d3", text)
        statement = text.split("theorem unsat", 1)[1].split(": False :=", 1)[0]
        self.assertNotIn("Decidable", statement)

    def test_structural_rule_signatures_are_checked(self):
        source = "(declare-const p Bool)(declare-const q Bool)"
        source += "(assert (= p p))(assert (and p q))(assert (not (or p q)))(assert false)"
        rules = [
            ("refl", [], "(= p p)"), ("symm", [0], "(= p p)"),
            ("trans", [0, 0], "(= p p)"),
            ("monotonicity", [0], "(= (not p) (not p))"),
            ("and-elim", [1], "p"), ("not-or-elim", [2], "(not p)"),
        ]
        for rule, premises, conclusion in rules:
            original = make_certificate(source, [
                (rule, premises, conclusion), ("asserted", [], "false"),
            ])
            for key, value in [("name", "forged"), ("domain", []),
                               ("domain", ["Proof"]), ("domain", ["Bool", "Bool"])]:
                with self.subTest(rule=rule, key=key, value=value):
                    certificate = copy.deepcopy(original)
                    declaration = next(decl for decl in certificate["declarations"] if decl["name"] == rule)
                    declaration[key] = value
                    with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "invalid " + rule):
                        proof_to_lean.reconstruct(source, certificate)
        for rule, premises in [
            ("refl", [0]), ("symm", []), ("symm", [0, 0]),
            ("trans", [0]), ("trans", [0, 0, 0]),
            ("and-elim", []), ("and-elim", [1, 1]),
            ("not-or-elim", []), ("not-or-elim", [2, 2]),
        ]:
            with self.subTest(rule=rule, premises=premises):
                certificate = make_certificate(source, [
                    (rule, premises, "false"),
                ])
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "invalid " + rule):
                    proof_to_lean.reconstruct(source, certificate)

    def test_incorrect_equivalence_steps_are_rejected_even_when_unused(self):
        source = "".join("(declare-const %s Bool)" % atom for atom in "pqr")
        source += """\
(assert (= p q))(assert (= q r))(assert (= r q))
(assert (=> p q))(assert (=> q r))(assert false)
"""
        for rule, premises, conclusion in [
            ("refl", [], "(= p q)"), ("refl", [], "(=> p p)"),
            ("symm", [0], "(= p q)"), ("symm", [0], "(= q r)"),
            ("symm", [3], "(=> q p)"), ("symm", [3], "(= q p)"),
            ("trans", [0, 1], "(= p q)"), ("trans", [0, 2], "(= p r)"),
            ("trans", [1, 0], "(= p r)"), ("trans", [3, 4], "(= p r)"),
            ("trans", [0, 1], "(=> p r)"),
        ]:
            with self.subTest(rule=rule, premises=premises, conclusion=conclusion):
                certificate = make_certificate(source, [
                    (rule, premises, conclusion), ("asserted", [], "false"),
                ])
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, rule):
                    proof_to_lean.reconstruct(source, certificate)

    def test_monotonicity_requires_matching_heads_and_oriented_evidence(self):
        source = "".join("(declare-const %s Bool)" % atom for atom in "pqrs")
        source += "(assert (= p q))(assert (= r s))(assert (=> p q))(assert (= q p))(assert false)"
        for premises, conclusion in [
            ([0], "(= (and p r) (or q r))"),
            ([0], "(= (or p r) (or q r s))"),
            ([], "(= (not p) (not q))"),
            ([3], "(= (not p) (not q))"),
            ([2], "(= (not p) (not q))"),
            ([0], "(= (and p r) (and q s))"),
            ([0, 1], "(= (and p r) (and s q))"),
            ([0], "(=> (not p) (not q))"),
            ([0], "(= p q)"),
        ]:
            with self.subTest(premises=premises, conclusion=conclusion):
                certificate = make_certificate(source, [
                    ("monotonicity", premises, conclusion), ("asserted", [], "false"),
                ])
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "monotonicity"):
                    proof_to_lean.reconstruct(source, certificate)

    def test_monotonicity_reuses_argument_evidence_without_atom_cases(self):
        source = "".join("(declare-const %s Bool)" % atom for atom in "pqrs")
        source += "(assert (= p q))(assert (= r s))"
        source += "(assert (and p r p q))(assert (not (and q s q q)))"
        certificate = make_certificate(source, [
            ("monotonicity", [1, 0, 0], "(= (and p r p q) (and q s q q))"),
            ("mp", [2, 4], "(and q s q q)"),
            ("unit-resolution", [5, 3], "false"),
        ])
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertEqual(text.count("and_congr"), 3)
        self.assertNotIn("cases _d", text)
        self.assertNotIn("refute_with_decidable", text)

    def test_elimination_requires_an_immediate_operand(self):
        source = "".join("(declare-const %s Bool)" % atom for atom in "pqr")
        source += """\
(assert (and p q r))(assert (not (or p q r)))
(assert (and (and p q) r))(assert (not (or (or p q) r)))
(assert (or p q r))(assert (not p))(assert false)
"""
        for rule, premise, conclusion in [
            ("and-elim", 0, "(and p q)"), ("and-elim", 0, "(not p)"),
            ("and-elim", 2, "p"), ("and-elim", 4, "p"),
            ("not-or-elim", 1, "p"), ("not-or-elim", 1, "(not (and p q))"),
            ("not-or-elim", 3, "(not p)"), ("not-or-elim", 4, "(not p)"),
            ("not-or-elim", 5, "(not p)"),
        ]:
            with self.subTest(rule=rule, premise=premise, conclusion=conclusion):
                certificate = make_certificate(source, [
                    (rule, [premise], conclusion), ("asserted", [], "false"),
                ])
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, rule):
                    proof_to_lean.reconstruct(source, certificate)

    def test_invalid_structural_step_never_replaces_an_artifact(self):
        source = LITERAL + "(assert false)"
        certificate = make_certificate(source, [
            ("symm", [0], "(= p p)"), ("asserted", [], "false"),
        ])
        with tempfile.TemporaryDirectory() as directory, \
                patch.object(proof_to_lean.subprocess, "run") as checker:
            output = Path(directory) / "proof.lean"
            output.write_text("previous artifact")
            with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "symm"):
                proof_to_lean.check_and_write(source, certificate, output)
            checker.assert_not_called()
            self.assertEqual(output.read_text(), "previous artifact")
            self.assertEqual(list(Path(directory).iterdir()), [output])

    def test_duplicate_assertions_remain_in_the_theorem(self):
        source = "(declare-const p Bool)(assert p)(assert p)(assert (not p))"
        text = proof_to_lean.reconstruct(source, proof_certificate.export_certificate(source))
        self.assertEqual(text.count("    (_h"), 3)

    def test_different_original_source_is_rejected(self):
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "source does not match"):
            proof_to_lean.reconstruct(LITERAL + "\n", self.certificate)

    def test_matching_source_text_does_not_authorize_changed_assertions(self):
        self.certificate["assertions"][1] = self.certificate["assertions"][0]
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "assertions do not match"):
            proof_to_lean.reconstruct(LITERAL, self.certificate)

    def test_matching_source_text_does_not_authorize_changed_symbols(self):
        for decl in self.certificate["declarations"]:
            if decl["kind"] == z3.Z3_OP_UNINTERPRETED:
                decl["name"] = "different_atom"
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "assertions do not match"):
            proof_to_lean.reconstruct(LITERAL, self.certificate)

    def test_duplicate_symbol_names_cannot_merge_distinct_declarations(self):
        certificate = copy.deepcopy(self.certificate)
        variable = certificate["nodes"][certificate["assertions"][0]]["declaration"]
        certificate["declarations"].append(copy.deepcopy(certificate["declarations"][variable]))
        for node in certificate["nodes"]:
            node["arguments"] = [arg + 1 if arg >= 1 else arg for arg in node["arguments"]]
        certificate["nodes"].insert(1, {
            "declaration": len(certificate["declarations"]) - 1, "arguments": [],
        })
        certificate["assertions"] = [arg + 1 if arg >= 1 else arg for arg in certificate["assertions"]]
        certificate["proof"] += 1
        certificate["nodes"][certificate["assertions"][1]]["arguments"] = [1]
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "ambiguous Boolean symbol"):
            proof_to_lean.reconstruct(LITERAL, certificate)

    def test_unjustified_asserted_fact_is_rejected(self):
        source = "(declare-const p Bool)(assert p)"
        certificate = make_certificate(source, [("asserted", [], "false")])
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "not an original assertion"):
            proof_to_lean.reconstruct(source, certificate)

    def test_incorrect_intermediate_resolvent_is_rejected(self):
        source = "(declare-const p Bool)(declare-const q Bool)"
        source += "(assert (or p q))(assert (not p))(assert (not q))"
        certificate = make_certificate(source, [
            ("unit-resolution", [0, 1], "p"),
            ("unit-resolution", [3, 1], "false"),
        ])
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "incorrect unit-resolution"):
            proof_to_lean.reconstruct(source, certificate)

    def test_unmatched_unit_is_rejected_even_in_an_unused_step(self):
        source = "(declare-const p Bool)(declare-const q Bool)"
        source += "(assert (or p q))(assert p)(assert (not p))"
        certificate = make_certificate(source, [
            ("unit-resolution", [0, 1], "q"),
            ("unit-resolution", [1, 2], "false"),
        ])
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "unmatched unit"):
            proof_to_lean.reconstruct(source, certificate)

    def test_unsupported_native_rules_are_rejected(self):
        certificate = proof_certificate.export_certificate(UNSUPPORTED)
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "unsupported native proof rule"):
            proof_to_lean.reconstruct(UNSUPPORTED, certificate)
        for kind, name in [(z3.Z3_OP_PR_HYPOTHESIS, "hypothesis"),
                           (z3.Z3_OP_PR_TH_LEMMA, "th-lemma"),
                           (z3.Z3_OP_PR_TRANSITIVITY_STAR, "trans*"),
                           (z3.Z3_OP_PR_REWRITE_STAR, "rewrite*"),
                           (z3.Z3_OP_PR_MODUS_PONENS_OEQ, "mp~"),
                           (z3.Z3_OP_PR_DEF_AXIOM, "def-axiom")]:
            certificate = copy.deepcopy(self.certificate)
            for decl in certificate["declarations"]:
                if decl["kind"] == z3.Z3_OP_PR_ASSERTED:
                    decl["kind"], decl["name"] = kind, name
            with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "unsupported native proof rule"):
                proof_to_lean.reconstruct(LITERAL, certificate)

    def test_invalid_indices_and_cycles_are_rejected(self):
        root = self.certificate["proof"]
        for value in [-1, True, 0.0, "0", len(self.certificate["nodes"]), root]:
            with self.subTest(value=value):
                certificate = copy.deepcopy(self.certificate)
                certificate["nodes"][root]["arguments"][0] = value
                with self.assertRaises(proof_to_lean.ReconstructionError):
                    proof_to_lean.reconstruct(LITERAL, certificate)

    def test_wrong_argument_sort_and_arity_are_rejected(self):
        root = self.certificate["proof"]
        for arguments in [[self.certificate["assertions"][0]] * 3, [], [0]]:
            certificate = copy.deepcopy(self.certificate)
            certificate["nodes"][root]["arguments"] = arguments
            with self.assertRaises(proof_to_lean.ReconstructionError):
                proof_to_lean.reconstruct(LITERAL, certificate)

    def test_invalid_headers_and_shapes_are_rejected(self):
        mutations = [
            ("format_version", True), ("format_version", 2), ("result", "sat"),
            ("verification", "verified"), ("fragment", "arithmetic"),
            ("source_smt2", None), ("z3_version", ""),
            ("nodes", {}), ("declarations", []), ("assertions", "0"),
            ("proof", True), ("proof", -1), ("rule_counts", {}),
        ]
        for field, value in mutations:
            with self.subTest(field=field, value=value):
                certificate = copy.deepcopy(self.certificate)
                certificate[field] = value
                with self.assertRaises(proof_to_lean.ReconstructionError):
                    proof_to_lean.reconstruct(LITERAL, certificate)

    def test_missing_and_unexpected_fields_are_rejected(self):
        for target in ["header", "node", "declaration"]:
            for remove in [True, False]:
                with self.subTest(target=target, remove=remove):
                    certificate = copy.deepcopy(self.certificate)
                    record = certificate if target == "header" else certificate[target + "s"][0]
                    if remove:
                        del record[next(iter(record))]
                    else:
                        record["unexpected"] = True
                    with self.assertRaises(proof_to_lean.ReconstructionError):
                        proof_to_lean.reconstruct(LITERAL, certificate)

    def test_forged_declarations_are_rejected(self):
        for key, value in [("kind", True), ("kind", -1), ("range", "Int"),
                           ("domain", ["Proof"]), ("parameters", [1])]:
            with self.subTest(key=key, value=value):
                certificate = copy.deepcopy(self.certificate)
                certificate["declarations"][0][key] = value
                with self.assertRaises(proof_to_lean.ReconstructionError):
                    proof_to_lean.reconstruct(LITERAL, certificate)
        certificate = copy.deepcopy(self.certificate)
        for decl in certificate["declarations"]:
            if decl["kind"] == z3.Z3_OP_FALSE:
                decl["name"] = "true"
        with self.assertRaises(proof_to_lean.ReconstructionError):
            proof_to_lean.reconstruct(LITERAL, certificate)

    def test_false_proof_root_and_rule_count_claims_are_rejected(self):
        certificate = copy.deepcopy(self.certificate)
        certificate["proof"] = certificate["assertions"][0]
        with self.assertRaises(proof_to_lean.ReconstructionError):
            proof_to_lean.reconstruct(LITERAL, certificate)
        for value in [True, 100, 0, "1"]:
            certificate = copy.deepcopy(self.certificate)
            certificate["rule_counts"]["unit-resolution"] = value
            with self.assertRaises(proof_to_lean.ReconstructionError):
                proof_to_lean.reconstruct(LITERAL, certificate)

    def test_duplicate_json_keys_are_rejected(self):
        for text in ['{"proof": 0, "proof": 1}', '{"node": {"arguments": [], "arguments": [0]}}']:
            with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "duplicate JSON field"):
                proof_to_lean.load_certificate(io.StringIO(text))

    def test_symbols_cannot_inject_lean_declarations(self):
        name = "|p\naxiom injected : False\n|"
        source = "(declare-const %s Bool)(assert %s)(assert (not %s))" % (name, name, name)
        text = proof_to_lean.reconstruct(source, proof_certificate.export_certificate(source))
        self.assertIn("\\naxiom injected", text)
        self.assertNotIn("\naxiom injected", text)
        self.assertNotIn(name, text)

    def test_deep_input_preserves_formula_sharing(self):
        source = "(declare-const p Bool)(assert " + "(not " * 1200 + "p"
        source += ")" * 1200 + ")(assert false)"
        certificate = proof_certificate.export_certificate(source)
        text = proof_to_lean.reconstruct(source, certificate)
        boolean_nodes = sum(certificate["declarations"][node["declaration"]]["range"] == "Bool"
                            for node in certificate["nodes"])
        self.assertEqual(text.count("\ndef formula_"), boolean_nodes)
        self.assertLess(len(text), 200_000)

    def test_publication_requires_a_successful_lean_check(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "proof.lean"
            output.write_text("old proof")
            with patch.object(proof_to_lean.subprocess, "run",
                              side_effect=subprocess.CalledProcessError(1, ["lean"], stderr="rejected")):
                with self.assertRaises(subprocess.CalledProcessError):
                    proof_to_lean.check_and_write(LITERAL, self.certificate, output)
            self.assertEqual(output.read_text(), "old proof")
            self.assertEqual(list(Path(directory).iterdir()), [output])
            with patch.object(proof_to_lean.subprocess, "run") as checker:
                proof_to_lean.check_and_write(LITERAL, self.certificate, output)
            checker.assert_called_once()
            self.assertTrue(checker.call_args.kwargs["check"])
            self.assertEqual(checker.call_args.args[0][0], str(proof_to_lean._CHECK_LEAN))
            self.assertIn("theorem unsat", output.read_text())
            self.assertEqual(list(Path(directory).iterdir()), [output])

    def test_bad_certificate_never_invokes_lean_or_creates_an_output(self):
        with tempfile.TemporaryDirectory() as directory, \
                patch.object(proof_to_lean.subprocess, "run") as checker:
            self.certificate["source_smt2"] = "different"
            output = Path(directory) / "proof.lean"
            with self.assertRaises(proof_to_lean.ReconstructionError):
                proof_to_lean.check_and_write(LITERAL, self.certificate, output)
            checker.assert_not_called()
            self.assertEqual(list(Path(directory).iterdir()), [])

    def test_missing_checker_and_wrong_output_extension_fail(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "proof.lean"
            with patch.object(proof_to_lean, "_CHECK_LEAN", Path(directory) / "missing-checker"):
                with self.assertRaises(OSError):
                    proof_to_lean.check_and_write(LITERAL, self.certificate, output)
            self.assertEqual(list(Path(directory).iterdir()), [])
            with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "must end in .lean"):
                proof_to_lean.check_and_write(LITERAL, self.certificate, output.with_suffix(".json"))


if __name__ == "__main__":
    unittest.main()
