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
        for source in [LITERAL, CLAUSE, "(assert false)"]:
            with self.subTest(source=source):
                certificate = proof_certificate.export_certificate(source)
                text = proof_to_lean.reconstruct(source, certificate)
                self.assertIn("theorem unsat", text)
                self.assertIn(": False :=", text)
                self.assertNotIn("sorry", text)
                self.assertNotIn("axiom ", text)
                self.assertNotIn("native_decide", text)
                self.assertEqual(text.count("  let _step_"), sum(certificate["rule_counts"].values()))

    def test_reconstruction_does_not_run_solver_search(self):
        with patch.object(z3.Solver, "check", side_effect=AssertionError("solver oracle invoked")):
            proof_to_lean.reconstruct(LITERAL, self.certificate)

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
        certificate = proof_certificate.export_certificate(REWRITE)
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "unsupported native proof rule"):
            proof_to_lean.reconstruct(REWRITE, certificate)
        for kind, name in [(z3.Z3_OP_PR_HYPOTHESIS, "hypothesis"),
                           (z3.Z3_OP_PR_TH_LEMMA, "th-lemma")]:
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
