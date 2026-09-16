############################################
# Copyright (c) 2026 Microsoft Corporation
#
# End-to-end tests requiring both native Z3 bindings and the pinned Lean toolchain.
############################################
import hashlib
import itertools
import json
import os
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
from test_proof_to_lean import CLAUSE, LITERAL, REWRITE, make_certificate


class TestProofToLeanIntegration(unittest.TestCase):
    def check(self, source, certificate):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "checked proof.lean"
            proof_to_lean.check_and_write(source, certificate, output)
            text = output.read_text()
            namespace = "Z3Proofs.NativeCertificate.p" + hashlib.sha256(source.encode()).hexdigest()
            output.write_text(text + "\n#print axioms " + namespace + ".unsat\n")
            result = subprocess.run(
                [str(proof_to_lean._CHECK_LEAN), str(output)], text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("does not depend on any axioms", result.stdout)
            return text

    def test_real_exported_refutations_are_checked_without_axioms(self):
        for source in [LITERAL, CLAUSE, "(assert false)"]:
            with self.subTest(source=source):
                self.check(source, proof_certificate.export_certificate(source))

    def test_both_complement_orientations(self):
        source = "(declare-const p Bool)(declare-const q Bool)"
        source += "(assert (or (not p) q))(assert p)(assert (not q))"
        self.check(source, make_certificate(source, [
            ("unit-resolution", [0, 1, 2], "false"),
        ]))

    def test_shared_derived_proofs(self):
        source = "".join("(declare-const %s Bool)" % atom for atom in "pqrs")
        source += """\
(assert (or p q))(assert (not p))
(assert (or (not q) r))(assert (or (not q) s))
(assert (or (not r) (not s)))
"""
        certificate = make_certificate(source, [
            ("unit-resolution", [0, 1], "q"),
            ("unit-resolution", [2, 5], "r"),
            ("unit-resolution", [3, 5], "s"),
            ("unit-resolution", [4, 6, 7], "false"),
        ])
        text = self.check(source, certificate)
        self.assertEqual(text.count("  let _step_"), 9)

    def test_residual_clauses_reordering_and_factoring(self):
        source = "".join("(declare-const %s Bool)" % atom for atom in "pqr")
        source += "(assert (or p p q r))(assert (not p))(assert (not q))(assert (not r))"
        self.check(source, make_certificate(source, [
            ("unit-resolution", [0, 1], "(or r q)"),
            ("unit-resolution", [4, 2, 3], "false"),
        ]))

    def test_empty_singleton_and_false_containing_clauses(self):
        for clause in ["false", "(or p)", "(or false p)", "(or p false)"]:
            with self.subTest(clause=clause):
                source = "(declare-const p Bool)(assert %s)" % clause
                units = []
                if clause != "false":
                    source += "(assert (not p))"
                    units = [1]
                self.check(source, make_certificate(source, [
                    ("unit-resolution", [0] + units, "false"),
                ]))

    def test_unusual_symbol_names_are_only_escaped_metadata(self):
        name = "|p\naxiom injected : False\n|"
        source = "(declare-const %s Bool)(assert %s)(assert (not %s))" % (name, name, name)
        self.check(source, proof_certificate.export_certificate(source))

    def test_boolean_translation_truth_tables(self):
        cases = [
            ("true", lambda p, q, r: True),
            ("false", lambda p, q, r: False),
            ("(not p)", lambda p, q, r: not p),
            ("(and p q r)", lambda p, q, r: p and q and r),
            ("(or p q r)", lambda p, q, r: p or q or r),
            ("(=> p q)", lambda p, q, r: not p or q),
            ("(=> p q r)", lambda p, q, r: not p or not q or r),
            ("(= p q)", lambda p, q, r: p == q),
            ("(= p q r)", lambda p, q, r: p == q == r),
            ("(xor p q)", lambda p, q, r: p != q),
            ("(xor p q r)", lambda p, q, r: (p != q) != r),
            ("(ite p q r)", lambda p, q, r: q if p else r),
            ("(distinct p q)", lambda p, q, r: p != q),
            ("(distinct p q r)", lambda p, q, r: len({p, q, r}) == 3),
        ]
        files = ["import Init\n"]
        for expression, evaluate in cases:
            source = "".join("(declare-const %s Bool)" % atom for atom in "pqr")
            source += "(assert %s)(assert false)" % expression
            certificate = make_certificate(source, [])
            text = proof_to_lean.reconstruct(source, certificate)
            files.append(text[len("import Init\n"):])
            namespace = "Z3Proofs.NativeCertificate.p" + hashlib.sha256(source.encode()).hexdigest()
            reachable, pending = set(), [certificate["assertions"][0]]
            while pending:
                node = pending.pop()
                if node not in reachable:
                    reachable.add(node)
                    pending.extend(certificate["nodes"][node]["arguments"])
            definitions = [
                namespace + ".formula_%d" % node
                for node in sorted(reachable)
            ]
            atoms = [decl["name"] for decl in certificate["declarations"]
                     if decl["kind"] == z3.Z3_OP_UNINTERPRETED]
            for values in itertools.product([False, True], repeat=3):
                assignment = dict(zip("pqr", values))
                valuation = "False"
                for index, name in reversed(list(enumerate(atoms))):
                    valuation = "if _i = %d then %s else %s" % (
                        index, str(assignment[name]), valuation)
                formula = "%s.formula_%d (fun _i => %s)" % (
                    namespace, certificate["assertions"][0], valuation)
                files.append("example : (%s) <-> %s := by\n  unfold %s\n  decide\n" % (
                    formula, str(evaluate(*values)), " ".join(reversed(definitions))))
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "truth_tables.lean"
            path.write_text("\n".join(files))
            result = subprocess.run(
                [str(proof_to_lean._CHECK_LEAN), str(path)], capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_lean_rejects_bad_generated_terms_without_publication(self):
        certificate = proof_certificate.export_certificate(LITERAL)
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "proof.lean"
            output.write_text("previous artifact")
            for bad_term in ["theorem unsat : False := True.intro\n",
                             "theorem unsat : False := by sorry\n"]:
                with self.subTest(term=bad_term):
                    with patch.object(proof_to_lean, "reconstruct", return_value=bad_term):
                        with self.assertRaises(subprocess.CalledProcessError):
                            proof_to_lean.check_and_write(LITERAL, certificate, output)
                    self.assertEqual(output.read_text(), "previous artifact")
                    self.assertEqual(list(Path(directory).iterdir()), [output])

    def test_cli_publishes_only_supported_checked_proofs(self):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            original = directory / "input.smt2"
            certificate = directory / "proof.json"
            output = directory / "result.lean"
            original.write_text(CLAUSE)
            certificate.write_text(json.dumps(proof_certificate.export_certificate(CLAUSE)))
            command = [sys.executable, str(_EXAMPLES / "proof_to_lean.py"),
                       str(original), str(certificate), "-o", str(output)]
            result = subprocess.run(command, text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("Lean checked the refutation", result.stdout)
            previous = output.read_text()
            original.write_text(REWRITE)
            certificate.write_text(json.dumps(proof_certificate.export_certificate(REWRITE)))
            result = subprocess.run(command, text=True, capture_output=True)
            self.assertEqual(result.returncode, 2)
            self.assertIn("unsupported native proof rule", result.stderr)
            self.assertEqual(output.read_text(), previous)
            self.assertEqual(set(directory.iterdir()), {original, certificate, output})

    def test_cli_rejects_tampering_and_input_overwrite(self):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            original = directory / "input.smt2"
            certificate_path = directory / "proof.json"
            output = directory / "result.lean"
            original.write_text(LITERAL)
            certificate = proof_certificate.export_certificate(LITERAL)
            certificate_path.write_text(json.dumps(certificate))
            command = [sys.executable, str(_EXAMPLES / "proof_to_lean.py"),
                       str(original), str(certificate_path), "-o"]
            for target in [original, certificate_path]:
                result = subprocess.run(command + [str(target)], text=True, capture_output=True)
                self.assertEqual(result.returncode, 2)
                self.assertIn("must not overwrite", result.stderr)
            alias = directory / "alias.lean"
            os.link(original, alias)
            result = subprocess.run(command + [str(alias)], text=True, capture_output=True)
            self.assertEqual(result.returncode, 2)
            self.assertIn("must not overwrite", result.stderr)
            self.assertEqual(original.read_text(), LITERAL)
            certificate["assertions"][1] = certificate["assertions"][0]
            certificate_path.write_text(json.dumps(certificate))
            result = subprocess.run(command + [str(output)], text=True, capture_output=True)
            self.assertEqual(result.returncode, 2)
            self.assertIn("assertions do not match", result.stderr)
            self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
