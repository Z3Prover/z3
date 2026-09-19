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
from test_proof_to_lean import (
    CLAUSE, CONJUNCTION, LITERAL, REWRITE, STRUCTURAL, UNSUPPORTED, make_certificate,
)


class TestProofToLeanIntegration(unittest.TestCase):
    def check(self, source, certificate):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "checked proof.lean"
            proof_to_lean.check_and_write(source, certificate, output)
            text = output.read_text()
            namespace = "Z3Proofs.NativeCertificate.p" + hashlib.sha256(source.encode()).hexdigest()
            theorems = ["unsat"] + [
                "rewrite_%d" % node for node, raw in enumerate(certificate["nodes"])
                if certificate["declarations"][raw["declaration"]]["kind"] == z3.Z3_OP_PR_REWRITE
            ]
            output.write_text(text + "".join(
                "\n#print axioms %s.%s\n" % (namespace, theorem) for theorem in theorems))
            result = subprocess.run(
                [str(proof_to_lean._CHECK_LEAN), str(output)], text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout.count("does not depend on any axioms"), len(theorems))
            return text

    def test_real_exported_refutations_are_checked_without_axioms(self):
        for source in [LITERAL, CLAUSE, REWRITE, CONJUNCTION, STRUCTURAL,
                       "(assert false)", "(assert (not true))"]:
            with self.subTest(source=source):
                self.check(source, proof_certificate.export_certificate(source))

    def test_documented_boolean_rewrite_example(self):
        source = (_EXAMPLES.parents[1] / "lean" / "examples" / "boolean_rewrite.smt2").read_text()
        certificate = proof_certificate.export_certificate(source)
        self.assertEqual(set(certificate["rule_counts"]), {"asserted", "mp", "rewrite", "unit-resolution"})
        with patch.object(z3.Solver, "check", side_effect=AssertionError("solver oracle invoked")):
            self.check(source, certificate)

    def test_documented_structural_boolean_example(self):
        source = (_EXAMPLES.parents[1] / "lean" / "examples" / "boolean_structural.smt2").read_text()
        certificate = proof_certificate.export_certificate(source)
        self.assertTrue({"trans", "monotonicity", "not-or-elim"} <= set(certificate["rule_counts"]))
        with patch.object(z3.Solver, "check", side_effect=AssertionError("solver oracle invoked")):
            self.check(source, certificate)

    def test_reflexivity_symmetry_and_transitivity_chains(self):
        source = "".join("(declare-const %s Bool)" % atom for atom in "pqr")
        source += "(assert (= p q))(assert (= q r))(assert p)(assert (not r))"
        certificate = make_certificate(source, [
            ("refl", [], "(= p p)"),
            ("symm", [0], "(= q p)"),
            ("symm", [5], "(= p q)"),
            ("trans", [4, 6], "(= p q)"),
            ("trans", [7, 1], "(= p r)"),
            ("mp", [2, 8], "r"),
            ("unit-resolution", [9, 3], "false"),
        ])
        text = self.check(source, certificate)
        self.assertIn("Iff.refl", text)
        self.assertIn("Iff.symm", text)
        self.assertIn("Iff.trans", text)
        self.assertNotIn("cases _d", text)

    def test_monotonicity_for_all_boolean_operators(self):
        cases = [
            ("p", "p", []), ("true", "true", []), ("false", "false", []),
            ("(not p)", "(not s)", [0]),
            ("(and p)", "(and s)", [0]), ("(or p)", "(or s)", [0]),
            ("(and p q r)", "(and s t u)", [2, 0, 1]),
            ("(or p q r)", "(or s t u)", [2, 0, 1]),
            ("(and p q p r)", "(and s q s r)", [0, 0]),
            ("(=> p q)", "(=> s t)", [1, 0]),
            ("(= p q)", "(= s t)", [0, 1]),
            ("(xor p q)", "(xor s t)", [0, 1]),
            ("(ite p q r)", "(ite s t u)", [2, 0, 1]),
            ("(distinct p q)", "(distinct s t)", [0, 1]),
            ("(distinct p q r)", "(distinct s t u)", [0, 1, 2]),
        ]
        for left, right, premises in cases:
            with self.subTest(left=left, right=right):
                source = "".join("(declare-const %s Bool)" % atom for atom in "pqrstu")
                source += "(assert (= p s))(assert (= q t))(assert (= r u))"
                source += "(assert %s)(assert (not %s))" % (left, right)
                certificate = make_certificate(source, [
                    ("monotonicity", premises, "(= %s %s)" % (left, right)),
                    ("mp", [3, 5], right),
                    ("unit-resolution", [4, 6], "false"),
                ])
                text = self.check(source, certificate)
                self.assertNotIn("cases _d", text)
                self.assertNotIn("refute_with_decidable", text)

    def test_shared_nested_congruence_proofs(self):
        source = "(declare-const p Bool)(declare-const q Bool)(assert (= p q))"
        source += "(assert (and (not p) (not p)))(assert (not (and (not q) (not q))))"
        certificate = make_certificate(source, [
            ("monotonicity", [0], "(= (not p) (not q))"),
            ("monotonicity", [3], "(= (and (not p) (not p)) (and (not q) (not q)))"),
            ("mp", [1, 4], "(and (not q) (not q))"),
            ("unit-resolution", [5, 2], "false"),
        ])
        text = self.check(source, certificate)
        self.assertEqual(text.count("not_congr"), 1)
        self.assertEqual(text.count("and_congr"), 1)
        self.assertEqual(text.count("  let _step_"), 7)

    def test_large_congruence_does_not_enumerate_truth_assignments(self):
        size = 24
        source = "".join("(declare-const %s%d Bool)" % (prefix, index)
                         for prefix in ["p", "q"] for index in range(size))
        source += "".join("(assert (= p%d q%d))" % (index, index) for index in range(size))
        left = "(and %s)" % " ".join("p%d" % index for index in range(size))
        right = "(and %s)" % " ".join("q%d" % index for index in range(size))
        source += "(assert %s)(assert (not %s))" % (left, right)
        certificate = make_certificate(source, [
            ("monotonicity", list(reversed(range(size))), "(= %s %s)" % (left, right)),
            ("mp", [size, size + 2], right),
            ("unit-resolution", [size + 3, size + 1], "false"),
        ])
        text = self.check(source, certificate)
        self.assertEqual(text.count("and_congr"), size - 1)
        self.assertNotIn("cases _d", text)
        self.assertNotIn("Decidable", text)

    def test_conjunction_elimination_positions_and_nesting(self):
        for conjunction, target in [
            ("(and p q r)", "p"), ("(and p q r)", "q"), ("(and p q r)", "r"),
            ("(and p)", "p"), ("(and p p q)", "q"),
            ("(and (and p q) r)", "(and p q)"),
        ]:
            with self.subTest(conjunction=conjunction, target=target):
                source = "".join("(declare-const %s Bool)" % atom for atom in "pqr")
                source += "(assert %s)(assert (not %s))" % (conjunction, target)
                self.check(source, make_certificate(source, [
                    ("and-elim", [0], target),
                    ("unit-resolution", [2, 1], "false"),
                ]))
        source = "(declare-const p Bool)(declare-const q Bool)(declare-const r Bool)"
        source += "(assert (and (and p q) r))(assert (not q))"
        self.check(source, make_certificate(source, [
            ("and-elim", [0], "(and p q)"),
            ("and-elim", [2], "q"),
            ("unit-resolution", [3, 1], "false"),
        ]))

    def test_negated_disjunction_elimination_in_both_orientations(self):
        for disjunction, target, complement, decidable in [
            ("(or p q r)", "(not p)", "p", False),
            ("(or p q r)", "(not q)", "q", False),
            ("(or p q r)", "(not r)", "r", False),
            ("(or p)", "(not p)", "p", False),
            ("(or p p q)", "(not q)", "q", False),
            ("(or (not p) q)", "p", "(not p)", True),
            ("(or (not p) q)", "(not (not p))", "(not p)", False),
            ("(or (not p) (not (and q r)))", "(and q r)", "(not (and q r))", True),
            ("(or (not (not p)) q)", "(not p)", "p", True),
            ("(or (or p q) r)", "(not (or p q))", "(or p q)", False),
        ]:
            with self.subTest(disjunction=disjunction, target=target):
                source = "".join("(declare-const %s Bool)" % atom for atom in "pqr")
                source += "(assert (not %s))(assert %s)" % (disjunction, complement)
                text = self.check(source, make_certificate(source, [
                    ("not-or-elim", [0], target),
                    ("unit-resolution", [2, 1], "false"),
                ]))
                self.assertEqual("refute_with_decidable" in text, decidable)
                statement = text.split("theorem unsat", 1)[1].split(": False :=", 1)[0]
                self.assertNotIn("Decidable", statement)
                self.assertEqual(statement.count("    (_h"), 2)

    def test_mp_chains_implications_and_boolean_equalities(self):
        source = "".join("(declare-const %s Bool)" % atom for atom in "pqr")
        source += "(assert p)(assert (=> p q))(assert (= q r))(assert (not r))"
        self.check(source, make_certificate(source, [
            ("mp", [0, 1], "q"),
            ("mp", [4, 2], "r"),
            ("unit-resolution", [5, 3], "false"),
        ]))

    def test_shared_rewrite_proofs(self):
        source = "(declare-const p Bool)(declare-const q Bool)"
        source += "(assert p)(assert (=> p q))(assert (=> p q))(assert (not q))"
        certificate = make_certificate(source, [
            ("rewrite", [], "(= (=> p q) (or q (not p)))"),
            ("mp", [1, 4], "(or q (not p))"),
            ("mp", [2, 4], "(or q (not p))"),
            ("unit-resolution", [5, 0], "q"),
            ("unit-resolution", [6, 0], "q"),
            ("unit-resolution", [3, 7, 8], "false"),
        ])
        text = self.check(source, certificate)
        self.assertEqual(text.count("private theorem rewrite_"), 1)
        self.assertEqual(text.count("  let _step_"), 10)

    def test_native_iff_rewrite_and_structural_rules(self):
        source = "(declare-const p Bool)(assert (not (not p)))(assert (not p))"
        certificate = make_certificate(source, [
            ("rewrite", [], "(= (not (not p)) p)"),
            ("symm", [2], "(= p (not (not p)))"),
            ("symm", [3], "(= (not (not p)) p)"),
            ("refl", [], "(= p p)"),
            ("trans", [4, 5], "(= (not (not p)) p)"),
            ("mp", [0, 6], "p"),
            ("unit-resolution", [7, 1], "false"),
        ])
        for declaration in certificate["declarations"]:
            if declaration["kind"] == z3.Z3_OP_EQ:
                declaration["kind"], declaration["name"] = z3.Z3_OP_IFF, "iff"
        self.check(source, certificate)

    def test_boolean_rewrite_truth_tables(self):
        equivalences = [
            ("(not true)", "false"),
            ("(not false)", "true"),
            ("(not (not p))", "p"),
            ("(and p)", "p"),
            ("(or p)", "p"),
            ("(and p true)", "p"),
            ("(or p false)", "p"),
            ("(or p p)", "p"),
            ("(and p q r)", "(and r p q)"),
            ("(or p q r)", "(or r p q)"),
            ("(=> p q)", "(or (not p) q)"),
            ("(not (and p q))", "(or (not p) (not q))"),
            ("(not (or p q))", "(and (not p) (not q))"),
            ("(and p (or q r))", "(or (and p q) (and p r))"),
            ("(= p q)", "(and (=> p q) (=> q p))"),
            ("(xor p q)", "(not (= p q))"),
            ("(ite p q r)", "(or (and p q) (and (not p) r))"),
            ("(distinct p q)", "(xor p q)"),
            ("(distinct p q r)", "false"),
            ("(or p (not p))", "true"),
        ]
        source = "".join("(declare-const %s Bool)" % atom for atom in "pqr")
        source += "(assert (or p q r))(assert false)"
        steps = [("rewrite", [], "(= %s %s)" % pair) for pair in equivalences]
        steps.append(("asserted", [], "false"))
        self.check(source, make_certificate(source, steps))

    def test_lean_rejects_false_rewrites_without_publication(self):
        source = "(declare-const p Bool)(declare-const q Bool)(assert p)(assert (not q))"
        false_refutation = make_certificate(source, [
            ("rewrite", [], "(= p q)"),
            ("mp", [0, 2], "q"),
            ("unit-resolution", [3, 1], "false"),
        ])
        unused_source = "(declare-const p Bool)(assert p)(assert false)"
        unused_rewrite = make_certificate(unused_source, [
            ("rewrite", [], "(= p false)"), ("asserted", [], "false"),
        ])
        conditional_source = "".join("(declare-const %s Bool)" % atom for atom in "pqr")
        conditional_source += "(assert (or p q r))(assert false)"
        conditional_rewrite = make_certificate(conditional_source, [
            ("rewrite", [], "(= (or p q r) true)"), ("asserted", [], "false"),
        ])
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "proof.lean"
            output.write_text("previous artifact")
            for original, certificate in [
                (source, false_refutation), (unused_source, unused_rewrite),
                (conditional_source, conditional_rewrite),
            ]:
                with self.subTest(source=original):
                    with self.assertRaises(subprocess.CalledProcessError):
                        proof_to_lean.check_and_write(original, certificate, output)
                    self.assertEqual(output.read_text(), "previous artifact")
                    self.assertEqual(list(Path(directory).iterdir()), [output])

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
            original.write_text(REWRITE)
            certificate.write_text(json.dumps(proof_certificate.export_certificate(REWRITE)))
            result = subprocess.run(command, text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("Lean checked the refutation", result.stdout)
            original.write_text(STRUCTURAL)
            certificate.write_text(json.dumps(proof_certificate.export_certificate(STRUCTURAL)))
            result = subprocess.run(command, text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("Lean checked the refutation", result.stdout)
            previous = output.read_text()
            original.write_text(UNSUPPORTED)
            certificate.write_text(json.dumps(proof_certificate.export_certificate(UNSUPPORTED)))
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
