############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Native certificate validation and Lean source reconstruction tests.
############################################
import copy
from collections import Counter
import io
import itertools
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
import proof_preprocessing
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
BRANCHING = """\
(declare-const p Bool)(declare-const q Bool)
(assert (or p q))(assert (or (not p) q))
(assert (or p (not q)))(assert (or (not p) (not q)))
"""
XOR = """\
(declare-const p Bool)(declare-const q Bool)
(assert (xor p q))(assert p)(assert q)
"""
NESTED = """\
(declare-const p Bool)(declare-const q Bool)(declare-const r Bool)
(assert (or (and p q) r))(assert (not p))(assert (not r))
"""
DEF_AXIOM_CLAUSES = [
    "(or (not p) p)",
    "(or (not (not p)) (not p))",
    "(or (not (and p q r)) p)",
    "(or (not (and p q r)) q)",
    "(or (not (and p q r)) r)",
    "(or (and p q r) (not p) (not q) (not r))",
    "(or (not (or p q r)) p q r)",
    "(or (or p q r) (not p))",
    "(or (or p q r) (not q))",
    "(or (or p q r) (not r))",
    "(or (not (=> p q)) (not p) q)",
    "(or (=> p q) p)",
    "(or (=> p q) (not q))",
    "(or (not (= p q)) p (not q))",
    "(or (not (= p q)) (not p) q)",
    "(or (= p q) p q)",
    "(or (= p q) (not p) (not q))",
    "(or (xor p q) p (not q))",
    "(or (xor p q) (not p) q)",
    "(or (not (xor p q)) p q)",
    "(or (not (xor p q)) (not p) (not q))",
    "(or (not (ite p q r)) (not p) q)",
    "(or (not (ite p q r)) p r)",
    "(or (ite p q r) (not p) (not q))",
    "(or (ite p q r) p (not r))",
]


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
                "hypothesis": z3.Z3_OP_PR_HYPOTHESIS,
                "lemma": z3.Z3_OP_PR_LEMMA,
                "mp": z3.Z3_OP_PR_MODUS_PONENS,
                "rewrite": z3.Z3_OP_PR_REWRITE,
                "def-axiom": z3.Z3_OP_PR_DEF_AXIOM,
                "refl": z3.Z3_OP_PR_REFLEXIVITY,
                "symm": z3.Z3_OP_PR_SYMMETRY,
                "trans": z3.Z3_OP_PR_TRANSITIVITY,
                "trans*": z3.Z3_OP_PR_TRANSITIVITY_STAR,
                "iff-true": z3.Z3_OP_PR_IFF_TRUE,
                "iff-false": z3.Z3_OP_PR_IFF_FALSE,
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
        for source in [LITERAL, CLAUSE, REWRITE, CONJUNCTION, STRUCTURAL, BRANCHING, XOR, NESTED,
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
                self.assertEqual(sum(line.startswith("  let _step_") for line in text.splitlines()),
                                 sum(certificate["rule_counts"].values()))

    def test_reconstruction_does_not_run_solver_search(self):
        for source in [LITERAL, REWRITE, CONJUNCTION, STRUCTURAL, BRANCHING, XOR]:
            certificate = proof_certificate.export_certificate(source)
            with patch.object(z3.Solver, "check", side_effect=AssertionError("solver oracle invoked")):
                proof_to_lean.reconstruct(source, certificate)

    def test_preprocessing_audit_requires_elimination_and_checked_evidence(self):
        successful = [{
            "pipeline": pipeline, "proofs_enabled": proofs, "result": "unsat",
            "preprocessing_observed": True, "branching_search_observed": True,
            "proof_status": "lean-checked" if proofs else "disabled",
            "diagnostics": [],
        } for pipeline in ("simplifier", "tactic") for proofs in (False, True)]
        with patch.object(proof_preprocessing, "_run_pipeline", side_effect=copy.deepcopy(successful)) as run:
            self.assertTrue(proof_preprocessing.audit_preprocessing(LITERAL, require_search=True)["complete"])
            self.assertEqual(run.call_count, 4)
        for index, field, value in [
            (0, "result", "sat"), (1, "result", "unknown"),
            (1, "preprocessing_observed", False), (1, "branching_search_observed", False),
            (1, "proof_status", "reconstruction-rejected"),
            (3, "proof_status", "lean-rejected"), (3, "proof_status", "native-proof-error"),
        ]:
            with self.subTest(index=index, field=field, value=value):
                runs = copy.deepcopy(successful)
                runs[index][field] = value
                with patch.object(proof_preprocessing, "_run_pipeline", side_effect=runs):
                    report = proof_preprocessing.audit_preprocessing(LITERAL, require_search=True)
                self.assertFalse(report["complete"])
        for require_search in [False, True]:
            runs = copy.deepcopy(successful)
            for run in runs:
                run["branching_search_observed"] = False
            with patch.object(proof_preprocessing, "_run_pipeline", side_effect=runs):
                report = proof_preprocessing.audit_preprocessing(LITERAL, require_search=require_search)
            self.assertEqual(report["complete"], not require_search)

    def test_preprocessing_audit_reports_reconstruction_and_lean_errors(self):
        source = (_EXAMPLES.parents[1] / "lean" / "examples" / "boolean_solve_eqs.smt2").read_text()
        errors = [
            (proof_to_lean.ReconstructionError("incorrect substitution proof"), "reconstruction-rejected"),
            (subprocess.CalledProcessError(1, ["lean"], output="bad proof", stderr="rejected"), "lean-rejected"),
        ]
        for pipeline, (error, status) in itertools.product(("simplifier", "tactic"), errors):
            with self.subTest(pipeline=pipeline, status=status):
                with patch.object(proof_preprocessing, "check_and_write", side_effect=error) as checker:
                    report = proof_preprocessing._run_pipeline(source, pipeline, True, 10000)
                self.assertEqual(report["proof_status"], status)
                self.assertTrue(report["diagnostics"])
                self.assertTrue(report["native_proof"])
                self.assertEqual(checker.call_args.args[0], source)
                certificate = checker.call_args.args[1]
                self.assertEqual(certificate["source_smt2"], source)
                self.assertEqual(certificate["verification"], "unverified")
                self.assertEqual(len(certificate["assertions"]), 5)
                proof_to_lean._bind_input(source, proof_to_lean._validate_graph(source, certificate))
                self.assertFalse(checker.call_args.args[2].exists())

    def test_preprocessing_audit_does_not_replay_non_unsat_results(self):
        source = "(declare-const p Bool)(assert p)"
        with patch.object(proof_preprocessing, "check_and_write") as checker:
            report = proof_preprocessing._run_pipeline(source, "simplifier", True, 10000)
        checker.assert_not_called()
        self.assertEqual(report["result"], "sat")
        self.assertEqual(report["proof_status"], "unavailable")
        self.assertTrue(report["diagnostics"])
        with patch.object(z3.Solver, "check", return_value=z3.unknown), \
                patch.object(z3.Solver, "reason_unknown", return_value="test resource limit"), \
                patch.object(proof_preprocessing, "check_and_write") as checker:
            report = proof_preprocessing._run_pipeline(source, "tactic", True, 10000)
        checker.assert_not_called()
        self.assertEqual(report["result"], "unknown")
        self.assertIn("unknown: test resource limit", report["diagnostics"])

    def test_preprocessing_audit_reports_missing_native_proofs(self):
        with patch.object(z3.Solver, "proof", side_effect=z3.Z3Exception("native proof is unavailable")), \
                patch.object(proof_preprocessing, "check_and_write") as checker:
            report = proof_preprocessing._run_pipeline(BRANCHING, "tactic", True, 10000)
        checker.assert_not_called()
        self.assertEqual(report["result"], "unsat")
        self.assertEqual(report["proof_status"], "native-proof-error")
        self.assertIn("native proof is unavailable", report["diagnostics"])
        self.assertNotIn("native_proof", report)

    def test_preprocessing_audit_requires_a_positive_timeout(self):
        for timeout in [0, -1, True, 1.0, "10"]:
            with self.subTest(timeout=timeout):
                with self.assertRaisesRegex(ValueError, "positive integer"):
                    proof_preprocessing.audit_preprocessing(LITERAL, timeout_ms=timeout)

    def test_def_axiom_signatures_are_checked(self):
        original = make_certificate(XOR, [
            ("def-axiom", [], "(or (not (xor p q)) (not p) (not q))"),
            ("unit-resolution", [3, 0, 1, 2], "false"),
        ])
        for key, value in [
            ("name", "forged"), ("domain", []), ("domain", ["Proof", "Bool"]),
            ("domain", ["Bool", "Bool"]), ("range", "Bool"), ("parameters", [1]),
        ]:
            with self.subTest(key=key, value=value):
                certificate = copy.deepcopy(original)
                declaration = next(decl for decl in certificate["declarations"] if decl["name"] == "def-axiom")
                declaration[key] = value
                with self.assertRaises(proof_to_lean.ReconstructionError):
                    proof_to_lean.reconstruct(XOR, certificate)
        source = LITERAL + "(assert false)"
        certificate = make_certificate(source, [
            ("def-axiom", [0], "(or p (not p))"), ("asserted", [], "false"),
        ])
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "invalid def-axiom"):
            proof_to_lean.reconstruct(source, certificate)

    def test_def_axiom_lemmas_are_independent_of_original_assertions(self):
        source = "(declare-const p Bool)(declare-const q Bool)(declare-const r Bool)"
        source += "(assert (or p q r))(assert false)"
        steps = [("def-axiom", [], clause) for clause in DEF_AXIOM_CLAUSES]
        steps.append(("asserted", [], "false"))
        certificate = make_certificate(source, steps)
        with patch.object(z3.Solver, "check", side_effect=AssertionError("solver oracle invoked")):
            text = proof_to_lean.reconstruct(source, certificate)
        self.assertEqual(text.count("private theorem def_axiom_"), len(DEF_AXIOM_CLAUSES))
        lemmas = text.split("private theorem def_axiom_", 1)[1].split("theorem unsat", 1)[0]
        self.assertNotIn("_h0", lemmas)
        self.assertNotIn("_step_", lemmas)
        self.assertNotIn("cases ", lemmas)
        self.assertNotIn("of_decide_eq_true", lemmas)

    def test_forged_def_axioms_are_rejected_even_when_unused(self):
        source = "(declare-const p Bool)(declare-const q Bool)(declare-const r Bool)"
        source += "(assert (or p q r))(assert false)"
        for clause in [
            "false", "p", "(not p)", "(or p q)",
            "(or (not (and p q)) r)", "(or (and p q) (not p))",
            "(or (not (or p q)) p)", "(or (or p q) (not r))",
            "(or (not (=> p q)) p q)", "(or (=> p q) (not p))",
            "(or (not (= p q)) p q)", "(or (= p q) p (not q))",
            "(or (not (xor p q)) p (not q))", "(or (xor p q) p q)",
            "(or (not (ite p q r)) p q)", "(or (ite p q r) (not p) (not r))",
        ]:
            with self.subTest(clause=clause):
                certificate = make_certificate(source, [
                    ("def-axiom", [], clause), ("asserted", [], "false"),
                ])
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "invalid def-axiom clause"):
                    proof_to_lean.reconstruct(source, certificate)

    def test_removing_a_required_def_axiom_literal_is_rejected(self):
        source = "(declare-const p Bool)(declare-const q Bool)(declare-const r Bool)"
        source += "(assert (or p q r))(assert false)"
        context = z3.Context()
        for clause in DEF_AXIOM_CLAUSES:
            parsed = proof_certificate.parse_propositional_assertions(
                source + "(assert %s)" % clause, context)[-1]
            for position in range(parsed.num_args()):
                damaged = "(or %s)" % " ".join(
                    arg.sexpr() for index, arg in enumerate(parsed.children()) if index != position)
                with self.subTest(clause=clause, removed=position):
                    certificate = make_certificate(source, [
                        ("def-axiom", [], damaged), ("asserted", [], "false"),
                    ])
                    with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "invalid def-axiom clause"):
                        proof_to_lean.reconstruct(source, certificate)

    def test_false_gate_clause_polarities_are_rejected(self):
        source = "(declare-const p Bool)(declare-const q Bool)(declare-const r Bool)"
        source += "(assert (or p q r))(assert false)"
        gates = [
            ("(and p q r)", 3, lambda values: all(values)),
            ("(or p q r)", 3, lambda values: any(values)),
            ("(=> p q)", 2, lambda values: not values[0] or values[1]),
            ("(= p q)", 2, lambda values: values[0] == values[1]),
            ("(xor p q)", 2, lambda values: values[0] != values[1]),
            ("(ite p q r)", 3, lambda values: values[1] if values[0] else values[2]),
        ]
        for gate, arity, evaluate in gates:
            for gate_sign in [False, True]:
                for signs in itertools.product([None, False, True], repeat=arity):
                    tautology = all(
                        evaluate(values) == gate_sign
                        or any(sign is not None and value == sign for value, sign in zip(values, signs))
                        for values in itertools.product([False, True], repeat=arity))
                    if tautology:
                        continue
                    literals = [gate if gate_sign else "(not %s)" % gate]
                    literals.extend(atom if sign else "(not %s)" % atom
                                    for atom, sign in zip("pqr", signs) if sign is not None)
                    clause = "(or %s)" % " ".join(literals)
                    with self.subTest(clause=clause):
                        certificate = make_certificate(source, [
                            ("def-axiom", [], clause), ("asserted", [], "false"),
                        ])
                        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "invalid def-axiom clause"):
                            proof_to_lean.reconstruct(source, certificate)

    def test_invalid_def_axioms_never_invoke_lean_or_replace_an_artifact(self):
        source = "(declare-const p Bool)(assert p)"
        certificates = [
            (source, make_certificate(source, [
                ("def-axiom", [], "(not p)"), ("unit-resolution", [0, 1], "false"),
            ])),
            (LITERAL, make_certificate(LITERAL, [
                ("def-axiom", [], "p"), ("unit-resolution", [0, 1], "false"),
            ])),
        ]
        with tempfile.TemporaryDirectory() as directory, \
                patch.object(proof_to_lean.subprocess, "run") as checker:
            output = Path(directory) / "proof.lean"
            output.write_text("previous artifact")
            for original, certificate in certificates:
                with self.subTest(source=original):
                    with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "invalid def-axiom clause"):
                        proof_to_lean.check_and_write(original, certificate, output)
                    checker.assert_not_called()
                    self.assertEqual(output.read_text(), "previous artifact")
                    self.assertEqual(list(Path(directory).iterdir()), [output])

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
            ("iff-true", [0], "(= (= p p) true)"),
            ("iff-false", [2], "(= (or p q) false)"),
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
            ("iff-true", []), ("iff-true", [0, 0]),
            ("iff-false", []), ("iff-false", [2, 2]),
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

    def test_iff_constant_steps_validate_the_fact_and_both_endpoints(self):
        source = "(declare-const p Bool)(declare-const q Bool)"
        source += "(assert p)(assert (not q))(assert (not (not p)))(assert false)"
        for rule, premise, conclusion in [
            ("iff-true", 0, "(= q true)"), ("iff-true", 0, "(= p false)"),
            ("iff-true", 0, "(= true p)"), ("iff-true", 0, "(=> p true)"),
            ("iff-true", 1, "(= q true)"), ("iff-true", 0, "true"),
            ("iff-false", 0, "(= p false)"), ("iff-false", 1, "(= p false)"),
            ("iff-false", 1, "(= q true)"), ("iff-false", 1, "(= false q)"),
            ("iff-false", 2, "(= p false)"), ("iff-false", 1, "false"),
        ]:
            with self.subTest(rule=rule, premise=premise, conclusion=conclusion):
                certificate = make_certificate(source, [
                    (rule, [premise], conclusion), ("asserted", [], "false"),
                ])
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, rule):
                    proof_to_lean.reconstruct(source, certificate)

    def test_transitivity_star_signatures_are_checked(self):
        source = "(declare-const p Bool)(declare-const q Bool)"
        source += "(assert (= p q))(assert false)"
        original = make_certificate(source, [
            ("trans*", [0], "(= p q)"), ("asserted", [], "false"),
        ])
        for key, value in [
            ("name", "trans"), ("domain", []), ("domain", ["Proof"]),
            ("domain", ["Bool", "Bool"]), ("domain", ["Proof", "Bool", "Proof"]),
            ("range", "Bool"), ("parameters", [1]),
        ]:
            with self.subTest(key=key, value=value):
                certificate = copy.deepcopy(original)
                declaration = next(decl for decl in certificate["declarations"] if decl["name"] == "trans*")
                declaration[key] = value
                with self.assertRaises(proof_to_lean.ReconstructionError):
                    proof_to_lean.reconstruct(source, certificate)

    def test_invalid_transitivity_star_steps_are_rejected_even_when_unused(self):
        source = "".join("(declare-const %s Bool)" % atom for atom in "pqrs")
        source += "(assert (= p q))(assert (= r s))(assert (=> q r))(assert false)"
        for premises, conclusion in [
            ([], "(= p q)"), ([0], "(= p r)"), ([0, 1], "(= p s)"),
            ([0, 1], "(= p r)"), ([0, 2], "(= p q)"),
            ([2], "(= p p)"), ([0, 3], "(= p q)"),
            ([0], "(=> p q)"), ([0], "p"), ([0], "false"),
        ]:
            with self.subTest(premises=premises, conclusion=conclusion):
                certificate = make_certificate(source, [
                    ("trans*", premises, conclusion), ("asserted", [], "false"),
                ])
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, r"trans\*"):
                    proof_to_lean.reconstruct(source, certificate)

    def test_transitivity_star_uses_only_supplied_equivalence_paths(self):
        atoms = "pqr"
        edges = [("p", "q"), ("r", "q"), ("p", "r")]
        source = "".join("(declare-const %s Bool)" % atom for atom in atoms)
        source += "".join("(assert (= %s %s))" % edge for edge in edges) + "(assert false)"
        for selected in itertools.product([False, True], repeat=len(edges)):
            premises = [index for index in reversed(range(len(edges))) if selected[index]]
            for left, right in itertools.product(atoms, repeat=2):
                reachable = {left}
                for _ in atoms:
                    for index in premises:
                        first, second = edges[index]
                        if first in reachable or second in reachable:
                            reachable.update((first, second))
                certificate = make_certificate(source, [
                    ("trans*", premises, "(= %s %s)" % (left, right)),
                    ("asserted", [], "false"),
                ])
                with self.subTest(premises=premises, left=left, right=right):
                    if right in reachable:
                        proof_to_lean.reconstruct(source, certificate)
                    else:
                        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "no equivalence path"):
                            proof_to_lean.reconstruct(source, certificate)

    def test_transitivity_star_preserves_hypotheses_from_unused_evidence(self):
        source = "".join("(declare-const %s Bool)" % atom for atom in "pqrs")
        source += "(assert (= p q))(assert p)(assert (not q))(assert (= r s))"
        for hypothesis in ["(= r s)", "(= p q)"]:
            with self.subTest(hypothesis=hypothesis):
                certificate = make_certificate(source, [
                    ("hypothesis", [], hypothesis),
                    ("trans*", [0, 4], "(= p q)"),
                    ("mp", [1, 5], "q"),
                    ("unit-resolution", [2, 6], "false"),
                ])
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "undischarged hypotheses"):
                    proof_to_lean.reconstruct(source, certificate)
        source = LITERAL + "(declare-const r Bool)(declare-const s Bool)(assert (= r s))"
        certificate = make_certificate(source, [
            ("hypothesis", [], "(= r s)"),
            ("trans*", [3], "(= p p)"),
            ("mp", [0, 4], "p"),
            ("unit-resolution", [1, 5], "false"),
        ])
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "undischarged hypotheses"):
            proof_to_lean.reconstruct(source, certificate)

    def test_invalid_transitivity_star_never_publishes_a_proof(self):
        source = "".join("(declare-const %s Bool)" % atom for atom in "pqr")
        source += "(assert (= p q))(assert p)(assert (not r))"
        certificate = make_certificate(source, [
            ("trans*", [0], "(= p r)"),
            ("mp", [1, 3], "r"),
            ("unit-resolution", [2, 4], "false"),
        ])
        with tempfile.TemporaryDirectory() as directory, \
                patch.object(proof_to_lean.subprocess, "run") as checker:
            output = Path(directory) / "proof.lean"
            output.write_text("previous artifact")
            with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "no equivalence path"):
                proof_to_lean.check_and_write(source, certificate, output)
            checker.assert_not_called()
            self.assertEqual(output.read_text(), "previous artifact")
            self.assertEqual(list(Path(directory).iterdir()), [output])

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
        for kind, name in [(z3.Z3_OP_PR_TH_LEMMA, "th-lemma"),
                           (z3.Z3_OP_PR_REWRITE_STAR, "rewrite*"),
                           (z3.Z3_OP_PR_MODUS_PONENS_OEQ, "mp~"),
                           (z3.Z3_OP_PR_DEF_INTRO, "intro-def")]:
            certificate = copy.deepcopy(self.certificate)
            for decl in certificate["declarations"]:
                if decl["kind"] == z3.Z3_OP_PR_ASSERTED:
                    decl["kind"], decl["name"] = kind, name
            with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "unsupported native proof rule"):
                proof_to_lean.reconstruct(LITERAL, certificate)

    def test_hypothesis_and_lemma_signatures_are_checked(self):
        original = proof_certificate.export_certificate(BRANCHING)
        for rule, domains in [
            ("hypothesis", [[], ["Proof", "Bool"], ["Proof"]]),
            ("lemma", [[], ["Bool"], ["Proof", "Proof", "Bool"], ["Bool", "Bool"]]),
        ]:
            for key, value in [("name", "forged")] + [("domain", domain) for domain in domains]:
                with self.subTest(rule=rule, key=key, value=value):
                    certificate = copy.deepcopy(original)
                    declaration = next(decl for decl in certificate["declarations"] if decl["name"] == rule)
                    declaration[key] = value
                    with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "invalid " + rule):
                        proof_to_lean.reconstruct(BRANCHING, certificate)
        source = LITERAL + "(assert false)"
        for rule, premises in [("hypothesis", [0]), ("lemma", []), ("lemma", [0, 1])]:
            with self.subTest(rule=rule, premises=premises):
                certificate = make_certificate(source, [(rule, premises, "false")])
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "invalid " + rule):
                    proof_to_lean.reconstruct(source, certificate)

    def test_open_hypotheses_cannot_prove_unsat(self):
        source = "(declare-const p Bool)(assert p)"
        for steps in [
            [("hypothesis", [], "false")],
            [("hypothesis", [], "(not p)"), ("unit-resolution", [0, 1], "false")],
            [
                ("hypothesis", [], "(not p)"),
                ("unit-resolution", [0, 1], "false"),
                ("lemma", [2], "p"),
                ("unit-resolution", [3, 1], "false"),
            ],
        ]:
            with self.subTest(steps=steps):
                certificate = make_certificate(source, steps)
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "undischarged hypotheses"):
                    proof_to_lean.reconstruct(source, certificate)

    def test_a_lemma_does_not_close_its_shared_premise_globally(self):
        source = "(declare-const p Bool)(assert p)"
        certificate = make_certificate(source, [
            ("hypothesis", [], "(not p)"),
            ("unit-resolution", [0, 1], "false"),
            ("lemma", [2], "p"),
        ])
        certificate["proof"] = certificate["nodes"][certificate["proof"]]["arguments"][0]
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "undischarged hypotheses"):
            proof_to_lean.reconstruct(source, certificate)

    def test_hypotheses_are_not_implicitly_original_assertions(self):
        certificate = make_certificate(LITERAL, [
            ("hypothesis", [], "p"), ("unit-resolution", [2, 1], "false"),
        ])
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "undischarged hypotheses"):
            proof_to_lean.reconstruct(LITERAL, certificate)

    def test_hypotheses_propagate_even_through_unused_congruence_evidence(self):
        source = "(declare-const p Bool)(declare-const q Bool)"
        source += "(assert p)(assert (not p))(assert (= q q))"
        certificate = make_certificate(source, [
            ("hypothesis", [], "(= q q)"),
            ("monotonicity", [3], "(= (not p) (not p))"),
            ("mp", [1, 4], "(not p)"),
            ("unit-resolution", [0, 5], "false"),
        ])
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "undischarged hypotheses"):
            proof_to_lean.reconstruct(source, certificate)

    def test_lemma_requires_false_even_when_unused(self):
        source = LITERAL + "(assert false)"
        certificate = make_certificate(source, [
            ("lemma", [0], "(not p)"), ("asserted", [], "false"),
        ])
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "lemma requires a proof of false"):
            proof_to_lean.reconstruct(source, certificate)

    def test_lemma_must_discharge_all_hypotheses_even_when_unused(self):
        source = "(declare-const p Bool)(declare-const q Bool)"
        source += "(assert (or (not p) (not q)))(assert false)"
        for conclusion in ["(not p)", "(not q)", "(or p q)", "false"]:
            with self.subTest(conclusion=conclusion):
                certificate = make_certificate(source, [
                    ("hypothesis", [], "p"), ("hypothesis", [], "q"),
                    ("unit-resolution", [0, 2, 3], "false"),
                    ("lemma", [4], conclusion), ("asserted", [], "false"),
                ])
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "discharge every hypothesis"):
                    proof_to_lean.reconstruct(source, certificate)

    def test_scope_errors_never_replace_an_artifact(self):
        source = "(declare-const p Bool)(assert p)"
        certificate = make_certificate(source, [
            ("hypothesis", [], "(not p)"), ("unit-resolution", [0, 1], "false"),
        ])
        with tempfile.TemporaryDirectory() as directory, \
                patch.object(proof_to_lean.subprocess, "run") as checker:
            output = Path(directory) / "proof.lean"
            output.write_text("previous artifact")
            with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "undischarged hypotheses"):
                proof_to_lean.check_and_write(source, certificate, output)
            checker.assert_not_called()
            self.assertEqual(output.read_text(), "previous artifact")
            self.assertEqual(list(Path(directory).iterdir()), [output])

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
