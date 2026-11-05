############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Tests for pseudo-Boolean constraints in the Lean reconstruction:
# at-most, at-least, pble, pbge, and pbeq over Boolean variables and their
# negations, in propositional input through the legacy proof object.
# Lean values each literal 0 or 1 over Int and proves theory_pb's th-lemma
# pb steps and the pseudo-Boolean rewrites with omega. Validation without
# Lean, the validity of theory_pb's lemmas on their own (checked by z3),
# and end-to-end checks that need the pinned Lean toolchain.
############################################
import copy
import hashlib
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import unittest

import z3

_EXAMPLES = Path(__file__).resolve().parent
sys.path.insert(0, str(_EXAMPLES))
import proof_certificate
import proof_to_lean
from test_proof_to_lean_lia import _STANDARD_AXIOMS

PB_INPUTS = {
    # At most one of three, yet every pair has a true member.
    "pb_at_most_pairs": """(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(assert ((_ at-most 1) a b c))
(assert (or a b))
(assert (or b c))
(assert (or a c))
(check-sat)
""",
    # No subset of {7, 3, 4, 3} sums to 5 (z3test regressions/smt2/pb.smt2).
    "pb_eq_no_subset": """(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(declare-const d Bool)
(assert ((_ pbeq 5 7 3 4 3) a b c d))
(check-sat)
""",
    # Weighted bounds both ways, a cardinality bound, and a clause.
    "pb_weighted_mix": """(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(declare-const d Bool)
(declare-const e Bool)
(assert ((_ pble 6 2 3 4 5 2) a b c d e))
(assert ((_ pbge 7 1 2 3 4 5) a b c d e))
(assert (or (not a) (not e)))
(assert ((_ at-least 2) a b c d))
(check-sat)
""",
    # The pble 0 assertion fixes p1, p2, and p4 false at the base level
    # before the pbge constraints are internalized. theory_pb used to fold
    # those values into the bound and then state (not (pbge 7 ...)) as an
    # axiom without them, which does not hold on its own.
    "pb_base_level_assignment": """(declare-const p0 Bool)
(declare-const p1 Bool)
(declare-const p2 Bool)
(declare-const p3 Bool)
(declare-const p4 Bool)
(assert ((_ at-least 0) p3 (not p3) p0 (not p2)))
(assert ((_ pble 0 1 2 7 5) p2 p1 p4 p1))
(assert ((_ pbeq 1 6 2 5 3 5) p3 p2 p2 p3 p2))
(assert ((_ pbge 7 4 1 2 6) p0 p0 p1 p2))
(assert ((_ pbge 1 6 7) p3 (not p3)))
(check-sat)
""",
    # Negative coefficients and bounds, as the API writes PbLe and PbGe with
    # them: 2c + d >= 1 + 3a rules a out, then 3b + 2d <= c - 1 rules out b
    # and d, which the clause needs.
    "pb_negative_coefficients": """(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(declare-const d Bool)
(assert ((_ pble -1 -2 3 -1 2) a b c d))
(assert ((_ pbge 1 -3 2 1) a c d))
(assert (or b d))
(check-sat)
""",
}

# Seeds of random_pseudo_boolean_instance(seed, 16, 9) whose refutations
# Lean checks: 1028 needs a conflict on a cardinality constraint, which
# theory_pb used to resolve into a propagation citing one of the
# constraints the resolvent came from, a th-lemma that does not hold on its
# own. 1051 and 1050 split a conjunction the rewriter makes of a
# constraint, and 1050 rewrites below it (monotonicity, trans).
PB_SEEDS = (1028, 1051, 1050)


def random_pseudo_boolean_instance(seed, variables=5, constraints=5):
    """A random mix of pseudo-Boolean constraints and clauses over Boolean variables (possibly satisfiable)."""
    generator = random.Random(seed)
    names = ["p%d" % i for i in range(variables)]
    lines = ["(declare-const %s Bool)" % name for name in names]

    def literal():
        name = generator.choice(names)
        return "(not %s)" % name if generator.random() < 0.3 else name

    for _ in range(constraints):
        width = generator.randint(2, variables)
        arguments = [literal() for _ in range(width)]
        kind = generator.choice(["at-most", "at-least", "pble", "pbge", "pbeq", "clause"])
        if kind == "clause":
            lines.append("(assert (or %s))" % " ".join(arguments[:3]))
        elif kind in ("at-most", "at-least"):
            lines.append("(assert ((_ %s %d) %s))" % (kind, generator.randint(0, width), " ".join(arguments)))
        else:
            coefficients = [generator.randint(1, 7) for _ in arguments]
            lines.append("(assert ((_ %s %d %s) %s))" % (
                kind, generator.randint(0, sum(coefficients)), " ".join(map(str, coefficients)),
                " ".join(arguments)))
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


def pigeonhole_instance(holes):
    """holes + 1 pigeons, each in at least one hole, each hole holding at most one: unsatisfiable."""
    pigeons = holes + 1
    lines = ["(declare-const p%d_%d Bool)" % (i, j) for i in range(pigeons) for j in range(holes)]
    for i in range(pigeons):
        lines.append("(assert ((_ at-least 1) %s))" % " ".join("p%d_%d" % (i, j) for j in range(holes)))
    for j in range(holes):
        lines.append("(assert ((_ at-most 1) %s))" % " ".join("p%d_%d" % (i, j) for i in range(pigeons)))
    return "\n".join(lines) + "\n(check-sat)\n"


def _pb_lemma_failures(source):
    """The th-lemma pb steps of the legacy proof that z3 finds do not follow from their premises."""
    context = z3.Context(proof=True)
    solver = z3.Solver(ctx=context)
    solver.set("combined_solver.ignore_solver1", True)
    solver.add(proof_certificate.parse_legacy_assertions(source, context)[0])
    if solver.check() != z3.unsat:
        raise AssertionError("the input is not unsatisfiable")
    failures, lemmas, seen, pending = [], 0, set(), [solver.proof()]
    while pending:
        step = pending.pop()
        if step.get_id() in seen:
            continue
        seen.add(step.get_id())
        children = step.children()
        pending.extend(children[:-1])
        if step.decl().kind() == z3.Z3_OP_PR_TH_LEMMA and step.decl().params() == ["pb"]:
            lemmas += 1
            check = z3.Solver(ctx=context)
            check.add([premise.arg(premise.num_args() - 1) for premise in children[:-1]] + [z3.Not(children[-1])])
            if check.check() != z3.unsat:
                failures.append(str(step))
    return lemmas, failures


class TestPseudoBooleanValidation(unittest.TestCase):
    """Fragment checks, rendering, and certificate tampering, without Lean."""

    source = PB_INPUTS["pb_at_most_pairs"]

    def test_pseudo_boolean_constraints_are_propositional(self):
        for name, source in PB_INPUTS.items():
            with self.subTest(name=name):
                _, fragment = proof_certificate.parse_assertions(source, z3.Context())
                self.assertEqual(fragment, "propositional")

    def test_unsupported_pseudo_boolean_inputs_are_rejected(self):
        cases = {
            "(declare-const a Bool)(declare-const b Bool)(assert ((_ at-most 1) (and a b) a))":
                "pseudo-Boolean arguments must be Boolean variables",
            "(declare-const a Bool)(declare-const x Int)(assert ((_ at-most 1) a (> x 0)))":
                "pseudo-Boolean arguments must be Boolean variables",
            # The legacy core would rewrite (not (not a)) inside the constraint by congruence.
            "(declare-const a Bool)(declare-const b Bool)(assert ((_ at-least 2) (not (not a)) b))(assert (not a))":
                "pseudo-Boolean arguments must be Boolean variables",
            "(declare-const a Bool)(declare-const x Int)(assert ((_ at-most 1) a))(assert (> x 0))":
                "propositional input only",
        }
        for source, message in cases.items():
            with self.subTest(source=source):
                with self.assertRaisesRegex(proof_certificate.ProofExportError, message):
                    proof_certificate.parse_assertions(source + "(check-sat)", z3.Context(), integer=True)

    def test_clause_log_rejects_pseudo_boolean_constraints(self):
        # The sat.smt core compiles them away before its log starts.
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "legacy proof object only"):
            proof_certificate.export_clause_log_certificate(self.source)

    def test_constraints_keep_their_parameters_and_render_as_int_sums(self):
        certificate = proof_certificate.export_certificate(PB_INPUTS["pb_weighted_mix"])
        constraints = {declaration["name"]: declaration["parameters"]
                       for declaration in certificate["declarations"] if declaration["kind"] in proof_to_lean._PSEUDO_BOOLEAN}
        self.assertIn(["2"], constraints.values())  # (at-least 2 ...) keeps its bound alone
        self.assertTrue(any(len(parameters) == 6 for parameters in constraints.values()))
        hints = {tuple(declaration["parameters"]) for declaration in certificate["declarations"]
                 if declaration["name"] == "th-lemma"}
        self.assertEqual(hints, {("pb",)})
        text = proof_to_lean.reconstruct(PB_INPUTS["pb_weighted_mix"], certificate)
        self.assertIn("private theorem _pb_bit", text)
        self.assertIn("((2 : Int)) * (@ite Int (formula_", text)
        self.assertIn("private theorem th_lemma_", text)
        self.assertIn("generalize (@ite Int (_atoms 0) (Classical.propDecidable (_atoms 0)) 1 0) = _x0", text)

    def test_tampered_constraints_are_rejected(self):
        certificate = proof_certificate.export_certificate(self.source)
        position = next(index for index, declaration in enumerate(certificate["declarations"])
                        if declaration["name"] == "at-most")
        cases = {
            # A weaker bound is another constraint than the input's.
            "2": "certificate assertions do not match the original input",
            "one": "pseudo-Boolean parameters must be integers",
            "1/2": "pseudo-Boolean parameters must be integers",
        }
        for bound, message in cases.items():
            with self.subTest(bound=bound):
                tampered = copy.deepcopy(certificate)
                tampered["declarations"][position]["parameters"] = [bound]
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, message):
                    proof_to_lean.reconstruct(self.source, tampered)
        tampered = copy.deepcopy(certificate)
        tampered["declarations"][position]["parameters"] = ["1", "1", "1", "1"]
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "invalid pseudo-Boolean declaration"):
            proof_to_lean.reconstruct(self.source, tampered)
        tampered = copy.deepcopy(certificate)
        tampered["fragment"] = "qf_uf"
        with self.assertRaises(proof_to_lean.ReconstructionError):
            proof_to_lean.reconstruct(self.source, tampered)

    def test_theory_pb_lemmas_hold_on_their_own(self):
        # Two theory_pb proof defects, fixed in theory_pb.cpp: folding
        # base-level values into a constraint's bound, and resolving a
        # cardinality conflict into a propagation that cites only one of
        # the resolved constraints.
        sources = [PB_INPUTS["pb_base_level_assignment"], random_pseudo_boolean_instance(1028, 16, 9),
                   pigeonhole_instance(4)]
        for source in sources:
            lemmas, failures = _pb_lemma_failures(source)
            self.assertGreater(lemmas, 0)
            self.assertEqual(failures, [])


def _check_in_lean(test, source):
    """Export on the legacy core, reconstruct, and kernel-check; return the certificate."""
    certificate = proof_certificate.export_certificate(source, timeout=60)
    test.assertEqual(certificate["fragment"], "propositional")
    test.assertIn("th-lemma", certificate["rule_counts"])
    with tempfile.TemporaryDirectory() as directory:
        output = Path(directory) / "checked.lean"
        proof_to_lean.check_and_write(source, certificate, output)
        namespace = "Z3Proofs.NativeCertificate.p" + hashlib.sha256(source.encode()).hexdigest()
        output.write_text(output.read_text() + "\n#print axioms %s.unsat\n" % namespace)
        result = subprocess.run([str(proof_to_lean._CHECK_LEAN), str(output)], text=True, capture_output=True)
        test.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        report = " ".join(result.stdout.split())
        test.assertTrue(_STANDARD_AXIOMS in report or "does not depend on any axioms" in report, report)
    return certificate


class TestPseudoBooleanLeanIntegration(unittest.TestCase):
    """End-to-end: legacy proof object, certificate, Lean reconstruction, kernel check."""

    def test_documented_pb_inputs_verify(self):
        for name, source in PB_INPUTS.items():
            with self.subTest(name=name):
                _check_in_lean(self, source)

    def test_pinned_random_instances_verify(self):
        for seed in PB_SEEDS:
            with self.subTest(seed=seed):
                _check_in_lean(self, random_pseudo_boolean_instance(seed, 16, 9))

    def test_pigeonhole_verifies(self):
        certificate = _check_in_lean(self, pigeonhole_instance(4))
        self.assertGreater(certificate["rule_counts"]["th-lemma"], 100)

    def test_z3test_pb_queries_verify(self):
        # The incremental z3test file's two unsatisfiable queries (pbeq), one per
        # half of the script, after a reset), here the first half: one query
        # per scope.
        source = "".join(
            "(push)(assert ((_ %s) a b c d))(check-sat)(pop)" % constraint
            for constraint in ("at-most 2", "at-least 3", "pbeq 5 7 3 4 3", "pbge 6 7 3 4 3"))
        source = "(set-logic QF_FD)(declare-const a Bool)(declare-const b Bool)(declare-const c Bool)" \
                 "(declare-const d Bool)" + source
        for query, satisfiable in enumerate((True, True, False, True)):
            with self.subTest(query=query):
                if satisfiable:
                    with self.assertRaisesRegex(proof_certificate.ProofExportError, "^sat: no unsat proof exists$"):
                        proof_certificate.export_certificate(source, query=query)
                    continue
                certificate = proof_certificate.export_certificate(source, query=query)
                with tempfile.TemporaryDirectory() as directory:
                    proof_to_lean.check_and_write(source, certificate, Path(directory) / "checked.lean")


if __name__ == "__main__":
    unittest.main()
