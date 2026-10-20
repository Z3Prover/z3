############################################
# Copyright (c) 2026 Microsoft Corporation
#
# End-to-end tests for wide n-ary Boolean connectives: certificates through
# both cores, Lean reconstruction, and kernel checks with the pinned Lean
# toolchain. SMT-LIB benchmarks routinely assert conjunctions and
# disjunctions over hundreds of operands (for example the QF_UF benchmark
# NEQ004_size4 in z3test's smtlib-sample asserts one conjunction of 338
# literals); every operand count Z3 solves must be certified, not only the
# small ones.
############################################
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

_EXAMPLES = Path(__file__).resolve().parent
sys.path.insert(0, str(_EXAMPLES))
import proof_certificate
import proof_to_lean
from test_proof_to_lean_uf import _z3_available

_STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
# Above Lean's default maxRecDepth (512) for the right-nested And/Or chain a
# connective of this many operands renders to; each case below is solved by
# Z3 in milliseconds.
WIDTH = 260
# The clause log eliminates every conjunct of an asserted conjunction, so its
# Lean check is the most expensive; this width is already rejected today.
CLAUSE_LOG_CONJUNCTION_WIDTH = 200


def wide_conjunction(width):
    """(and p0 ... p(n-1)) refuted by the negation of its middle operand."""
    source = "".join("(declare-const p%d Bool)\n" % index for index in range(width))
    source += "(assert (and %s))\n" % " ".join("p%d" % index for index in range(width))
    source += "(assert (not p%d))\n(check-sat)\n" % (width // 2)
    return source


def wide_disjunction(width):
    """(or p0 ... p(n-1)) refuted by one negated unit per operand."""
    source = "".join("(declare-const p%d Bool)\n" % index for index in range(width))
    source += "(assert (or %s))\n" % " ".join("p%d" % index for index in range(width))
    source += "".join("(assert (not p%d))\n" % index for index in range(width))
    return source + "(check-sat)\n"


def wide_uf_conjunction(width):
    """A conjunction of predicate applications over an uninterpreted sort, as in NEQ004_size4."""
    source = "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-fun P (U) Bool)\n"
    source += "".join("(declare-const a%d U)\n" % index for index in range(width))
    source += "(assert (and %s))\n" % " ".join("(P a%d)" % index for index in range(width))
    source += "(assert (not (P a%d)))\n(check-sat)\n" % (width // 2)
    return source


def wide_uf_disjunction(width):
    """A disjunction of equalities over an uninterpreted sort, each refuted by a unit disequality."""
    source = "(set-logic QF_UF)\n(declare-sort U 0)\n"
    source += "".join("(declare-const a%d U)\n(declare-const b%d U)\n" % (index, index) for index in range(width))
    source += "(assert (or %s))\n" % " ".join("(= a%d b%d)" % (index, index) for index in range(width))
    source += "".join("(assert (not (= a%d b%d)))\n" % (index, index) for index in range(width))
    return source + "(check-sat)\n"


class _WideLeanIntegration(unittest.TestCase):
    def export(self, source, core):
        if core == "legacy":
            return proof_certificate.export_certificate(source)
        return proof_certificate.export_clause_log_certificate(source)

    def check(self, source, core, fragment, width=WIDTH):
        """Export, publish only after Lean accepts, and return (certificate, axioms of unsat)."""
        certificate = self.export(source, core)
        self.assertEqual(certificate["fragment"], fragment)
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "checked.lean"
            try:
                proof_to_lean.check_and_write(source, certificate, output)
            except subprocess.CalledProcessError as error:
                errors = [line for line in (error.stdout + error.stderr).splitlines() if "error" in line]
                raise self.failureException("Lean rejected the %s certificate of a %d-operand connective:\n%s"
                                            % (core, width, "\n".join(errors[:5]))) from None
            text = output.read_text()
            statement = text.split("theorem unsat", 1)[1].split(": False :=", 1)[0]
            self.assertEqual(statement.count("    (_h"), len(certificate["assertions"]))
            self.assertNotIn("_hyp", statement)
            namespace = "Z3Proofs.NativeCertificate.p" + hashlib.sha256(source.encode()).hexdigest()
            output.write_text(text + "\n#print axioms %s.unsat\n" % namespace)
            result = subprocess.run([str(proof_to_lean._CHECK_LEAN), str(output)],
                                    text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        report = " ".join(result.stdout.split())
        if ".unsat' does not depend on any axioms" in report:
            return certificate, set()
        axioms = report.split("depends on axioms: [", 1)[1].split("]", 1)[0]
        return certificate, {name.strip() for name in axioms.split(",")}


class TestWidePropositionalLegacyCore(_WideLeanIntegration):
    """The legacy proof object: propositional refutations stay axiom-free at any width."""

    def test_wide_conjunction_is_checked_without_axioms(self):
        certificate, axioms = self.check(wide_conjunction(WIDTH), "legacy", "propositional")
        self.assertIn("and-elim", certificate["rule_counts"])
        self.assertEqual(axioms, set())

    def test_wide_disjunction_is_checked_without_axioms(self):
        certificate, axioms = self.check(wide_disjunction(WIDTH), "legacy", "propositional")
        self.assertEqual(certificate["rule_counts"]["asserted"], WIDTH + 1)
        self.assertEqual(axioms, set())


@unittest.skipUnless(_z3_available(), "the z3 executable is required for the clause log")
class TestWidePropositionalClauseLog(_WideLeanIntegration):
    """The sat.smt clause log: the replay's theory lemmas and resolution chains over wide clauses."""

    def test_wide_conjunction_is_checked(self):
        # The core splits the conjunction into its conjuncts, and the replay ties
        # them to the assertion by and-elim steps and a th-lemma over the whole
        # conjunction; grind fails on that lemma today.
        certificate, axioms = self.check(wide_conjunction(CLAUSE_LOG_CONJUNCTION_WIDTH), "clause-log",
                                         "propositional", CLAUSE_LOG_CONJUNCTION_WIDTH)
        self.assertEqual(certificate["rule_counts"]["and-elim"], CLAUSE_LOG_CONJUNCTION_WIDTH - 1)
        self.assertLessEqual(axioms, _STANDARD_AXIOMS)

    def test_wide_disjunction_is_checked(self):
        certificate, axioms = self.check(wide_disjunction(WIDTH), "clause-log", "propositional")
        self.assertEqual(certificate["rule_counts"]["asserted"], WIDTH + 1)
        self.assertLessEqual(axioms, _STANDARD_AXIOMS)


class TestWideUninterpretedLegacyCore(_WideLeanIntegration):
    def test_wide_predicate_conjunction_is_checked(self):
        certificate, axioms = self.check(wide_uf_conjunction(WIDTH), "legacy", "qf_uf")
        self.assertIn("and-elim", certificate["rule_counts"])
        self.assertLessEqual(axioms, _STANDARD_AXIOMS)


@unittest.skipUnless(_z3_available(), "the z3 executable is required for the clause log")
class TestWideUninterpretedClauseLog(_WideLeanIntegration):
    def test_wide_equality_disjunction_is_checked(self):
        certificate, axioms = self.check(wide_uf_disjunction(WIDTH), "clause-log", "qf_uf")
        self.assertEqual(certificate["rule_counts"]["asserted"], WIDTH + 1)
        self.assertLessEqual(axioms, _STANDARD_AXIOMS)


if __name__ == "__main__":
    unittest.main()
