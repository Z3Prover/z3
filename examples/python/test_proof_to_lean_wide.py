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
import re
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

_EXAMPLES = Path(__file__).resolve().parent
sys.path.insert(0, str(_EXAMPLES))
import proof_certificate
import proof_clause_log
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
# Outlined, the proof steps project the assertions out of one conjunction;
# at this many assertions a right-nested conjunction exhausts maxHeartbeats
# (isDefEq on the chain of 600 projections), a balanced one checks in 20 s.
OUTLINED_WIDTH = 600
# Below _OUTLINE_PROOF_STEPS proof steps when every operand is eliminated
# (three per operand), so the steps are checked in the theorem itself.
INLINE_CHAIN_WIDTH = 150
# Its middle operand, the one refuted, lies past the first tail.
LOCAL_TAIL_WIDTH = 80


def wide_conjunction(width):
    """(and p0 ... p(n-1)) refuted by the negation of its middle operand."""
    source = "".join("(declare-const p%d Bool)\n" % index for index in range(width))
    source += "(assert (and %s))\n" % " ".join("p%d" % index for index in range(width))
    source += "(assert (not p%d))\n(check-sat)\n" % (width // 2)
    return source


def implication_chain_conjunction(width):
    """(and p0 (=> p0 p1) ... (not p(n-2))): the refutation eliminates every operand."""
    source = "".join("(declare-const p%d Bool)\n" % index for index in range(width - 1))
    operands = ["p0"] + ["(=> p%d p%d)" % (index, index + 1) for index in range(width - 2)]
    source += "(assert (and %s (not p%d)))\n(check-sat)\n" % (" ".join(operands), width - 2)
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

    def test_outlined_wide_disjunction_projects_each_assertion_at_logarithmic_depth(self):
        # Outlined, every proof step receives the assertions as one
        # conjunction, Inputs, and projects assertion k by field notation.
        # Right-nested, the last of the 601 assertions sat under 600
        # projections and elaborating the chain exhausted maxHeartbeats (as
        # it did for z3test's QF_LIA BART-PT-002/RF-00.smt2, 1,211
        # assertions); balanced, no assertion is more than ten deep.
        source = wide_disjunction(OUTLINED_WIDTH)
        with patch.object(proof_to_lean, "_OUTLINE_PROOF_STEPS", 0):
            certificate, axioms = self.check(source, "legacy", "propositional", OUTLINED_WIDTH)
            text = proof_to_lean.reconstruct(source, certificate)
        self.assertEqual(axioms, set())
        self.assertIn("private def Inputs", text)
        paths = re.findall(r"_inputs((?:\.[12])+)", text)
        self.assertEqual(len(set(paths)), OUTLINED_WIDTH + 1)
        self.assertEqual(max(path.count(".") for path in paths), OUTLINED_WIDTH.bit_length())

    def check_every_operand_eliminated(self, width, outlined):
        source = implication_chain_conjunction(width)
        certificate, axioms = self.check(source, "legacy", "propositional", width)
        self.assertEqual(certificate["rule_counts"]["and-elim"], width)
        self.assertEqual(axioms, set())
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertEqual("private def Inputs" in text, outlined)
        # No projection starts more than a stride of operands before its own:
        # a tail is a stride past the one before, and an operand at most a
        # stride minus one past its tail.
        stride = proof_to_lean._AND_ELIM_STRIDE
        tails = re.findall(r"let _tail_\d+_\d+ := _(?:step_\d+|tail_\d+_\d+)((?:\.2)*)\n", text)
        self.assertEqual({path.count(".") for path in tails}, {stride})
        projections = re.findall(r"\n    _(?:step_\d+|tail_\d+_\d+)((?:\.2)*)\.1\n", text)
        self.assertEqual(len(projections), width - 1)
        self.assertEqual(max(path.count(".") for path in projections), stride - 1)
        return text

    def test_outlined_conjunction_with_every_operand_eliminated_is_checked(self):
        # Each operand was projected from the start of the conjunction, one
        # `.2` per operand before it: an outlined lemma eliminating 250 of
        # 600 operands held 94,000 projections and exhausted maxHeartbeats.
        # Now every lemma binds the rest of the conjunction once per 32
        # operands and projects from the nearest of those tails.
        text = self.check_every_operand_eliminated(OUTLINED_WIDTH, outlined=True)
        self.assertGreater(text.count("let _tail_"), OUTLINED_WIDTH // proof_to_lean._AND_ELIM_STRIDE)

    def test_inline_conjunction_with_every_operand_eliminated_is_checked(self):
        text = self.check_every_operand_eliminated(INLINE_CHAIN_WIDTH, outlined=False)
        self.assertEqual(text.count("let _tail_"), (INLINE_CHAIN_WIDTH - 1) // proof_to_lean._AND_ELIM_STRIDE)

    def test_outlined_lemma_binds_tails_after_a_local_premise(self):
        # A conjunction eliminated once is used once, so its proof is a step
        # of the lemma that eliminates from it rather than a lemma of its
        # own: the tails follow that step inside the lemma.
        source = wide_conjunction(LOCAL_TAIL_WIDTH)
        with patch.object(proof_to_lean, "_OUTLINE_PROOF_STEPS", 0):
            certificate, axioms = self.check(source, "legacy", "propositional", LOCAL_TAIL_WIDTH)
            text = proof_to_lean.reconstruct(source, certificate)
        self.assertEqual(certificate["rule_counts"]["and-elim"], 1)
        self.assertEqual(axioms, set())
        self.assertIn("private def Inputs", text)
        tail = re.search(r"\n  let _tail_(\d+)_32 := _step_\1(?:\.2){32}\n", text)
        self.assertIsNotNone(tail)
        premise = tail.group(1)
        self.assertNotIn("proof_step_%s " % premise, text)
        self.assertLess(text.index("\n  let _step_%s : " % premise), tail.start())
        self.assertIn("\n    _tail_%s_32%s.1\n" % (premise, ".2" * (LOCAL_TAIL_WIDTH // 2 - 32)), text)


@unittest.skipUnless(_z3_available(), "the z3 executable is required for the clause log")
class TestWidePropositionalClauseLog(_WideLeanIntegration):
    """The sat.smt clause log: the replay's theory lemmas and resolution chains over wide clauses."""

    def test_wide_conjunction_is_checked(self):
        # The core splits the conjunction into its conjuncts, and the replay ties
        # them to the assertion by and-elim steps and a th-lemma over the whole
        # conjunction; grind fails on that lemma today.
        source = wide_conjunction(CLAUSE_LOG_CONJUNCTION_WIDTH)
        with patch.object(proof_clause_log, "_TRIM_THRESHOLD", float("inf")):
            certificate, axioms = self.check(source, "clause-log", "propositional", CLAUSE_LOG_CONJUNCTION_WIDTH)
        self.assertEqual(certificate["rule_counts"]["and-elim"], CLAUSE_LOG_CONJUNCTION_WIDTH - 1)
        self.assertLessEqual(axioms, _STANDARD_AXIOMS)
        # Trimmed, the default since 2026-10-27, the core is the empty clause
        # Z3 assumes once preprocessing reduces the conjunction against the
        # unit to false (until then the trimmer wrote a cyclic core for it).
        certificate, axioms = self.check(source, "clause-log", "propositional", CLAUSE_LOG_CONJUNCTION_WIDTH)
        self.assertNotIn("and-elim", certificate["rule_counts"])
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
