############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Tests for deeply nested inputs: the exporter and the reconstructor walk
# formulas and proof searches on explicit stacks, so nesting deeper than
# Python's recursion limit is certified like any other input. Translated
# benchmarks nest connectives a thousand levels deep: z3test's QF_IDL
# FISCHER6-4-ninc (a CVC Lite translation) asserts conjunctions of the form
# (and a (and b (and c ...))) nested a thousand levels, and the cnf lemma of
# QF_LRA tta_startup/simple_startup_11nodes searches through a thousand nested
# case splits; both failed with RecursionError.
############################################
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile
import traceback
import unittest

import z3

_EXAMPLES = Path(__file__).resolve().parent
sys.path.insert(0, str(_EXAMPLES))
import proof_certificate
import proof_clause_log
import proof_to_lean
from test_proof_to_lean_uf import _z3_available

# Above Python's default recursion limit (1000), so every walk that recursed
# once per nesting level failed on these inputs.
DEPTH = 1100


def _nested_and(operands):
    """Right-nested binary conjunctions, as CVC Lite translations write them."""
    body = operands[-1]
    for operand in reversed(operands[:-1]):
        body = "(and %s %s)" % (operand, body)
    return body


def deep_implication_chain(depth):
    """p0, p0 => p1, ..., and not pn, asserted as one conjunction nested depth levels deep."""
    source = "(set-logic QF_UF)\n"
    source += "".join("(declare-const p%d Bool)\n" % index for index in range(depth + 1))
    operands = ["p0"] + ["(=> p%d p%d)" % (index, index + 1) for index in range(depth)] + ["(not p%d)" % depth]
    return source + "(assert %s)\n(check-sat)\n" % _nested_and(operands)


def deep_bounds_conjunction(depth):
    """Bounds x0 < 5, ..., and the contradictory x < y and y < x innermost, in one nested conjunction."""
    source = "(set-logic QF_LRA)\n(declare-const x Real)\n(declare-const y Real)\n"
    source += "".join("(declare-const x%d Real)\n" % index for index in range(depth))
    operands = ["(< x%d 5.0)" % index for index in range(depth)] + ["(< x y)", "(< y x)"]
    return source + "(assert %s)\n(check-sat)\n" % _nested_and(operands)


def deep_case_split_facts(depth, closed=True):
    """Facts a refutation of (or a0 b0) can only reach through depth nested case splits.

    For every i, (or ai bi), bi => ci and bi => (not ci): no assignment makes
    bi true, but propagation alone never sees it, so the prover splits on
    the disjunction; the bi case closes at once and the ai case goes on to
    the next disjunction. With closed, the facts also deny the right-nested
    conjunction of all ai, which the deepest case contradicts; without, the
    search reaches a satisfying assignment after as many splits.
    """
    a, b, c = ([("atom", 3 * index + offset) for index in range(depth)] for offset in range(3))
    facts = [("or", a[index], b[index]) for index in range(1, depth)]
    facts += [("implies", b[index], c[index]) for index in range(depth)]
    facts += [("implies", b[index], ("not", c[index])) for index in range(depth)]
    if closed:
        conjunction = a[-1]
        for atom in reversed(a[:-1]):
            conjunction = ("and", atom, conjunction)
        facts.append(("not", conjunction))
    return ("or", a[0], b[0]), facts


class TestDeepFormulaWalks(unittest.TestCase):
    def test_conjuncts_are_listed_parents_first(self):
        p, q, r = z3.Bools("p q r")
        inner = z3.And(q, r)
        outer = z3.And(p, inner)
        listed = [(conjunct.sexpr(), [step.sexpr() for step in path])
                  for conjunct, path in proof_clause_log._conjuncts(outer)]
        self.assertEqual(listed, [(outer.sexpr(), []), ("p", ["p"]), (inner.sexpr(), [inner.sexpr()]),
                                  ("q", [inner.sexpr(), "q"]), ("r", [inner.sexpr(), "r"])])
        deep = z3.BoolVal(True)
        for index in range(DEPTH):
            deep = z3.And(z3.Bool("p%d" % index), deep)
        self.assertEqual(len(list(proof_clause_log._conjuncts(deep))), 2 * DEPTH + 1)

    def test_normalizer_keys_deep_formulas_and_defers_errors(self):
        normalizer = proof_clause_log._Normalizer()
        atoms = [z3.Bool("p%d" % index) for index in range(DEPTH)]
        deep = z3.BoolVal(True)
        for atom in atoms:
            deep = z3.And(atom, deep)
        self.assertEqual(normalizer.forms[normalizer.key(deep)],
                         ("and", tuple(sorted(normalizer.key(atom) for atom in atoms))))
        # The subformulas are keyed before their parent, but an error is
        # raised only when the parent's form asks for the subformula: a
        # conjunction stops at a false conjunct.
        x, y = z3.Reals("x y")
        nonlinear = x * y > 0
        self.assertEqual(normalizer.forms[normalizer.key(z3.And(z3.BoolVal(False), nonlinear))], ("false",))
        for formula in (z3.And(x > 0, nonlinear), z3.Not(z3.Or(nonlinear, x > 0)), nonlinear):
            with self.assertRaisesRegex(proof_certificate.ProofExportError, "nonlinear"):
                normalizer.key(formula)
        # Every failing ancestor raises the same error again, from the
        # traceback where it was first caught rather than gathering their frames.
        for atom in atoms:
            nonlinear = z3.And(atom, nonlinear)
        try:  # not assertRaises, which drops the traceback
            normalizer.key(nonlinear)
        except proof_certificate.ProofExportError as error:
            self.assertIn("nonlinear", str(error))
            self.assertLess(len(traceback.extract_tb(error.__traceback__)), 50)
        else:
            self.fail("the nonlinear conjunct was not reported")


class TestDeepCaseSplits(unittest.TestCase):
    def prove(self, closed):
        structure, facts = deep_case_split_facts(DEPTH, closed)
        prover = proof_to_lean._PropositionalProver(structure, *facts, classical=True)
        named = [(fact, "_h%d" % index) for index, fact in enumerate(facts)]
        return structure, named, prover.refutation(structure, named)

    def test_satisfiable_facts_are_not_refuted_after_deep_search(self):
        # The search goes through more nested splits than Python's recursion
        # limit allows and ends in a satisfying assignment: no proof, as for
        # the tta_startup cnf lemma, whose grind fallback then takes over.
        self.assertIsNone(self.prove(closed=False)[2])

    def test_deeply_nested_case_splits_are_checked(self):
        structure, named, lines = self.prove(closed=True)
        self.assertIsNotNone(lines)
        # One bullet level per split: the deepest line is indented DEPTH - 1 times.
        self.assertEqual(max(len(line) - len(line.lstrip("· ")) for line in lines) // 2, DEPTH - 1)
        source = ["set_option maxRecDepth 100000", "",
                  "theorem deep_case_splits (_atoms : Nat -> Prop)"]
        source += ["    (%s : %s)" % (name, proof_to_lean._render_structure(fact)) for fact, name in named]
        source += ["    : Not %s := by" % proof_to_lean._render_structure(structure)]
        source += ["  " + line for line in lines]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "deep.lean"
            path.write_text("\n".join(source) + "\n")
            result = subprocess.run([str(proof_to_lean._CHECK_LEAN), str(path)], text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, (result.stdout + result.stderr)[-3000:])


class _LeanChecked(unittest.TestCase):
    def check_lean(self, source, certificate):
        """Check the certificate with Lean and return the Lean text."""
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "checked.lean"
            try:
                proof_to_lean.check_and_write(source, certificate, output)
            except subprocess.CalledProcessError as error:
                errors = [line for line in (error.stdout + error.stderr).splitlines() if "error" in line]
                raise self.failureException("Lean rejected the certificate:\n%s" % "\n".join(errors[:5])) from None
            text = output.read_text()
        namespace = "Z3Proofs.NativeCertificate.p" + hashlib.sha256(source.encode()).hexdigest()
        self.assertIn("namespace " + namespace, text)
        return text


@unittest.skipUnless(_z3_available(), "the z3 executable is required for the clause log")
class TestDeepClauseLog(_LeanChecked):
    def check(self, source, fragment):
        certificate = proof_certificate.export_clause_log_certificate(source)
        self.assertEqual(certificate["fragment"], fragment)
        self.check_lean(source, certificate)
        return certificate

    def test_deep_conjunction_is_checked(self):
        # The assumption sources (and-elim paths through the nested
        # conjunction), the canonical keys matching assumed clauses to them,
        # and the Boolean structure of the cnf lemma tying the empty clause
        # to the assertion all read the conjunction a level at a time.
        self.check(deep_implication_chain(DEPTH), "propositional")

    def test_deep_arithmetic_conjunction_is_checked(self):
        # The canonical keys of the nested conjunction over arithmetic atoms;
        # each bound and the two contradictory atoms are and-eliminated
        # through the levels above them.
        certificate = self.check(deep_bounds_conjunction(DEPTH), "qf_lra")
        self.assertEqual(certificate["rule_counts"]["and-elim"], DEPTH + 2)


class TestDeepLegacyCore(_LeanChecked):
    def test_deep_arithmetic_rewrite_is_checked(self):
        # The legacy core rewrites the nested conjunction into one flat
        # conjunction over the normalized arithmetic atoms (_normalized_rewrite);
        # the rewrite's Boolean structure is read and rendered without
        # recursion, and the prover settles the flat conjunction without
        # rebuilding every projection whenever one operand is assigned (two
        # minutes before at 1,200 operands, a second now). Each atom is
        # normalized by grind in a lemma of its own: as haves of the rewrite
        # lemma, every grind saw the atoms and normalizations before it, and
        # the rewrite ran out of heartbeats about 200 atoms in.
        source = deep_bounds_conjunction(DEPTH)
        certificate = proof_certificate.export_certificate(source)
        self.assertEqual(certificate["fragment"], "qf_lra")
        text = self.check_lean(source, certificate)
        self.assertEqual(text.count("private theorem normalized_rewrite_"), 1)
        self.assertEqual(text.count("private theorem normalized_atom_"), DEPTH + 2)


if __name__ == "__main__":
    unittest.main()
