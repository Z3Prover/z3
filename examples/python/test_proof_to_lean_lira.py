############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Tests for the QF_LIRA slice of the Lean reconstruction: Int and Real
# variables side by side without conversions, each sort valued on its own
# (_ivars into Int, _vars into Rat). Validation without Lean, and end-to-end
# checks through both proof cores that need the z3 executable and the
# pinned Lean toolchain.
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
import proof_clause_log
import proof_to_lean
from test_proof_to_lean_lia import LIA_INPUTS, _STANDARD_AXIOMS, _hints, _th_lemma_nodes, _z3_available

# Documented QF_LIRA inputs: each refutation needs atoms of both sorts, tied
# together by Boolean structure, while every theory lemma stays within one
# sort (Z3 never relates Int and Real atoms without a conversion).
LIRA_INPUTS = {
    # A Real conflict forces p, under which an Int conflict follows.
    "lira_case_split": """(set-logic QF_LIRA)
(declare-const x Real)
(declare-const y Real)
(declare-const n Int)
(declare-const m Int)
(declare-const p Bool)
(assert (or p (> x (+ y 1.5))))
(assert (or (not p) (> (* 2 n) (+ (* 2 m) 1))))
(assert (< x y))
(assert (< n (+ m 1)))
(check-sat)
""",
    # Parity: 2a = 2b + 1 has a Real solution but no Int one (a cut).
    "lira_parity": """(set-logic QF_LIRA)
(declare-const x Real)
(declare-const a Int)
(declare-const b Int)
(declare-const q Bool)
(assert (= q (> x 0.5)))
(assert (=> q (= (* 2 a) (+ (* 2 b) 1))))
(assert (=> (not q) (< x (- 1.0))))
(assert (> x (- 0.75)))
(check-sat)
""",
    # One condition selects an Int and a Real ite branch at once.
    "lira_ite": """(set-logic QF_LIRA)
(declare-const x Real)
(declare-const n Int)
(declare-const p Bool)
(assert (= x (ite p 1.5 2.5)))
(assert (= n (ite p 3 4)))
(assert (or (> x 2.0) (> n 3)))
(assert (or (< x 2.0) (< n 4)))
(check-sat)
""",
    # abs over both sorts, Real division by a numeral, and Int mod.
    "lira_abs_mod": """(set-logic QF_LIRA)
(declare-const x Real)
(declare-const n Int)
(assert (or (> (abs x) 3.0) (> (abs n) 3) (= (mod n 2) 1)))
(assert (< (- 1.5) (/ x 2.0) 1.5))
(assert (< (- 3) n 3))
(assert (distinct n (- 1) 1))
(check-sat)
""",
}


def random_mixed_instance(seed, variables=3, constraints=12):
    """A random QF_LIRA problem over Int and Real variables tied by Booleans, or None when it is satisfiable."""
    generator = random.Random(seed)
    lines = ["(set-logic QF_LIRA)"]
    lines += ["(declare-const n%d Int)" % i for i in range(variables)]
    lines += ["(declare-const x%d Real)" % i for i in range(variables)]
    lines += ["(declare-const p%d Bool)" % i for i in range(2)]

    def numeral(value, real):
        text = ("%d.%d" % (abs(value) // 2, 5 * (abs(value) % 2)) if real else "%d" % (abs(value) // 2))
        return text if value >= 0 else "(- %s)" % text

    def atom(real):
        chosen = generator.sample(range(variables), generator.randint(1, 2))
        terms = " ".join("(* %s %s%d)" % (numeral(2 * generator.choice([-3, -2, -1, 1, 2, 3]), False),
                                          "x" if real else "n", v) for v in chosen)
        # Real bounds in halves, Int bounds whole, both within [-6, 6].
        bound = generator.randint(-12, 12) if real else 2 * generator.randint(-6, 6)
        return "(%s (+ %s) %s)" % (generator.choice(["<=", ">=", "<", ">", "="]), terms, numeral(bound, real))

    def literal():
        roll = generator.random()
        if roll < 0.2:
            return generator.choice(["p0", "p1", "(not p0)", "(not p1)"])
        return atom(roll < 0.6)

    for _ in range(constraints):
        roll = generator.random()
        if roll < 0.5:
            lines.append("(assert (or %s %s))" % (literal(), literal()))
        elif roll < 0.7:
            lines.append("(assert (or %s %s %s))" % (literal(), literal(), literal()))
        else:
            lines.append("(assert %s)" % atom(generator.random() < 0.5))
    lines.append("(check-sat)")
    source = "\n".join(lines) + "\n"
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.from_string(source)
    return source if solver.check() == z3.unsat else None


def wide_mixed_rewrite_instance(variables=5, ites=False):
    """Int and Real variables bounded, and one clause asking for one of them outside.

    The clause is a single rewrite over 4 * variables linear atoms of both
    sorts, more than proof_to_lean._NORMALIZED_REWRITE_ATOMS for five
    variables of each, so it takes the normalized-rewrite path, where each
    atom keeps its own sort (a strict Int atom keyed as the complement of
    the bound it contradicts, a strict Real one as it is). With ites, every
    atom adds (ite p 1 2) over Int or (ite p 1.0 2.0) over Real, and the
    bounds shift so that both values of p stay inside: the two ites have
    one value table, but each sort keeps its own representative
    (proof_to_lean._ite_representatives).
    """
    lines = ["(set-logic QF_LIRA)"] + ["(declare-const p Bool)"] * ites
    lines += ["(declare-const n%d Int)" % i for i in range(variables)]
    lines += ["(declare-const x%d Real)" % i for i in range(variables)]

    def term(variable, ite):
        return "(+ %s %s)" % (variable, ite) if ites else variable

    low, high, real_low, real_high = ("4", "5", "(- 0.5)", "5.5") if ites else ("5", "7", "0.5", "7.5")
    atoms, bounds = [], []
    for i in range(variables):
        integer, real = term("n%d" % i, "(ite p 1 2)"), term("x%d" % i, "(ite p 1.0 2.0)")
        atoms += ["(< %s 5)" % integer, "(> %s 7)" % integer, "(< %s 0.5)" % real, "(> %s 7.5)" % real]
        bounds += ["(assert (>= n%d %s))" % (i, low), "(assert (<= n%d %s))" % (i, high),
                   "(assert (>= x%d %s))" % (i, real_low), "(assert (<= x%d %s))" % (i, real_high)]
    lines.append("(assert (or %s))" % " ".join(atoms))
    lines += bounds
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


# Unsatisfiable seeds of random_mixed_instance: 12 folds an Int assertion to
# false, after which Z3 logs the rest unprocessed, to_real coercions of Int
# numerals included (see proof_clause_log._Terms.build), 17 has bound and
# euf hints, 18 an Int cut, 21 a cnf lemma.
MIXED_SEEDS = (12, 17, 18, 21)


def _export(source, core):
    if core == "clause-log":
        return proof_certificate.export_clause_log_certificate(source)
    return proof_certificate.export_certificate(source)


class TestMixedValidation(unittest.TestCase):
    """Validation without Lean: the encoding, the fragment labels, and the per-lemma sort."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")
        cls.source = LIRA_INPUTS["lira_ite"]
        cls.certificate = _export(cls.source, "clause-log")

    def test_each_sort_has_its_own_valuation(self):
        self.assertEqual(self.certificate["fragment"], "qf_lira")
        text = proof_to_lean.reconstruct(self.source, self.certificate)
        statement = text.split("theorem unsat", 1)[1].split(": False :=", 1)[0]
        self.assertIn("(_vars : Nat -> Rat) (_ivars : Nat -> Int)", statement)
        self.assertIn("-- Real variables are encoded as Rat (_vars) and Int variables as Int (_ivars)", text)
        # x is variable 0, valued in Rat; n is variable 1, valued in Int.
        self.assertIn('-- Variable 0: "x"', text)
        self.assertIn('-- Variable 1: "n"', text)
        self.assertRegex(text, r"\(_ivars : Nat -> Int\) : Rat := _vars 0\n")
        self.assertRegex(text, r"\(_ivars : Nat -> Int\) : Int := _ivars 1\n")
        self.assertNotIn("_ivars 0", text)
        self.assertNotIn("_vars 1", text.replace("_ivars 1", ""))
        # Numerals and ites carry the sort of their node.
        self.assertIn("((3 : Int))", text)
        self.assertIn("((3 : Rat) / (2 : Rat))", text)
        self.assertIn("(@ite Int ", text)
        self.assertIn("(@ite Rat ", text)

    def test_fragment_labels_and_sorts_are_consistent(self):
        for fragment in ("qf_lia", "qf_lra", "qf_uflia"):
            relabelled = copy.deepcopy(self.certificate)
            relabelled["fragment"] = fragment
            with self.subTest(fragment=fragment):
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError,
                                            "%s certificates cannot mix Int and Real arithmetic" % fragment):
                    proof_to_lean.reconstruct(self.source, relabelled)
        # A single-sort certificate labelled qf_lira, and the mixed input
        # under a single-sort certificate.
        source = LIA_INPUTS["lia_gomory"]
        relabelled = _export(source, "clause-log")
        relabelled["fragment"] = "qf_lira"
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "contain both Int and Real arithmetic"):
            proof_to_lean.reconstruct(source, relabelled)
        relabelled["source_smt2"] = self.source
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "contain both Int and Real arithmetic"):
            proof_to_lean.reconstruct(self.source, relabelled)

    def test_theory_lemmas_over_both_sorts_are_rejected(self):
        # Retarget a farkas lemma at an assertion over atoms of both sorts:
        # the Int and Real treatments differ, so no sort is guessed.
        graph = proof_to_lean._validate_graph(self.source, self.certificate)
        mixed = next(node for node in graph.assertions
                     if {graph.decl(term).range for term in proof_to_lean._reachable(graph, node)[0]}
                     >= {"Int", "Real"})
        lemma = next(node for node in _th_lemma_nodes(self.certificate)
                     if self.certificate["declarations"][self.certificate["nodes"][node]["declaration"]]
                     ["parameters"][0] == "farkas" and node > mixed)
        tampered = copy.deepcopy(self.certificate)
        tampered["nodes"][lemma]["arguments"][-1] = mixed
        graph = proof_to_lean._validate_graph(self.source, tampered)
        for check in (proof_to_lean._check_th_lemma, proof_to_lean._opaque_tactic):
            with self.subTest(check=check.__name__):
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError,
                                            "arithmetic step over both Int and Real atoms at node %d" % lemma):
                    check(graph, lemma)

    def test_ites_of_one_table_keep_their_sort_in_normalized_rewrites(self):
        # (ite p 1 2) over Int and (ite p 1.0 2.0) over Real tabulate alike;
        # each atom's linear form must still range over the ite of its sort.
        source = wide_mixed_rewrite_instance(ites=True)
        text = proof_to_lean.reconstruct(source, _export(source, "clause-log"))
        self.assertIn("private theorem normalized_rewrite_", text)
        atoms = [line for line in text.splitlines() if "let _atom" in line]
        self.assertTrue(any("@ite Int" in line for line in atoms))
        self.assertTrue(any("@ite Rat" in line for line in atoms))
        for line in atoms:
            with self.subTest(atom=line):
                self.assertFalse("@ite Int" in line and ": Rat" in line, line)
                self.assertFalse("@ite Rat" in line and ": Int" in line, line)

    def test_clause_log_numerals_are_read_by_their_spelling(self):
        # The log prints numerals without a sort: in an input over both sorts
        # a decimal point marks a Real numeral, its absence an Int one.
        context = z3.Context()
        assertions, fragment = proof_certificate.parse_assertions(self.source, context, integer=True)
        self.assertEqual(fragment, "qf_lira")
        terms = proof_clause_log._Terms(context, assertions)
        self.assertTrue(z3.is_int(terms.build("3")))
        self.assertTrue(z3.is_real(terms.build("3.0")))
        self.assertEqual(terms.build(["+", "n", "1"]).sexpr(), "(+ n 1)")
        self.assertEqual(terms.build(["<=", "x", ["/", "3.0", "2.0"]]).sexpr(), "(<= x (/ 3.0 2.0))")
        # An Int numeral against a Real term is coerced by z3py, so no input
        # atom matches it.
        self.assertIn("to_real", terms.build(["<=", "x", "1"]).sexpr())


class TestMixedLeanIntegration(unittest.TestCase):
    """End-to-end: both proof cores, certificate, Lean reconstruction, kernel check."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")

    def check(self, source, core):
        certificate = _export(source, core)
        self.assertEqual(certificate["fragment"], "qf_lira")
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "checked.lean"
            proof_to_lean.check_and_write(source, certificate, output)
            text = output.read_text()
            namespace = "Z3Proofs.NativeCertificate.p" + hashlib.sha256(source.encode()).hexdigest()
            statement = text.split("theorem unsat", 1)[1].split(": False :=", 1)[0]
            self.assertEqual(statement.count("    (_h"), len(certificate["assertions"]))
            self.assertIn("(_vars : Nat -> Rat) (_ivars : Nat -> Int)", statement)
            output.write_text(text + "\n#print axioms %s.unsat\n" % namespace)
            result = subprocess.run([str(proof_to_lean._CHECK_LEAN), str(output)], text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            report = " ".join(result.stdout.split())
            self.assertTrue(_STANDARD_AXIOMS in report or "does not depend on any axioms" in report, report)
        return certificate

    def test_documented_lira_inputs_verify_on_both_cores(self):
        hints = set()
        for name, source in LIRA_INPUTS.items():
            for core in ("clause-log", "legacy"):
                with self.subTest(name=name, core=core):
                    certificate = self.check(source, core)
                    if core == "clause-log":
                        hints |= _hints(certificate)
        self.assertLessEqual({"farkas", "cut", "arith"}, hints)

    def test_wide_rewrite_over_both_sorts_verifies_through_the_normalized_path(self):
        source = wide_mixed_rewrite_instance()
        certificate = self.check(source, "clause-log")
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertIn("private theorem normalized_rewrite_", text)
        self.assertIn("_ivars 0", text)
        self.assertIn("_vars 5", text)
        # Int and Real ites of one value table, each keyed by its own sort.
        source = wide_mixed_rewrite_instance(ites=True)
        text = proof_to_lean.reconstruct(source, self.check(source, "clause-log"))
        self.assertIn("private theorem normalized_rewrite_", text)

    def test_pinned_random_instances_verify_on_both_cores(self):
        for seed in MIXED_SEEDS:
            source = random_mixed_instance(seed)
            self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % seed)
            for core in ("clause-log", "legacy"):
                with self.subTest(seed=seed, core=core):
                    self.check(source, core)


if __name__ == "__main__":
    unittest.main()
