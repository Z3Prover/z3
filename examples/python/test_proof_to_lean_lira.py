############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Tests for the QF_LIRA slice of the Lean reconstruction: Int and Real
# variables side by side, each sort valued on its own (_ivars into Int,
# _vars into Rat), and related by to_real (Int.cast into Rat). Validation without Lean, and end-to-end
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
from test_proof_to_lean_lia import LIA_INPUTS, _STANDARD_AXIOMS, _hints, _parameters, _th_lemma_nodes, _z3_available

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


# Documented inputs relating the sorts through to_real: theory lemmas over
# Int and Real atoms at once, proved with the Int atoms cast into Rat and
# the Real atoms over Int terms alone tied to Int atoms
# (proof_to_lean._cast_facts).
CAST_INPUTS = {
    # x = n, 0 < x < 1: one farkas lemma over both sorts, which refutes only
    # once the Int literal (not (<= n 0)) is tightened to n >= 1.
    "cast_tightening": """(set-logic QF_LIRA)
(declare-const x Real)
(declare-const n Int)
(assert (= x (to_real n)))
(assert (< 0.0 x))
(assert (< x 1.0))
(check-sat)
""",
    # A sum under to_real next to a Real offset, and an Int ite of numerals
    # in a Real position, which Z3 reads as (to_real (ite p 1 2)) (logic ALL).
    "cast_sum_ite": """(declare-const x Real)
(declare-const y Real)
(declare-const n Int)
(declare-const m Int)
(declare-const p Bool)
(assert (= x (+ (to_real (+ n m)) 0.5)))
(assert (or (> x 4.0) (< n 0) (> y 2.5)))
(assert (<= (+ n m) 3))
(assert (>= n 0))
(assert (= y (ite p 1 2)))
(check-sat)
""",
    # 2n = 2m + 1 over the casts: refuted by integrality alone, a cut over
    # a Real atom whose linear form ranges over Int terms.
    "cast_parity_cut": """(set-logic QF_LIRA)
(declare-const n Int)
(declare-const m Int)
(assert (= (* 2.0 (to_real n)) (+ (* 2.0 (to_real m)) 1.0)))
(check-sat)
""",
    # div, mod, and abs of Int terms under to_real.
    "cast_div_mod_abs": """(set-logic QF_LIRA)
(declare-const x Real)
(declare-const n Int)
(assert (= x (to_real (+ (div n 3) (mod n 3)))))
(assert (or (< x 2.5) (> x 3.5) (<= (abs (to_real n)) 0.5)))
(assert (= n 5))
(check-sat)
""",
}


def random_cast_instance(seed, variables=3, constraints=10):
    """A random QF_LIRA problem whose Real atoms range over to_real of Int terms, or None when it is satisfiable."""
    generator = random.Random(seed)
    lines = ["(set-logic QF_LIRA)"]
    lines += ["(declare-const n%d Int)" % i for i in range(variables)]
    lines += ["(declare-const x%d Real)" % i for i in range(variables)]
    lines += ["(declare-const p%d Bool)" % i for i in range(2)]

    def coefficient():
        value = generator.choice([-3, -2, -1, 1, 2, 3])
        return "%d" % value if value > 0 else "(- %d)" % -value

    def real_numeral(halves):
        text = "%d.%d" % (abs(halves) // 2, 5 * (abs(halves) % 2))
        return text if halves >= 0 else "(- %s)" % text

    def int_term():
        roll, v = generator.random(), generator.randrange(variables)
        if roll < 0.5:
            return "n%d" % v
        if roll < 0.8:
            w = generator.randrange(variables)
            return "(+ n%d (* %s n%d))" % (v, coefficient(), w)
        return "(ite p%d n%d %s)" % (generator.randrange(2), v, integer_numeral(generator.randint(-2, 2)))

    def real_term():
        return "(to_real %s)" % int_term() if generator.random() < 0.6 else "x%d" % generator.randrange(variables)

    def integer_numeral(value):
        return "%d" % value if value >= 0 else "(- %d)" % -value

    def atom():
        roll = generator.random()
        relation = generator.choice(["<=", ">=", "<", ">", "="])
        if roll < 0.6:
            terms = ["(* %s.0 %s)" % (generator.choice([1, 2, 3]), real_term())
                     for _ in range(generator.randint(1, 2))]
            left = terms[0] if len(terms) == 1 else "(+ %s)" % " ".join(terms)
            return "(%s %s %s)" % (relation, left, real_numeral(generator.randint(-12, 12)))
        return "(%s %s %s)" % (relation, int_term(), integer_numeral(generator.randint(-6, 6)))

    def literal():
        if generator.random() < 0.15:
            return generator.choice(["p0", "p1", "(not p0)", "(not p1)"])
        return atom()

    for _ in range(constraints):
        roll = generator.random()
        if roll < 0.4:
            lines.append("(assert (or %s %s))" % (literal(), literal()))
        elif roll < 0.55:
            lines.append("(assert (or %s %s %s))" % (literal(), literal(), literal()))
        else:
            lines.append("(assert %s)" % atom())
    lines.append("(check-sat)")
    source = "\n".join(lines) + "\n"
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.from_string(source)
    return source if solver.check() == z3.unsat else None


# Unsatisfiable seeds of random_cast_instance: 11 and 36 have clause-log
# cuts over Real atoms of Int terms, 12 legacy congruences through to_real,
# 25 a legacy farkas lemma without coefficients over both sorts.
CAST_SEEDS = (11, 12, 25, 36)


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


def _check_in_lean(test, source, core):
    """Export, reconstruct, and kernel-check a qf_lira input; return the certificate and the Lean text."""
    certificate = _export(source, core)
    test.assertEqual(certificate["fragment"], "qf_lira")
    with tempfile.TemporaryDirectory() as directory:
        output = Path(directory) / "checked.lean"
        proof_to_lean.check_and_write(source, certificate, output)
        text = output.read_text()
        namespace = "Z3Proofs.NativeCertificate.p" + hashlib.sha256(source.encode()).hexdigest()
        statement = text.split("theorem unsat", 1)[1].split(": False :=", 1)[0]
        test.assertEqual(statement.count("    (_h"), len(certificate["assertions"]))
        test.assertIn("(_vars : Nat -> Rat) (_ivars : Nat -> Int)", statement)
        output.write_text(text + "\n#print axioms %s.unsat\n" % namespace)
        result = subprocess.run([str(proof_to_lean._CHECK_LEAN), str(output)], text=True, capture_output=True)
        test.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        report = " ".join(result.stdout.split())
        test.assertTrue(_STANDARD_AXIOMS in report or "does not depend on any axioms" in report, report)
    return certificate, text


class TestMixedLeanIntegration(unittest.TestCase):
    """End-to-end: both proof cores, certificate, Lean reconstruction, kernel check."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")

    def check(self, source, core):
        return _check_in_lean(self, source, core)[0]

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


class TestCastValidation(unittest.TestCase):
    """Validation without Lean of to_real: its encoding, the cast facts, and what stays rejected."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")
        cls.source = CAST_INPUTS["cast_tightening"]
        cls.certificate = _export(cls.source, "clause-log")

    def test_to_real_is_int_cast_and_lemmas_get_cast_facts(self):
        self.assertIn({"kind": z3.Z3_OP_TO_REAL, "name": "to_real", "domain": ["Int"], "range": "Real",
                       "parameters": []}, self.certificate["declarations"])
        text = proof_to_lean.reconstruct(self.source, self.certificate)
        self.assertIn("-- Real variables are encoded as Rat (_vars) and Int variables as Int (_ivars), "
                      "to_real is Int.cast into Rat", text)
        self.assertRegex(text, r"\(_ivars : Nat -> Int\) : Rat := \(\(\(term_\d+ _atoms _vars _ivars\) : Int\) : Rat\)")
        for lemma in ("_int_cast_le", "_int_cast_lt", "_int_cast_eq"):
            self.assertIn("private theorem %s (s t : Int)" % lemma, text)
        # The farkas lemma over x = n, (not (<= n 0)), x < 1 transports the
        # Int atom into Rat and pushes the casts before grind.
        self.assertRegex(text, r"have _c\d+ := _int_cast_le \(_ivars 1\) \(\(\(0 : Int\)\)\)\n\s+push_cast at \*")
        # A certificate without to_real states none of this.
        text = proof_to_lean.reconstruct(LIRA_INPUTS["lira_ite"], _export(LIRA_INPUTS["lira_ite"], "clause-log"))
        self.assertNotIn("_int_cast_le", text)
        self.assertNotIn("push_cast", text)

    def test_real_atoms_over_int_terms_are_tied_to_int_atoms(self):
        # 2n = 2m + 1 over the casts is an integer constraint: the cut gets
        # it as an Int atom, scaled to integer coefficients.
        source = CAST_INPUTS["cast_parity_cut"]
        certificate = _export(source, "clause-log")
        self.assertIn("cut", _hints(certificate))
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertRegex(text, r"have _r\d+ : .* <-> \(\(.*\) = \(\(0 : Int\)\)\) := "
                               r"Iff\.trans \(by push_cast; grind\) Rat\.intCast_inj")

    def test_real_atoms_over_int_terms_key_by_their_meaning(self):
        # A Real atom over to_real alone is not tightened like an Int atom:
        # its key (_normalized_atom, used by wide normalized rewrites and ite
        # tables) must tighten it before taking the integer complement, so
        # -2n + 1/2 <= 0 keys as not (n <= 0), like the Int atom n >= 1.
        source = ("(set-logic QF_LIRA)\n(declare-const n Int)\n(declare-const x Real)\n"
                  "(assert (or (<= (+ (* (- 2.0) (to_real n)) 0.5) 0.0) (> x 1.0)))\n"
                  "(assert (< n 1))\n(assert (<= x 1.0))\n(assert (or (< (to_real n) 2.5) (> x 0.0)))\n"
                  "(check-sat)\n")
        for core in ("clause-log", "legacy"):
            graph = proof_to_lean._validate_graph(source, _export(source, core))
            checked = 0
            for node in range(len(graph.nodes)):
                kind, arguments = graph.kind(node), graph.arguments(node)
                if graph.is_term(node) or kind not in proof_to_lean._CAST_ATOMS or kind == z3.Z3_OP_EQ:
                    continue
                if not graph.is_arith(arguments[0]):
                    continue
                relation, terms, constant = proof_to_lean._atom_constraint(graph, node)
                if len(terms) != 1 or not graph.is_int(next(iter(terms))):
                    continue
                (relation_key, ordered, constant_key), negated = proof_to_lean._normalized_atom(
                    graph, node, lambda variable: (0, variable))
                (_, coefficient), = ordered
                for value in range(-4, 5):
                    exact = sum(c * value for c in terms.values()) + constant
                    expected = exact <= 0 if relation == "<=" else exact < 0
                    keyed = coefficient * value + constant_key
                    keyed = keyed <= 0 if relation_key == "<=" else keyed < 0
                    with self.subTest(core=core, node=node, n=value):
                        self.assertEqual(keyed != negated, expected)
                checked += 1
            self.assertGreater(checked, 0)

    def test_invalid_to_real_declarations_are_rejected(self):
        for domain, range_ in ((["Real"], "Real"), (["Int"], "Int"), (["Int", "Int"], "Real")):
            tampered = copy.deepcopy(self.certificate)
            declaration = next(d for d in tampered["declarations"] if d["name"] == "to_real")
            declaration["domain"], declaration["range"] = domain, range_
            with self.subTest(domain=domain, range=range_):
                with self.assertRaises(proof_to_lean.ReconstructionError):
                    proof_to_lean.reconstruct(self.source, tampered)

    def test_cuts_over_real_atoms_with_real_terms_are_rejected(self):
        # A cut rounds integer-valued forms only: retargeted at an assertion
        # with a Real atom over a Real variable, the step is rejected, as
        # the exporter rejects such a hint.
        source = random_cast_instance(CAST_SEEDS[0])
        certificate = _export(source, "clause-log")
        graph = proof_to_lean._validate_graph(source, certificate)
        lemma = next(node for node in _th_lemma_nodes(certificate)
                     if _parameters(certificate, node)[0] == "cut")

        def mixes(node):
            # A clause of inequalities (a denied equality is no constraint)
            # over to_real and a Real variable.
            reachable = proof_to_lean._reachable(graph, node)[0]
            literals = graph.arguments(node) if graph.kind(node) == z3.Z3_OP_OR else [node]
            return (all(graph.kind(literal) != z3.Z3_OP_EQ for literal in literals)
                    and any(graph.kind(term) == z3.Z3_OP_TO_REAL for term in reachable)
                    and any(graph.kind(term) == z3.Z3_OP_UNINTERPRETED and graph.decl(term).range == "Real"
                            for term in reachable))
        target = next(node for node in graph.assertions if mixes(node) and node < lemma)
        tampered = copy.deepcopy(certificate)
        tampered["nodes"][lemma]["arguments"][-1] = target
        graph = proof_to_lean._validate_graph(source, tampered)
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError,
                                    "cut th-lemma over a Real atom with a Real term at node %d" % lemma):
            proof_to_lean._check_th_lemma(graph, lemma)
        context = z3.Context()
        n, x = z3.Int("n", ctx=context), z3.Real("x", ctx=context)
        quarter = z3.RealVal("9/4", ctx=context)
        self.assertFalse(proof_clause_log.check_linear_hint("cut", [(1, z3.ToReal(n) == quarter)]))
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "cut hint over Real atoms"):
            proof_clause_log.check_linear_hint("cut", [(1, x + z3.ToReal(n) == quarter)])


class TestCastLeanIntegration(unittest.TestCase):
    """End-to-end through to_real: both proof cores, certificate, Lean reconstruction, kernel check."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")

    def test_documented_cast_inputs_verify_on_both_cores(self):
        hints = set()
        for name, source in CAST_INPUTS.items():
            for core in ("clause-log", "legacy"):
                with self.subTest(name=name, core=core):
                    certificate, text = _check_in_lean(self, source, core)
                    self.assertIn("_int_cast_", text)
                    if core == "clause-log":
                        hints |= _hints(certificate)
        self.assertLessEqual({"farkas", "cut", "arith"}, hints)

    def test_pinned_random_cast_instances_verify_on_both_cores(self):
        hints, congruences = set(), 0
        for seed in CAST_SEEDS:
            source = random_cast_instance(seed)
            self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % seed)
            for core in ("clause-log", "legacy"):
                with self.subTest(seed=seed, core=core):
                    certificate, text = _check_in_lean(self, source, core)
                    if core == "clause-log":
                        hints |= _hints(certificate)
                    else:
                        congruences += text.count("congrArg (fun (_t : Int) => ((_t : Int) : Rat))")
        self.assertIn("cut", hints)
        self.assertGreater(congruences, 0)


if __name__ == "__main__":
    unittest.main()
