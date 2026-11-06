############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Tests for the QF_UFLIRA slice of the Lean reconstruction: uninterpreted
# sorts and functions next to Int and Real variables. Both valuations
# (_vars into Rat, _ivars into Int) sit next to the interpretation _m,
# whose carrier receives Int arguments by _m.int and Real ones by _m.real,
# and whose families _m.ifuns and _m.rfuns value the functions with an Int
# and a Real result. Validation without Lean, and end-to-end checks through
# both proof cores that need the z3 executable and the pinned Lean
# toolchain.
############################################
import copy
from pathlib import Path
import random
import re
import sys
import unittest

import z3

_EXAMPLES = Path(__file__).resolve().parent
sys.path.insert(0, str(_EXAMPLES))
import proof_certificate
import lean_test_support
import proof_to_lean
from test_proof_to_lean_lia import _STANDARD_AXIOMS, _hints, _z3_available
from test_proof_to_lean_lira import LIRA_INPUTS
from test_proof_to_lean_uflia import UFLIA_INPUTS

# Documented QF_UFLIRA inputs: each refutation needs an uninterpreted
# function or predicate whose signature mentions both arithmetic sorts.
UFLIRA_INPUTS = {
    # f : Int -> Real. n = 3 by Int arithmetic, so (f n) = (f 3) by
    # congruence over an Int argument, which contradicts the Real bounds.
    "int_argument_real_result": """(set-logic QF_UFLIRA)
(declare-fun f (Int) Real)
(declare-const n Int)
(declare-const m Int)
(declare-const x Real)
(assert (= n (+ m 1)))
(assert (= m 2))
(assert (> (f n) x))
(assert (< (f 3) (- x 1.0)))
(check-sat)
""",
    # g : Real -> Int. x = 3.0 by Real arithmetic, so (g x) = (g 3.0); an
    # Int parity cut over the results refutes 2 (g x) = 2 (g 3.0) + 1.
    "real_argument_int_result": """(set-logic QF_UFLIRA)
(declare-fun g (Real) Int)
(declare-const x Real)
(declare-const y Real)
(assert (= x (* 2.0 y)))
(assert (= y 1.5))
(assert (= (* 2 (g x)) (+ (* 2 (g 3.0)) 1)))
(check-sat)
""",
    # A predicate over Int, Real, and an uninterpreted sort, whose Int
    # argument is itself an application over the sort.
    "predicate_over_both_sorts": """(set-logic QF_UFLIRA)
(declare-sort U 0)
(declare-fun P (Int Real U) Bool)
(declare-fun h (U) Int)
(declare-const a U)
(declare-const b U)
(declare-const n Int)
(declare-const x Real)
(assert (P n x a))
(assert (not (P (h b) (+ x 0.0) b)))
(assert (= a b))
(assert (= (h a) n))
(check-sat)
""",
    # to_real ties the sorts: x = n, so (k x) = (k (to_real n)), and the
    # Real function r is bounded on both sides by that Int value cast.
    "to_real_between_functions": """(set-logic QF_UFLIRA)
(declare-fun r (Int) Real)
(declare-fun k (Real) Int)
(declare-const n Int)
(declare-const x Real)
(assert (= x (to_real n)))
(assert (> (r n) (to_real (k x))))
(assert (< (r n) (to_real (k (to_real n)))))
(check-sat)
""",
    # An Int and a Real function applied to the same ite of numerals, one
    # per sort: the two arguments share a linear form but no helper may
    # equate them (they are injected by _m.int and _m.real).
    "ite_arguments_of_both_sorts": """(set-logic QF_UFLIRA)
(declare-fun f (Int) Real)
(declare-fun g (Real) Real)
(declare-const x Real)
(declare-const y Real)
(assert (> (f (ite (> x 0.0) 1 0)) y))
(assert (> (g (ite (> x 0.0) 1.0 0.0)) y))
(assert (< (+ (f (ite (> x 0.0) 1 0)) (g (ite (> x 0.0) 1.0 0.0))) (* 2.0 y)))
(check-sat)
""",
}


def random_uflira_instance(seed, variables=2, constraints=10, depth=2, casts=False, ites=False):
    """A random QF_UFLIRA instance, or None when it is satisfiable.

    Int variables n_i and Real variables x_i, functions in both directions
    between the sorts (f : Int -> Real, g : Real -> Int), one taking both
    (k : Int Real -> Int), a predicate over both (q), and an uninterpreted
    sort reached from Int and read back as Real (h, r). Atoms compare terms
    of one sort, and with casts Real terms include to_real of Int terms.
    With ites, a function or predicate argument of either sort may be an
    ite of the numerals 0 and 1 over a condition of either sort from a
    small pool, so that Int and Real arguments share linear forms ((ite c
    1 0) and (ite c 1.0 0.0)). Without either option the random sequence
    is the one the pinned seeds were drawn from.
    """
    rng = random.Random(seed)
    lines = ["(set-logic QF_UFLIRA)", "(declare-sort U 0)", "(declare-const a U)", "(declare-const b U)"]
    lines += ["(declare-const n%d Int)" % i for i in range(variables)]
    lines += ["(declare-const x%d Real)" % i for i in range(variables)]
    lines += ["(declare-fun f (Int) Real)", "(declare-fun g (Real) Int)", "(declare-fun k (Int Real) Int)",
              "(declare-fun q (Int Real) Bool)", "(declare-fun h (Int) U)", "(declare-fun r (U) Real)"]

    def ite_argument(numerals):
        condition = rng.choice(["(> x%d 0.0)", "(<= n%d 0)"]) % rng.randrange(variables)
        then_branch = rng.randrange(2)
        return "(ite %s %s %s)" % (condition, numerals[then_branch], numerals[1 - then_branch])

    def int_term(d=depth, argument=False):
        if ites and argument and rng.random() < 0.3:
            return ite_argument(("0", "1"))
        roll = rng.random()
        if d == 0 or roll < 0.35:
            return "n%d" % rng.randrange(variables)
        if roll < 0.5:
            return str(rng.choice([0, 1, 2, -1]))
        if roll < 0.65:
            return "(g %s)" % real_term(d - 1, True)
        if roll < 0.75:
            return "(k %s %s)" % (int_term(d - 1, True), real_term(d - 1, True))
        return "(+ %s %s)" % (int_term(d - 1), int_term(d - 1))

    def real_term(d=depth, argument=False):
        if ites and argument and rng.random() < 0.3:
            return ite_argument(("0.0", "1.0"))
        roll = rng.random()
        if d == 0 or roll < 0.35:
            return "x%d" % rng.randrange(variables)
        if roll < 0.5:
            return rng.choice(["0.0", "1.0", "0.5", "(- 1.5)"])
        if roll < 0.65:
            return "(f %s)" % int_term(d - 1, True)
        if roll < 0.75:
            return "(r %s)" % rng.choice(["a", "b", "(h %s)" % int_term(d - 1, True)])
        if casts and roll < 0.85:
            return "(to_real %s)" % int_term(d - 1)
        return "(+ %s %s)" % (real_term(d - 1), real_term(d - 1))

    def atom():
        roll = rng.random()
        if roll < 0.35:
            return "(%s %s %s)" % (rng.choice(["<=", "<", "="]), int_term(), int_term())
        if roll < 0.7:
            return "(%s %s %s)" % (rng.choice(["<=", "<", "="]), real_term(), real_term())
        if roll < 0.85:
            return "(q %s %s)" % (int_term(argument=True), real_term(argument=True))
        return "(= %s %s)" % (rng.choice(["a", "b"]), "(h %s)" % int_term(argument=True))

    def formula():
        roll = rng.random()
        if roll < 0.55:
            return atom()
        if roll < 0.8:
            return "(or %s %s)" % (atom(), atom())
        return "(not %s)" % atom()

    lines += ["(assert %s)" % formula() for _ in range(constraints)]
    lines.append("(check-sat)")
    source = "\n".join(lines) + "\n"
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set("timeout", 10000)
    solver.from_string(source)
    return source if solver.check() == z3.unsat else None


# Pinned seeds whose clause logs carry theory lemmas over functions of both
# sorts: (keyword arguments, seed). 16 and 54 (a cut over Int applications
# of Real terms) with the defaults; 3 and 40 (a bound step) with to_real;
# 105 with ite arguments, whose Int (ite c 0 1) and Real (ite c 0.0 1.0)
# arguments share a linear form (an Int = Rat helper failed Lean there
# before the helpers were grouped per sort).
_CASTS = {"variables": 3, "constraints": 14, "depth": 3, "casts": True}
_ITES = {"variables": 2, "constraints": 10, "depth": 3, "ites": True}
UFLIRA_SEEDS = (({}, 16), ({}, 54), (_CASTS, 3), (_CASTS, 40), (_ITES, 105))


def _export(source, core):
    if core == "clause-log":
        return proof_certificate.export_clause_log_certificate(source)
    return proof_certificate.export_certificate(source)


def _statement(text):
    return text.split("theorem unsat", 1)[1].split(": False :=", 1)[0]


class TestUFLIRAValidation(unittest.TestCase):
    """Validation without Lean: the encoding, the fragment labels, and the per-lemma sort."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")
        cls.source = UFLIRA_INPUTS["to_real_between_functions"]
        cls.certificate = _export(cls.source, "clause-log")

    def test_both_valuations_sit_next_to_the_interpretation(self):
        self.assertEqual(self.certificate["fragment"], "qf_uflira")
        text = proof_to_lean.reconstruct(self.source, self.certificate)
        self.assertIn("(_vars : Nat -> Rat) (_ivars : Nat -> Int) (_m : Interpretation)", _statement(text))
        structure = text.split("structure Interpretation where\n", 1)[1].split("\n\n", 1)[0]
        for field in ("real : Rat -> U", "rfuns : Nat -> List U -> Rat", "int : Int -> U",
                      "ifuns : Nat -> List U -> Int"):
            self.assertIn("  %s\n" % field, structure + "\n")
        # r : Int -> Real is a Real function over an injected Int argument,
        # k : Real -> Int an Int function over an injected Real argument.
        self.assertIn('-- Real function 0: "r"', text)
        self.assertIn('-- Int function 1: "k"', text)
        self.assertIn("-- Real arguments of functions and predicates are injected into _m.U by _m.real", text)
        self.assertIn("-- Int arguments of functions and predicates are injected into _m.U by _m.int", text)
        self.assertRegex(text, r": Rat := _m\.rfuns 0 \[\(_m\.int \(term_\d+ _atoms _vars _ivars _m\)\)\]\n")
        self.assertRegex(text, r": Int := _m\.ifuns 1 \[\(_m\.real \(term_\d+ _atoms _vars _ivars _m\)\)\]\n")
        self.assertNotIn("_m.rfuns 1", text)
        self.assertNotIn("_m.ifuns 0", text)

    def test_fragment_labels_and_sorts_are_consistent(self):
        for fragment, message in (("qf_uflia", "qf_uflia certificates cannot mix Int and Real"),
                                  ("qf_uflra", "qf_uflra certificates cannot mix Int and Real"),
                                  ("qf_lira", "only qf_uf, qf_uflra, qf_uflia, and qf_uflira certificates")):
            relabelled = copy.deepcopy(self.certificate)
            relabelled["fragment"] = fragment
            with self.subTest(fragment=fragment):
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, message):
                    proof_to_lean.reconstruct(self.source, relabelled)
        # Certificates over one arithmetic sort, or without uninterpreted
        # symbols, labelled qf_uflira.
        for source in (LIRA_INPUTS["lira_ite"], UFLIA_INPUTS["uflia_int_function"]):
            relabelled = _export(source, "clause-log")
            relabelled["fragment"] = "qf_uflira"
            with self.subTest(source=source):
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError,
                                            "contain both Int and Real arithmetic|declare an uninterpreted sort"):
                    proof_to_lean.reconstruct(source, relabelled)

    def test_function_arguments_do_not_decide_the_sort_of_a_lemma(self):
        # Each farkas lemma of int_argument_real_result is over Real atoms,
        # applications of f to Int terms among them, and the euf
        # congruence (f n) = (f 3) from 3 = n relates the sorts without a
        # conversion; neither is rejected as a step over both sorts.
        source = UFLIRA_INPUTS["int_argument_real_result"]
        certificate = _export(source, "clause-log")
        graph = proof_to_lean._validate_graph(source, certificate)
        sorts = {}
        for node in range(len(graph.nodes)):
            decl = graph.decl(node)
            if decl.name == "th-lemma" and decl.parameters[0] in ("farkas", "bound", "cut"):
                sorts[node] = proof_to_lean._lemma_numeric(graph, node)
        self.assertTrue(sorts)
        self.assertIn("Real", sorts.values())
        self.assertNotIn(proof_to_lean._CAST, sorts.values())
        proof_to_lean.reconstruct(source, certificate)

    def test_argument_helpers_never_equate_terms_of_two_sorts(self):
        # The Int argument (ite c 1 0) of f and the Real argument (ite c 1.0
        # 0.0) of g have one linear form; the normal-form helpers
        # (_real_argument_helpers) group arguments per sort, so none states
        # an Int term equal to a Real one.
        source = UFLIRA_INPUTS["ite_arguments_of_both_sorts"]
        for core in ("clause-log", "legacy"):
            with self.subTest(core=core):
                certificate = _export(source, core)
                graph = proof_to_lean._validate_graph(source, certificate)
                arguments = {argument for node in range(len(graph.nodes))
                             if graph.kind(node) == z3.Z3_OP_UNINTERPRETED
                             for argument in graph.arguments(node) if graph.is_arith(argument)}
                keys = {}
                for argument in arguments:
                    keys.setdefault(proof_to_lean._real_argument_key(graph, argument), set()).add(
                        graph.decl(argument).range)
                self.assertIn({"Int", "Real"}, keys.values())
                text = proof_to_lean.reconstruct(source, certificate)
                for first, second in re.findall(r"have _r(\d+)_(\d+) :", text):
                    self.assertEqual(graph.decl(int(first)).range, graph.decl(int(second)).range,
                                     "helper _r%s_%s equates terms of two sorts" % (first, second))

    def test_a_lemma_over_both_sorts_without_a_conversion_is_still_rejected(self):
        # Retarget the Real farkas lemma (f n) > x, (f 3) < x - 1, ... at an
        # Int atom next to its Real ones: no sort is guessed.
        source = UFLIRA_INPUTS["int_argument_real_result"]
        certificate = _export(source, "clause-log")
        graph = proof_to_lean._validate_graph(source, certificate)
        int_atom = next(node for node in range(len(graph.nodes))
                        if graph.kind(node) in (z3.Z3_OP_LE, z3.Z3_OP_GE, z3.Z3_OP_LT, z3.Z3_OP_GT, z3.Z3_OP_EQ)
                        and graph.decl(node).domain == ("Int", "Int"))
        farkas = next(node for node in range(len(graph.nodes))
                      if graph.decl(node).name == "th-lemma" and graph.decl(node).parameters[0] == "farkas"
                      and proof_to_lean._lemma_numeric(graph, node) == "Real")
        clause = graph.conclusion(farkas)
        literals = list(graph.clause(clause))
        nodes = list(graph.nodes)
        nodes[clause] = proof_to_lean._Node(nodes[clause].declaration, tuple(literals[:-1] + [int_atom]))
        mixed = proof_to_lean._Graph(graph.declarations, tuple(nodes), graph.assertions, graph.proof,
                                     graph.arithmetic, graph.sorts, graph.uninterpreted, graph.numeric)
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "arithmetic step over both Int and Real"):
            proof_to_lean._lemma_numeric(mixed, farkas)


def _check_in_lean(test, source, core):
    """Export, reconstruct, and kernel-check a qf_uflira input; return the certificate."""
    certificate = _export(source, core)
    test.assertEqual(certificate["fragment"], "qf_uflira")
    text, report = lean_test_support.check(test, source, certificate)
    statement = _statement(text)
    test.assertEqual(statement.count("    (_h"), len(certificate["assertions"]))
    test.assertIn("(_vars : Nat -> Rat) (_ivars : Nat -> Int) (_m : Interpretation)", statement)
    test.assertTrue(_STANDARD_AXIOMS in report or "does not depend on any axioms" in report, report)
    return certificate


class TestUFLIRALeanIntegration(unittest.TestCase):
    """End-to-end: both proof cores, certificate, Lean reconstruction, kernel check."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")

    def test_documented_inputs_verify_on_both_cores(self):
        lean_test_support.prefetch((source, _export(source, core)) for source in UFLIRA_INPUTS.values()
                                    for core in ("clause-log", "legacy"))
        hints = set()
        for name, source in UFLIRA_INPUTS.items():
            for core in ("clause-log", "legacy"):
                with self.subTest(name=name, core=core):
                    certificate = _check_in_lean(self, source, core)
                    if core == "clause-log":
                        hints |= _hints(certificate)
        self.assertLessEqual({"farkas", "euf", "implied-eq"}, hints)

    def test_pinned_random_instances_verify_on_both_cores(self):
        hints = set()
        for arguments, seed in UFLIRA_SEEDS:
            source = random_uflira_instance(seed, **arguments)
            self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % seed)
            for core in ("clause-log", "legacy"):
                with self.subTest(seed=seed, options=sorted(arguments), core=core):
                    certificate = _check_in_lean(self, source, core)
                    if core == "clause-log":
                        hints |= _hints(certificate)
        self.assertLessEqual({"farkas", "euf", "cut", "bound"}, hints)


if __name__ == "__main__":
    unittest.main()
