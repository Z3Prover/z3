############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Tests for the QF_UFLIA slice of the Lean reconstruction (uninterpreted
# sorts and functions mixed with linear integer arithmetic, through the
# clause log): validation without Lean, and end-to-end checks that need the
# z3 executable and the pinned Lean toolchain.
############################################
import copy
import hashlib
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import z3

_EXAMPLES = Path(__file__).resolve().parent
sys.path.insert(0, str(_EXAMPLES))
import proof_certificate
import proof_clause_log
import proof_to_lean
from test_proof_to_lean_uf import _unsat_core_size, _z3_available, outlined_lemma_sizes, _proof_steps
from test_proof_to_lean_uflra import _th_lemma_nodes

_STANDARD_AXIOMS = "[propext, Classical.choice, Quot.sound]"

# Uninterpreted functions mixed with linear integer arithmetic: the Int twins
# of the QF_UFLRA inputs plus the integer-specific steps (gcd conflicts,
# tightened strict bounds, rounded bounds) through an application. Each
# input is unsatisfiable; the clause log certifies all of them.
UFLIA_INPUTS = {
    # Congruence through an Int-valued function, then a Farkas step over the
    # two applications as opaque atoms.
    "uflia_int_function": """\
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const x Int)
(declare-const y Int)
(assert (= x y))
(assert (< (f x) (f y)))
(check-sat)
""",
    # A function from the sort into Int.
    "uflia_sort_to_int": """\
(set-logic QF_UFLIA)
(declare-sort U 0)
(declare-fun g (U) Int)
(declare-fun h (Int) U)
(declare-const a U)
(declare-const b U)
(declare-const x Int)
(assert (= a b))
(assert (> (g a) (+ (g b) 1)))
(check-sat)
""",
    # A function from Int into the sort under a predicate; the equality of
    # the Int arguments is an implied equality of two bounds.
    "uflia_int_to_sort": """\
(set-logic QF_UFLIA)
(declare-sort U 0)
(declare-fun h (Int) U)
(declare-fun p (U) Bool)
(declare-const x Int)
(declare-const y Int)
(assert (<= x y))
(assert (>= x y))
(assert (p (h x)))
(assert (not (p (h y))))
(check-sat)
""",
    # A gcd conflict through an application: 2 f(x) = 2y + 1 has no integer
    # solution (a cut hint over the opaque atom f(x)).
    "uflia_gcd_application": """\
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const x Int)
(declare-const y Int)
(assert (= (* 2 (f x)) (+ (* 2 y) 1)))
(check-sat)
""",
    # Strict bounds on an application are tightened to f(x) <= 2 and
    # f(x) >= 2, which with the disequality is a conflict.
    "uflia_tightened_application": """\
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const x Int)
(assert (< (f x) 3))
(assert (> (f x) 1))
(assert (not (= (f x) 2)))
(check-sat)
""",
    # Z3's rewriter rounds the bounds on an application (1 <= 3 f(x) is
    # f(x) >= 1), so the assumptions are bridged by rewrites proved over Int.
    "uflia_rounded_application": """\
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const x Int)
(assert (<= 1 (* 3 (f x))))
(assert (<= (* 3 (f x)) 2))
(check-sat)
""",
    # Arguments that are equal as linear forms but differ as terms, which
    # grind's congruence closure needs stated explicitly (the _r helpers).
    "uflia_normalized_arguments": """\
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-fun q (Int) Bool)
(declare-const x Int)
(declare-const y Int)
(assert (q (f (- x y))))
(assert (or (not (q (f (+ x (* (- 1) y))))) (< (f (+ 2 2)) 4)))
(assert (>= (f 4) (f (- x x))))
(assert (= (f 0) 4))
(assert (>= y 0))
(assert (<= x (+ y 1)))
(check-sat)
""",
    # An Int ite inside a function argument, logged in the rewriter's normal
    # form and keyed up to it by the argument helpers.
    "uflia_ite_argument": """\
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const x Int)
(declare-const y Int)
(assert (< (f (ite (> x 0) x (- x))) (f 1)))
(assert (= x 1))
(check-sat)
""",
    # An ite whose branches are one term, (ite c y y): Z3 logs both gate
    # clauses and the bare equality (ite c y y) = y as a tseitin step, all
    # three proved by a case split on c.
    "uflia_same_branch_ite": """\
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const x Int)
(declare-const y Int)
(assert (= (- y (* 3 (ite (= x 3) y y))) -1))
(assert (<= (f x) (+ (f x) (ite (<= y 1) y y))))
(assert (< y 0))
(check-sat)
""",
    # A predicate over Bool alone applied to Int atoms: QF_UFLIA without a
    # sort or a function over Int.
    "uflia_bool_predicate": """\
(set-logic QF_UFLIA)
(declare-fun r (Bool) Bool)
(declare-const x Int)
(declare-const y Int)
(assert (r (< x y)))
(assert (not (r (> y x))))
(check-sat)
""",
    # The Int twin of the exporter test's _UFLRA input plus a gcd conflict
    # through (f (g a)): every hint kind of the slice appears (cut, euf,
    # farkas, implied-eq, bound).
    "uflia_all_hints": """\
(set-logic QF_UFLIA)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun f (Int) Int)
(declare-fun g (U) Int)
(declare-fun h (Int) U)
(declare-fun q (Int) Bool)
(declare-const x Int)
(declare-const y Int)
(assert (= a b))
(assert (<= x y))
(assert (>= x y))
(assert (or (> (g a) (+ (g b) 1)) (q (f x))))
(assert (or (not (q (f y))) (not (= (h x) (h y))) (= (* 2 (f (g a))) (+ (* 2 y) 1))))
(check-sat)
""",
    # Integer div and mod by a numeral next to a function: the solver's
    # arith axioms tie the quotients and remainders to x and y, the euf step
    # carries the congruence (f x) = (f y).
    "uflia_div_mod": """\
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const x Int)
(declare-const y Int)
(assert (= (mod x 2) (mod y 2)))
(assert (= (div x 2) (div y 2)))
(assert (not (= (f x) (f y))))
(check-sat)
""",
}


def random_instance(seed, variables=4, constraints=10, with_sort=False, depth=2, ite=False):
    """A random QF_UFLIA instance, or None when it is satisfiable.

    Int variables, a unary and a binary Int function, a predicate over Int,
    with_sort an uninterpreted sort with constants, functions in both
    directions, and a predicate over it, and with ite Int ite terms whose
    conditions are linear atoms (branches may coincide).
    """
    rng = random.Random(seed)
    names = ["x%d" % i for i in range(variables)]
    lines = ["(set-logic QF_UFLIA)"]
    if with_sort:
        lines += ["(declare-sort U 0)", "(declare-fun a () U)", "(declare-fun b () U)",
                  "(declare-fun h (Int) U)", "(declare-fun g (U) Int)", "(declare-fun p (U) Bool)"]
    lines += ["(declare-fun %s () Int)" % n for n in names]
    lines += ["(declare-fun f (Int) Int)", "(declare-fun k (Int Int) Int)", "(declare-fun q (Int) Bool)"]

    def numeral():
        return str(rng.choice([0, 1, 2, 3, -1]))

    def term(d=depth):
        choice = rng.random()
        if d == 0 or choice < 0.3:
            return rng.choice(names)
        if choice < 0.45:
            return numeral()
        if choice < 0.6:
            return "(f %s)" % term(d - 1)
        if choice < 0.7:
            return "(k %s %s)" % (term(d - 1), term(d - 1))
        if choice < 0.8 and with_sort:
            return "(g %s)" % uterm(d - 1)
        if choice < 0.85 and ite:
            return "(ite (%s %s %s) %s %s)" % (rng.choice(["<=", "<", "="]), term(d - 1), numeral(),
                                                term(d - 1), term(d - 1))
        if choice < 0.9:
            return "(+ %s %s)" % (term(d - 1), term(d - 1))
        return "(- %s (* %s %s))" % (term(d - 1), rng.choice(["2", "3"]), term(d - 1))

    def uterm(d=depth):
        if d == 0 or rng.random() < 0.5:
            return rng.choice(["a", "b"])
        return "(h %s)" % term(d - 1)

    def atom():
        choice = rng.random()
        if choice < 0.5:
            return "(%s %s %s)" % (rng.choice(["<=", "<", "=", ">="]), term(), term())
        if choice < 0.7:
            return "(q %s)" % term()
        if with_sort and choice < 0.85:
            return rng.choice(["(p %s)" % uterm(), "(= %s %s)" % (uterm(), uterm())])
        return "(= %s %s)" % (term(), term())

    def formula():
        choice = rng.random()
        if choice < 0.6:
            return atom()
        if choice < 0.8:
            return "(or %s %s)" % (atom(), atom())
        if choice < 0.9:
            return "(not %s)" % atom()
        return "(=> %s %s)" % (atom(), atom())

    lines += ["(assert %s)" % formula() for _ in range(constraints)]
    lines.append("(check-sat)")
    source = "\n".join(lines) + "\n"
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.add(z3.parse_smt2_string(source, ctx=context))
    return source if solver.check() == z3.unsat else None


def _hints(certificate):
    return {certificate["declarations"][certificate["nodes"][node]["declaration"]]["parameters"][0]
            for node in _th_lemma_nodes(certificate)}


class TestIntegerMixedValidation(unittest.TestCase):
    """Certificate validation and Lean text generation, without running Lean."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")
        cls.source = UFLIA_INPUTS["uflia_sort_to_int"]
        cls.certificate = proof_certificate.export_clause_log_certificate(cls.source)

    def test_generated_lean_carries_the_int_valuation_and_the_interpretation(self):
        self.assertEqual(self.certificate["fragment"], "qf_uflia")
        text = proof_to_lean.reconstruct(self.source, self.certificate)
        self.assertIn("theorem unsat (_atoms : Nat -> Prop)" + proof_to_lean._UFLIA_BINDERS, text)
        self.assertIn("(_vars : Nat -> Int)", proof_to_lean._UFLIA_BINDERS)
        self.assertIn("(_int : Int -> _U) (_ifuns : Nat -> List _U -> Int)", proof_to_lean._UFLIA_BINDERS)
        self.assertIn('-- Element 0: "a"', text)
        self.assertIn('-- Int function 0: "g"', text)
        self.assertIn('-- Uninterpreted sort "U" is the type _U', text)
        self.assertIn("-- Int variables are encoded as Int", text)
        self.assertIn("Int arguments of functions and predicates are injected into _U by _int;"
                      " functions with an Int result are the family _ifuns", text)
        self.assertIn(" : _U := _elems 0", text)
        self.assertIn(" : Int := _ifuns 0 [(term_", text)
        self.assertIn("((1 : Int))", text)
        self.assertNotIn("Rat", text)
        self.assertNotIn("_real", text)
        self.assertNotIn(":= _funs ", text)  # h is declared but applied nowhere in this input
        self.assertIn("private theorem th_lemma_", text)
        self.assertIn("  first | omega | grind (splits := 64)", text)
        self.assertNotIn("sorry", text)
        self.assertNotIn("axiom ", text)
        graph = proof_to_lean._validate_graph(self.source, self.certificate)
        self.assertEqual(graph.sorts, ("U",))
        self.assertTrue(graph.arithmetic)
        self.assertTrue(graph.uninterpreted)
        self.assertEqual(graph.numeric, "Int")
        self.assertEqual(graph.number_type, "Int")
        self.assertEqual(graph.fragment, "qf_uflia")
        self.assertEqual(graph.valuation, proof_to_lean._UFLIA_ARGUMENTS)
        hints = set()
        for node in _th_lemma_nodes(self.certificate):
            hints.add(graph.decl(node).parameters[0])
            proof_to_lean._check_th_lemma(graph, node)
            self.assertTrue(proof_to_lean._reachable(graph, graph.conclusion(node))[1])
        self.assertEqual(hints, {"farkas", "euf"})

    def test_int_arguments_are_injected_and_predicates_range_over_int(self):
        source = UFLIA_INPUTS["uflia_int_to_sort"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertIn('-- Function 0: "h"', text)
        self.assertIn('-- Predicate 0: "p"', text)
        self.assertIn(" : _U := _funs 0 [(_int (term_", text)
        self.assertIn(" : Prop := _preds 0 [(term_", text)
        self.assertNotIn("_ifuns 0", text.split("namespace", 1)[1])
        self.assertIn("implied-eq", _hints(certificate))
        source = UFLIA_INPUTS["uflia_bool_predicate"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertIn("No uninterpreted sort", text)
        self.assertIn("(_bool (formula_", text)
        graph = proof_to_lean._validate_graph(source, certificate)
        self.assertEqual(graph.sorts, ())
        self.assertEqual(graph.fragment, "qf_uflia")

    def test_integer_steps_through_applications_are_checked_before_lean(self):
        # A gcd conflict over the opaque atom f(x) is a cut without
        # coefficients; a tightened strict bound on f(x) is an integer
        # constraint on that atom; both pass the shape checks.
        source = UFLIA_INPUTS["uflia_gcd_application"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        self.assertIn("cut", _hints(certificate))
        graph = proof_to_lean._validate_graph(source, certificate)
        cuts = 0
        for node in _th_lemma_nodes(certificate):
            proof_to_lean._check_th_lemma(graph, node)
            if graph.decl(node).parameters[0] != "cut":
                continue
            cuts += 1
            self.assertEqual(tuple(graph.decl(node).parameters), ("cut",))
            application = next(arg for literal in graph.clause(graph.conclusion(node))
                               for arg in proof_to_lean._reachable(graph, literal)[0]
                               if graph.kind(arg) == z3.Z3_OP_UNINTERPRETED and graph.arguments(arg))
            self.assertTrue(graph.is_arith(application))
        self.assertEqual(cuts, 1)
        # Relabelling the cut as a Farkas step with one unit coefficient per
        # clause literal is rejected: 2 f(x) - 2y - 1 = 0 has rational
        # solutions. (Without coefficients it would be an Int farkas resting
        # on a cut, proved by Lean alone like the cut itself.)
        cut = next(node for node in _th_lemma_nodes(certificate) if graph.decl(node).parameters[0] == "cut")
        literals = len(list(graph.clause(graph.conclusion(cut))))
        tampered = copy.deepcopy(certificate)
        tampered["declarations"][certificate["nodes"][cut]["declaration"]]["parameters"] = ["farkas"] + ["1"] * literals
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "do not refute"):
            proof_to_lean.reconstruct(source, tampered)
        source = UFLIA_INPUTS["uflia_tightened_application"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        graph = proof_to_lean._validate_graph(source, certificate)
        strict = next(node for node in range(len(graph.nodes)) if graph.kind(node) == z3.Z3_OP_LT)
        relation, terms, constant = proof_to_lean._atom_constraint(graph, strict)
        self.assertEqual(relation, "<=")
        self.assertEqual(constant, -2)  # f(x) < 3 is f(x) - 2 <= 0 over Int
        (atom, coefficient), = terms.items()
        self.assertEqual(coefficient, 1)
        self.assertEqual(graph.decl(atom).name, "f")
        for node in _th_lemma_nodes(certificate):
            proof_to_lean._check_th_lemma(graph, node)

    def test_equal_linear_forms_of_int_arguments_are_stated_for_the_theory_tactic(self):
        source = UFLIA_INPUTS["uflia_normalized_arguments"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertIn("have _r", text)
        helper = next(line for line in text.splitlines() if line.startswith("  have _r"))
        self.assertTrue(helper.endswith(":= by first | omega | grind (splits := 64)"), helper)
        graph = proof_to_lean._validate_graph(source, certificate)
        ites = [node for node in range(len(graph.nodes)) if graph.kind(node) == z3.Z3_OP_ITE]
        self.assertEqual(ites, [])
        source = UFLIA_INPUTS["uflia_ite_argument"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        graph = proof_to_lean._validate_graph(source, certificate)
        ites = [node for node in range(len(graph.nodes)) if graph.kind(node) == z3.Z3_OP_ITE and graph.is_arith(node)]
        self.assertTrue(ites)
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertIn("(@ite Int ", text)

    def test_same_branch_ite_gates_are_proved_by_cases(self):
        source = UFLIA_INPUTS["uflia_same_branch_ite"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        graph = proof_to_lean._validate_graph(source, certificate)
        gates = [graph.conclusion(node) for node in range(len(graph.nodes)) if graph.kind(node) == z3.Z3_OP_PR_DEF_AXIOM]
        # Both guarded gates and the bare equality (ite c y y) = y.
        units = [gate for gate in gates if graph.kind(gate) == z3.Z3_OP_EQ]
        self.assertEqual(len(units), 1)
        ite = next(arg for arg in graph.arguments(units[0]) if graph.kind(arg) == z3.Z3_OP_ITE)
        _, then_branch, else_branch = graph.arguments(ite)
        self.assertEqual(then_branch, else_branch)
        self.assertGreaterEqual(len([gate for gate in gates if graph.kind(gate) == z3.Z3_OP_OR]), 2)
        text = proof_to_lean.reconstruct(source, certificate)
        lemmas = [block for block in text.split("private theorem def_axiom_")[1:]
                  if "(ite_eq_left _hc)" in block and "(ite_eq_right _hnc)" in block]
        self.assertEqual(len(lemmas), 1, "the unit gate splits on the condition with both branch lemmas")
        self.assertIn("Decidable.byCases", lemmas[0])
        # A def-axiom equating the ite to another term, (= (ite c y y) x), is
        # no gate: rejected before Lean even though every def-axiom is checked
        # independently of the refutation.
        tampered = copy.deepcopy(certificate)
        x_decl = next(index for index, decl in enumerate(certificate["declarations"])
                      if decl["kind"] == z3.Z3_OP_UNINTERPRETED and decl["name"] == "x")
        x_node = next(index for index, node in enumerate(certificate["nodes"]) if node["declaration"] == x_decl)
        def_axiom = next(index for index, decl in enumerate(certificate["declarations"]) if decl["name"] == "def-axiom")
        tampered["nodes"].append({"declaration": certificate["nodes"][units[0]]["declaration"],
                                  "arguments": [ite, x_node]})
        tampered["nodes"].append({"declaration": def_axiom, "arguments": [len(tampered["nodes"]) - 1]})
        tampered["rule_counts"]["def-axiom"] += 1
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "invalid def-axiom clause"):
            proof_to_lean.reconstruct(source, tampered)

    def test_fragment_consistency(self):
        for fragment, message in [("qf_uf", "qf_uf certificates cannot contain arithmetic"),
                                  ("propositional", "propositional certificates cannot contain arithmetic"),
                                  ("qf_lia", "only qf_uf, qf_uflra, and qf_uflia certificates"),
                                  ("qf_lra", "only qf_uf, qf_uflra, and qf_uflia certificates"),
                                  ("qf_uflra", "only qf_lia and qf_uflia certificates contain Int")]:
            certificate = copy.deepcopy(self.certificate)
            certificate["fragment"] = fragment
            with self.subTest(fragment=fragment):
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, message):
                    proof_to_lean.reconstruct(self.source, certificate)
        # A QF_UFLRA certificate relabeled qf_uflia contains Real, a QF_LIA one
        # declares no uninterpreted symbol, a QF_UF one has no arithmetic.
        from test_proof_to_lean_uflra import UFLRA_INPUTS
        source = UFLRA_INPUTS["uflra_sort_to_real"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        certificate["fragment"] = "qf_uflia"
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "only qf_lia and qf_uflia certificates contain Int"):
            proof_to_lean.reconstruct(source, certificate)
        from test_proof_to_lean_lia import LIA_INPUTS
        source = LIA_INPUTS["lia_gcd"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        certificate["fragment"] = "qf_uflia"
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "only qf_uf, qf_uflra, and qf_uflia certificates"):
            proof_to_lean.reconstruct(source, certificate)
        from test_proof_to_lean_uf import UF_INPUTS
        source = UF_INPUTS["uf_congruence"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        certificate["fragment"] = "qf_uflia"
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "qf_uflia certificates must contain arithmetic"):
            proof_to_lean.reconstruct(source, certificate)
        # The Real twin of the input is another fragment (the certificate's
        # source copy is compared first; the twin's fragment is checked when
        # the copy is made to match).
        twin = self.source.replace(" Int)", " Real)").replace(" 1)", " 1.0)").replace("QF_UFLIA", "QF_UFLRA")
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "does not match the original input"):
            proof_to_lean.reconstruct(twin, self.certificate)
        certificate = copy.deepcopy(self.certificate)
        certificate["source_smt2"] = twin
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "in fragment qf_uflra, not qf_uflia"):
            proof_to_lean.reconstruct(twin, certificate)

    def test_malformed_mixed_declarations_are_rejected(self):
        certificate = copy.deepcopy(self.certificate)
        for declaration in certificate["declarations"]:
            if declaration["name"] == "g":
                declaration["range"] = "Real"  # g returns Int, not Real: its applications no longer fit
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "wrong argument sort|cannot mix Int and Real"):
            proof_to_lean.reconstruct(self.source, certificate)
        # A Real declaration next to Int ones, even one the proof does not use.
        certificate = copy.deepcopy(self.certificate)
        certificate["declarations"].append({"kind": z3.Z3_OP_UNINTERPRETED, "name": "r", "domain": [],
                                            "range": "Real", "parameters": []})
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "cannot mix Int and Real"):
            proof_to_lean.reconstruct(self.source, certificate)
        certificate = copy.deepcopy(self.certificate)
        for declaration in certificate["declarations"]:
            if declaration["name"] == "g":
                declaration["domain"] = ["Int"]  # g takes the sort, not Int
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "wrong argument sort"):
            proof_to_lean.reconstruct(self.source, certificate)
        certificate = copy.deepcopy(self.certificate)
        for declaration in certificate["declarations"]:
            if declaration["kind"] == z3.Z3_OP_ANUM and declaration["name"] == "1":
                declaration["name"] = "1/2"
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "invalid Int numeral declaration"):
            proof_to_lean.reconstruct(self.source, certificate)
        for domain, range_name, message in [
            (["Proof"], "Int", "unsupported arithmetic function declaration"),
            (["BitVec"], "Int", "invalid native declaration"),
            (["Int", "Proof"], "U", "unsupported uninterpreted-sort declaration"),
            (["Int"], "Proof", "invalid native declaration|unsupported"),
        ]:
            with self.subTest(domain=domain, range=range_name):
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, message):
                    proof_to_lean._declaration({"kind": z3.Z3_OP_UNINTERPRETED, "name": "w", "domain": domain,
                                                "range": range_name, "parameters": []}, ("U",))
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "unsupported arithmetic declaration"):
            proof_to_lean._declaration({"kind": z3.Z3_OP_DIV, "name": "/", "domain": ["Int", "Int"],
                                        "range": "Int", "parameters": []}, ())
        # An Int-valued function over the sort, Bool, and Int is a valid declaration.
        decl = proof_to_lean._declaration({"kind": z3.Z3_OP_UNINTERPRETED, "name": "w", "domain": ["U", "Bool", "Int"],
                                           "range": "Int", "parameters": []}, ("U",))
        self.assertEqual(decl.domain, ("U", "Bool", "Int"))

    def test_legacy_core_rejects_the_fragment(self):
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "clause log only"):
            proof_certificate.export_certificate(self.source)


class TestIntegerMixedInProcess(unittest.TestCase):
    """Checks that need neither the z3 executable nor Lean (only the Python bindings)."""

    def test_applications_are_opaque_integer_atoms_of_the_replay(self):
        context = z3.Context()
        f = z3.Function("f", z3.IntSort(context), z3.IntSort(context))
        q = z3.Function("q", z3.IntSort(context), z3.BoolSort(context))
        x = z3.Int("x", context)
        # A strict bound on an application is tightened like one on a variable.
        relation, terms, constant = proof_clause_log._constraint(f(x) < 3)
        self.assertEqual((relation, constant), ("<=", -2))
        self.assertEqual(list(terms.values()), [1])
        self.assertEqual(list(terms), [f(x).get_id()])
        relation, terms, constant = proof_clause_log._constraint(z3.Not(2 * f(x) <= x + 1))
        self.assertEqual((relation, constant), ("<=", 2))  # x + 2 - 2 f(x) <= 0
        self.assertEqual(sorted(terms.values()), [-2, 1])
        # The normalizer tells (q 1) from (q 2) and keys the complement of an
        # Int atom over an application as its tightened form.
        normalizer = proof_clause_log._Normalizer()
        self.assertNotEqual(normalizer.key(q(z3.IntVal(1, context))), normalizer.key(q(z3.IntVal(2, context))))
        self.assertEqual(normalizer.key(z3.Not(f(x) <= 4)), normalizer.key(f(x) >= 5))
        self.assertEqual(normalizer.key(f(x) < 5), normalizer.key(f(x) <= 4))

    def test_random_instances_are_integer_mixed_input(self):
        seeds = [seed for seed in range(40) if random_instance(seed) is not None]
        self.assertTrue(seeds)
        source = random_instance(seeds[0])
        _, fragment = proof_certificate.parse_assertions(source, z3.Context(), integer=True)
        self.assertEqual(fragment, "qf_uflia")
        with self.assertRaisesRegex(proof_certificate.ProofExportError, r"\(qf_uflia\)"):
            proof_certificate.parse_assertions(source, z3.Context())


@unittest.skipUnless(_z3_available(), "the z3 executable is required for the clause log")
class TestIntegerMixedLeanIntegration(unittest.TestCase):
    """End-to-end: z3 clause log, certificate, Lean reconstruction, kernel check."""

    def check(self, source):
        certificate = proof_certificate.export_clause_log_certificate(source)
        self.assertEqual(certificate["fragment"], "qf_uflia")
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "checked.lean"
            proof_to_lean.check_and_write(source, certificate, output)
            text = output.read_text()
            namespace = "Z3Proofs.NativeCertificate.p" + hashlib.sha256(source.encode()).hexdigest()
            statement = text.split("theorem unsat", 1)[1].split(": False :=", 1)[0]
            self.assertEqual(statement.count("    (_h"), len(certificate["assertions"]))
            self.assertIn(proof_to_lean._UFLIA_BINDERS, statement)
            self.assertNotIn("Rat", text)
            output.write_text(text + "\n#print axioms %s.unsat\n" % namespace)
            result = subprocess.run([str(proof_to_lean._CHECK_LEAN), str(output)],
                                    text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            report = " ".join(result.stdout.split())
            self.assertIn(".unsat' depends on axioms: " + _STANDARD_AXIOMS, report)
            return certificate, text

    def test_documented_inputs_verify_under_the_standard_axioms(self):
        hints = set()
        for name, source in UFLIA_INPUTS.items():
            with self.subTest(name=name):
                certificate, text = self.check(source)
                hints |= _hints(certificate)
                if name == "uflia_normalized_arguments":
                    self.assertIn("have _r", text)
                if name == "uflia_all_hints":
                    self.assertEqual(_hints(certificate), {"cut", "euf", "farkas", "implied-eq", "bound"})
                if name == "uflia_same_branch_ite":
                    self.assertIn("def-axiom", certificate["rule_counts"])
                if name == "uflia_div_mod":
                    self.assertEqual(_hints(certificate), {"arith", "euf"})
                    self.assertIn(" / ", text)
                    self.assertIn(" % ", text)
        # Every hint kind of the slice, plus the exporter's own cnf bridge.
        self.assertEqual(hints, {"cut", "euf", "farkas", "implied-eq", "bound", "cnf", "arith"})

    # Seeds of random_instance whose unsat core has at least three assertions,
    # pinned so the checked inputs stay the same across Z3 versions: plain,
    # with an uninterpreted sort, and with ite terms. Seed 14 with ite terms
    # has an ite whose branches coincide inside a product and under a
    # function, the shape that produced the unit gate clause (ite c a a) = a
    # (6 of 38 random ite instances failed on it before it was handled).
    PLAIN_SEEDS = (8, 51, 76)
    SORT_SEEDS = (79, 120)
    ITE_SEEDS = (3, 7)
    SAME_BRANCH_SEED = 14

    def test_random_instances(self):
        for seeds, options in ((self.PLAIN_SEEDS, {}), (self.SORT_SEEDS, {"with_sort": True}),
                               (self.ITE_SEEDS, {"ite": True})):
            for seed in seeds:
                source = random_instance(seed, **options)
                with self.subTest(seed=seed, **options):
                    self.assertGreaterEqual(_unsat_core_size(source), 3, "re-pick seed %d" % seed)
                    certificate, _ = self.check(source)
                    self.assertIn("th-lemma", certificate["rule_counts"])
        source = random_instance(self.SAME_BRANCH_SEED, ite=True)
        self.assertIn("(ite (= x3 3) x2 x2)", source, "re-pick the same-branch seed")
        certificate, text = self.check(source)
        self.assertIn("def-axiom", certificate["rule_counts"])
        self.assertTrue(any("(ite_eq_left _hc)" in block and "(ite_eq_right _hnc)" in block
                            for block in text.split("private theorem def_axiom_")[1:]))

    # Seeds of test_proof_to_lean_lia.random_division_instance with a
    # function: div, mod, and abs atoms under and next to applications, with
    # bound and cut hints (seed 28 also an implied equality) next to the
    # arith axioms.
    DIVISION_SEEDS = (13, 28)

    def test_random_division_instances(self):
        from test_proof_to_lean_lia import random_division_instance
        hints = set()
        for seed in self.DIVISION_SEEDS:
            source = random_division_instance(seed, functions=True)
            self.assertIsNotNone(source, "seed %d is no longer unsatisfiable" % seed)
            with self.subTest(seed=seed):
                certificate, _ = self.check(source)
                hints |= _hints(certificate)
        self.assertLessEqual({"arith", "farkas", "bound", "cut", "euf"}, hints)

    def test_small_chunks_cut_every_lemma_shape(self):
        with patch.object(proof_to_lean, "_OUTLINE_PROOF_STEPS", 0), \
                patch.object(proof_to_lean, "_OUTLINE_CHUNK_STEPS", 3):
            source = UFLIA_INPUTS["uflia_all_hints"]
            certificate, text = self.check(source)
            sizes = outlined_lemma_sizes(text)
            self.assertGreater(len(sizes), 1)
            self.assertLessEqual(max(sizes), 3)
            self.assertEqual(sum(sizes), _proof_steps(certificate))

    def test_false_coefficient_free_lemmas_are_rejected_by_lean(self):
        # A cut claiming the unit clause (<= (f x) y): f(x) and y are opaque
        # Int atoms, so the clause is satisfiable, the shape check passes
        # (one integer linear atom), and Lean must fail without publishing a
        # proof. The same for an Int farkas and bound without coefficients.
        source = UFLIA_INPUTS["uflia_gcd_application"]
        exported = proof_certificate.export_clause_log_certificate(source)
        for hint in ("cut", "farkas", "bound"):
            certificate = copy.deepcopy(exported)
            declarations, nodes = certificate["declarations"], certificate["nodes"]
            application = next(index for index, raw in enumerate(nodes)
                               if declarations[raw["declaration"]]["name"] == "f")
            y = next(index for index, raw in enumerate(nodes) if declarations[raw["declaration"]]["name"] == "y")
            declarations.append({"kind": z3.Z3_OP_LE, "name": "<=", "domain": ["Int", "Int"], "range": "Bool",
                                 "parameters": []})
            nodes.append({"declaration": len(declarations) - 1, "arguments": [application, y]})
            declarations.append({"kind": z3.Z3_OP_PR_TH_LEMMA, "name": "th-lemma", "domain": ["Bool"],
                                 "range": "Proof", "parameters": [hint]})
            nodes.append({"declaration": len(declarations) - 1, "arguments": [len(nodes) - 1]})
            certificate["rule_counts"]["th-lemma"] += 1
            graph = proof_to_lean._validate_graph(source, certificate)
            proof_to_lean._check_th_lemma(graph, len(nodes) - 1)  # the shape passes
            with self.subTest(hint=hint), tempfile.TemporaryDirectory() as directory:
                output = Path(directory) / "checked.lean"
                with self.assertRaises(subprocess.CalledProcessError):
                    proof_to_lean.check_and_write(source, certificate, output)
                self.assertFalse(output.exists(), "no proof is published when Lean rejects the lemma")


if __name__ == "__main__":
    unittest.main()
