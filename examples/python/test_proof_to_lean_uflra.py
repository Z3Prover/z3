############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Tests for the QF_UFLRA slice of the Lean reconstruction (uninterpreted
# sorts and functions mixed with linear real arithmetic): validation without
# Lean, and end-to-end checks that need the z3 executable and the pinned
# Lean toolchain.
############################################
import copy
import hashlib
import json
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

_STANDARD_AXIOMS = "[propext, Classical.choice, Quot.sound]"

# Uninterpreted functions mixed with linear real arithmetic. Each input is
# unsatisfiable and both cores certify all of them.
UFLRA_INPUTS = {
    # Congruence through a Real-valued function, then a Farkas step over the
    # two applications as opaque atoms.
    "uflra_real_function": """\
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-const x Real)
(declare-const y Real)
(assert (= x y))
(assert (< (f x) (f y)))
(check-sat)
""",
    # A function from the sort into Real.
    "uflra_sort_to_real": """\
(set-logic QF_UFLRA)
(declare-sort U 0)
(declare-fun g (U) Real)
(declare-fun h (Real) U)
(declare-const a U)
(declare-const b U)
(declare-const x Real)
(assert (= a b))
(assert (> (g a) (+ (g b) 1.0)))
(check-sat)
""",
    # A function from Real into the sort under a predicate; the equality of
    # the Real arguments is an implied equality of two bounds.
    "uflra_real_to_sort": """\
(set-logic QF_UFLRA)
(declare-sort U 0)
(declare-fun h (Real) U)
(declare-fun p (U) Bool)
(declare-const x Real)
(declare-const y Real)
(assert (<= x y))
(assert (>= x y))
(assert (p (h x)))
(assert (not (p (h y))))
(check-sat)
""",
    # A binary Real function under a disjunction: two congruences, one per case.
    "uflra_binary_split": """\
(set-logic QF_UFLRA)
(declare-fun f (Real Real) Real)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (or (= x y) (= x z)))
(assert (< (f x y) (f y y)))
(assert (< (f x z) (f z z)))
(check-sat)
""",
    # The implied equality x = y feeds the congruence (f x) = (f y), which
    # closes a Farkas combination with the bounds on the applications.
    "uflra_implied_equality": """\
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-const x Real)
(declare-const y Real)
(assert (<= (f x) 0.0))
(assert (>= (f y) 1.0))
(assert (<= (- x y) 0.0))
(assert (>= (- x y) 0.0))
(check-sat)
""",
    # Z3 rewrites the arguments (+ x 0.0) and (* 1.0 y) before logging, so
    # the assumed clauses are bridged to the assertions by rewrites.
    "uflra_rewritten_arguments": """\
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-const x Real)
(declare-const y Real)
(assert (<= (+ (f x) (f y)) 0.0))
(assert (>= (f (+ x 0.0)) 1.0))
(assert (>= (f (* 1.0 y)) 1.0))
(check-sat)
""",
    # A predicate over Real without any sort or Real-valued function still
    # runs the euf solver.
    "uflra_real_predicate": """\
(set-logic QF_UFLRA)
(declare-fun q (Real) Bool)
(declare-const x Real)
(declare-const y Real)
(assert (q x))
(assert (not (q y)))
(assert (<= x y))
(assert (<= y x))
(check-sat)
""",
    # A Real ite inside a function argument; Z3 decides this input before
    # search, so the log is empty and the refutation is one cnf lemma.
    "uflra_ite_argument": """\
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-const x Real)
(declare-const y Real)
(assert (< (f (ite (> x 0.0) x (- x))) (f 1.0)))
(assert (= x 1.0))
(check-sat)
""",
    # Arguments that are equal as linear forms but differ as terms, which
    # grind's congruence closure needs stated explicitly.
    "uflra_normalized_arguments": """\
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun q (Real) Bool)
(declare-const x Real)
(declare-const y Real)
(assert (q (f (- x y))))
(assert (or (not (q (f (+ x (* (- 1.0) y))))) (< (f (+ 2.0 2.0)) 4.0)))
(assert (>= (f 4.0) (f (- x x))))
(assert (= (f 0.0) 4.0))
(assert (>= y 0.0))
(assert (<= x (+ y 1.0)))
(check-sat)
""",
    # The same without the two bounds: y occurs in a single function argument,
    # which the frontend's elim-uncnstr tactic would replace by a fresh constant
    # (the exporters bypass the tactic preamble).
    "uflra_single_occurrence": """\
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun q (Real) Bool)
(declare-const x Real)
(declare-const y Real)
(assert (q (f (- x y))))
(assert (or (not (q (f (+ x (* (- 1.0) y))))) (< (f (+ 2.0 2.0)) 4.0)))
(assert (>= (f 4.0) (f (- x x))))
(assert (= (f 0.0) 4.0))
(check-sat)
""",
    # Real ite terms whose conditions are a Bool variable and a predicate:
    # no linear atom to key them by, so the argument helpers leave them as
    # opaque atoms and grind relates the two through (= p (q x)) alone.
    "uflra_opaque_ite_conditions": """\
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun q (Real) Bool)
(declare-const p Bool)
(declare-const x Real)
(declare-const y Real)
(assert (= (f (ite p x y)) 1.0))
(assert (= (f (ite (q x) x y)) 2.0))
(assert (= p (q x)))
(check-sat)
""",
    # A numeral quotient inside a ground atom next to a conflict at level
    # zero: the sat.smt arithmetic solver logs its division axiom
    # 2 * (1 / 2) = 1 under an arith hint whose first literal is the
    # constant true, which the clause log rejected before.
    "uflra_division_axiom": """\
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (< x x))
(assert (or (< y (f z)) (< (/ 1.0 2.0) 3.0)))
(check-sat)
""",
}

# A predicate over Bool alone applied to Real atoms: QF_UFLRA without a
# sort or a function over Real, so no euf hint mentions a Real term.
BOOL_PREDICATE_WITH_ARITHMETIC = """\
(set-logic QF_UFLRA)
(declare-fun r (Bool) Bool)
(declare-const x Real)
(declare-const y Real)
(assert (r (< x y)))
(assert (not (r (> y x))))
(check-sat)
"""


def random_instance(seed, variables=4, constraints=10, with_sort=False, depth=2):
    """A random QF_UFLRA instance, or None when it is satisfiable.

    Real variables, a unary and a binary Real function, a predicate over
    Real, and with_sort an uninterpreted sort with constants, functions in
    both directions, and a predicate over it.
    """
    rng = random.Random(seed)
    names = ["x%d" % i for i in range(variables)]
    lines = ["(set-logic QF_UFLRA)"]
    if with_sort:
        lines += ["(declare-sort U 0)", "(declare-fun a () U)", "(declare-fun b () U)",
                  "(declare-fun h (Real) U)", "(declare-fun g (U) Real)", "(declare-fun p (U) Bool)"]
    lines += ["(declare-fun %s () Real)" % n for n in names]
    lines += ["(declare-fun f (Real) Real)", "(declare-fun k (Real Real) Real)", "(declare-fun q (Real) Bool)"]

    def numeral():
        value = rng.choice([0, 1, 2, 3, "(/ 1.0 2.0)", "(/ 3.0 2.0)"])
        return "%d.0" % value if isinstance(value, int) else value

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
        if choice < 0.9:
            return "(+ %s %s)" % (term(d - 1), term(d - 1))
        return "(- %s %s)" % (term(d - 1), term(d - 1))

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


def _th_lemma_nodes(certificate):
    return [index for index, node in enumerate(certificate["nodes"])
            if certificate["declarations"][node["declaration"]]["name"] == "th-lemma"]


class TestMixedValidation(unittest.TestCase):
    """Certificate validation and Lean text generation, without running Lean."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")
        cls.source = UFLRA_INPUTS["uflra_sort_to_real"]
        cls.certificate = proof_certificate.export_clause_log_certificate(cls.source)

    def test_generated_lean_carries_the_valuation_and_the_interpretation(self):
        self.assertEqual(self.certificate["fragment"], "qf_uflra")
        text = proof_to_lean.reconstruct(self.source, self.certificate)
        self.assertIn("theorem unsat (_atoms : Nat -> Prop)" + proof_to_lean._UFLRA_BINDERS, text)
        self.assertIn("(_vars : Nat -> Rat)", proof_to_lean._UFLRA_BINDERS)
        self.assertIn(" (_m : Interpretation)", proof_to_lean._UFLRA_BINDERS)
        self.assertIn("\n  real : Rat -> U\n  rfuns : Nat -> List U -> Rat\n", text)
        self.assertIn('-- Element 0: "a"', text)
        self.assertIn('-- Real function 0: "g"', text)
        self.assertIn('-- Uninterpreted sort "U" is the type _m.U', text)
        self.assertIn("injected into _m.U by _m.real; functions with a Real result are the family _m.rfuns", text)
        self.assertIn(" : _m.U := _m.elems 0", text)
        self.assertIn(" : Rat := _m.rfuns 0 [(term_", text)
        self.assertNotIn(":= _m.funs ", text)  # h is declared but applied nowhere in this input
        self.assertIn("private theorem th_lemma_", text)
        self.assertNotIn("sorry", text)
        self.assertNotIn("axiom ", text)
        graph = proof_to_lean._validate_graph(self.source, self.certificate)
        self.assertEqual(graph.sorts, ("U",))
        self.assertTrue(graph.arithmetic)
        self.assertTrue(graph.uninterpreted)
        self.assertEqual(graph.fragment, "qf_uflra")
        self.assertEqual(graph.valuation, proof_to_lean._UFLRA_ARGUMENTS)
        hints = set()
        for node in _th_lemma_nodes(self.certificate):
            hints.add(graph.decl(node).parameters[0])
            proof_to_lean._check_th_lemma(graph, node)
            self.assertTrue(proof_to_lean._reachable(graph, graph.conclusion(node))[1])
        self.assertEqual(hints, {"farkas", "euf"})

    def test_real_arguments_are_injected_and_predicates_range_over_real(self):
        source = UFLRA_INPUTS["uflra_real_to_sort"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertIn('-- Function 0: "h"', text)
        self.assertIn('-- Predicate 0: "p"', text)
        self.assertIn(" : _m.U := _m.funs 0 [(_m.real (term_", text)
        self.assertIn(" : Prop := _m.preds 0 [(term_", text)
        self.assertNotIn("_m.rfuns 0", text.split("namespace", 1)[1])
        source = UFLRA_INPUTS["uflra_real_predicate"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertIn(" : Prop := _m.preds 0 [(_m.real (term_", text)
        self.assertNotIn("Uninterpreted sort", text)
        graph = proof_to_lean._validate_graph(source, certificate)
        self.assertEqual(graph.sorts, ())
        self.assertEqual(graph.fragment, "qf_uflra")

    def test_equal_linear_forms_of_arguments_are_stated_for_grind(self):
        # (f (- x y)) and (f (+ x (* -1 y))) are one term to Z3's rewriter and
        # two to grind's congruence closure; the lemma states their equality.
        source = UFLRA_INPUTS["uflra_normalized_arguments"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertRegex(text, r"have _r\d+_\d+ : .* = .* := by grind")
        graph = proof_to_lean._validate_graph(source, certificate)
        terms, tables = proof_to_lean._bind_input(source, graph, "qf_uflra")
        indices = {table: {decl: index for index, decl in enumerate(sorted(symbols.values()))}
                   for table, symbols in tables.items()}
        atom_indices = {**indices["atoms"], **indices["predicates"]}
        variable_indices = {**indices["variables"], **indices["numeric_functions"]}
        reachable = set(range(len(graph.nodes)))
        helpers = proof_to_lean._real_argument_helpers(graph, reachable, atom_indices, variable_indices)
        self.assertEqual(len(helpers), 3, helpers)  # x - y, 2 + 2 = 4, x - x = 0
        self.assertTrue(any("(_vars 0) - (_vars 1)" in h and "* (_vars 1)" in h for h in helpers), helpers)
        self.assertTrue(any("((4 : Rat))" in h for h in helpers), helpers)
        # Function applications are opaque atoms of the linear forms, keyed by
        # node in the atom-normalizing rewrite shape: a rewrite whose sides
        # apply f to different renderings of one argument ((f (+ 2.0 2.0))
        # against (f 4.0)) is left to grind, one whose sides share their
        # applications, or range over variables alone, is normalizable.
        verdicts = {}
        for node in range(len(graph.nodes)):
            if graph.kind(node) != z3.Z3_OP_PR_REWRITE:
                continue
            reachable, _ = proof_to_lean._reachable(graph, graph.conclusion(node))
            atoms = [formula for formula in sorted(reachable)
                     if graph.kind(formula) in (z3.Z3_OP_LE, z3.Z3_OP_GE, z3.Z3_OP_LT, z3.Z3_OP_GT, z3.Z3_OP_EQ)
                     and graph.arguments(formula) and graph.is_arith(graph.arguments(formula)[0])]
            if not atoms:
                continue
            applications = [{term for formula in proof_to_lean._reachable(graph, side)[0]
                             if graph.is_term(formula) for term in [formula]
                             if graph.kind(term) == z3.Z3_OP_UNINTERPRETED and graph.arguments(term)}
                            for side in graph.arguments(graph.conclusion(node))]
            verdicts[node] = (proof_to_lean._normalizable_rewrite(graph, node, reachable, atoms),
                              applications[0] == applications[1])
        self.assertEqual(set(verdicts.values()), {(False, False), (True, True)}, verdicts)

    def test_ite_arguments_are_keyed_up_to_normalization(self):
        # Z3 logs (f (ite (> x 0) x (- x))) with the ite in the rewriter's
        # normal form, (ite (<= x 0) (* -1 x) x); both ite terms get one key
        # (the non-strict condition, branches swapped), so the lemma states
        # their equality, which grind proves by splitting the conditions.
        source = UFLRA_INPUTS["uflra_ite_argument"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        graph = proof_to_lean._validate_graph(source, certificate)
        ites = [node for node in range(len(graph.nodes)) if graph.kind(node) == z3.Z3_OP_ITE]
        self.assertEqual(len(ites), 2)
        self.assertNotEqual(*(graph.arguments(node)[0] for node in ites))  # different conditions
        keys = {proof_to_lean._real_argument_key(graph, node) for node in ites}
        self.assertEqual(len(keys), 1)
        (((kind, condition, then_key, else_key), _),), constant = keys.pop()
        self.assertEqual((kind, condition[0], constant), ("ite", "<=", 0))
        self.assertNotEqual(then_key, else_key)
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertRegex(text, r"have _r\d+_\d+ : .*@ite Rat .* = .*@ite Rat .* := by grind")
        # A variable and an application are opaque atoms.
        opaque = [node for node in range(len(graph.nodes)) if graph.is_arith(node)
                  and graph.kind(node) == z3.Z3_OP_UNINTERPRETED]
        self.assertTrue(opaque)
        for node in opaque:
            self.assertEqual(proof_to_lean._real_atom_key(graph, node), ("atom", node))
        # So is an ite whose condition is no linear atom (a Bool variable, a
        # predicate): the two ite terms keep different keys and no helper
        # states their equality.
        source = UFLRA_INPUTS["uflra_opaque_ite_conditions"]
        for certificate in (proof_certificate.export_clause_log_certificate(source),
                            proof_certificate.export_certificate(source)):
            graph = proof_to_lean._validate_graph(source, certificate)
            ites = [node for node in range(len(graph.nodes)) if graph.kind(node) == z3.Z3_OP_ITE]
            self.assertEqual(len(ites), 2)
            for node in ites:
                self.assertEqual(graph.kind(graph.arguments(node)[0]), z3.Z3_OP_UNINTERPRETED)
                self.assertEqual(proof_to_lean._real_atom_key(graph, node), ("atom", node))
            self.assertEqual(len({proof_to_lean._real_argument_key(graph, node) for node in ites}), 2)
            self.assertNotIn("have _r", proof_to_lean.reconstruct(source, certificate))

    def test_fragment_consistency(self):
        for fragment, message in [("qf_uf", "qf_uf certificates cannot contain arithmetic"),
                                  ("propositional", "propositional certificates cannot contain arithmetic"),
                                  ("qf_lra", "only qf_uf, qf_uflra, and qf_uflia certificates")]:
            certificate = copy.deepcopy(self.certificate)
            certificate["fragment"] = fragment
            with self.subTest(fragment=fragment):
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, message):
                    proof_to_lean.reconstruct(self.source, certificate)
        # A pure QF_UF certificate relabeled qf_uflra has no arithmetic.
        from test_proof_to_lean_uf import UF_INPUTS
        source = UF_INPUTS["uf_congruence"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        certificate["fragment"] = "qf_uflra"
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "qf_uflra certificates must contain arithmetic"):
            proof_to_lean.reconstruct(source, certificate)
        # A pure QF_LRA certificate relabeled qf_uflra declares no uninterpreted function.
        from test_proof_to_lean_arith import Z3TEST_LRA_INPUTS
        source = Z3TEST_LRA_INPUTS["lra_farkas"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        certificate["fragment"] = "qf_uflra"
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "only qf_uf, qf_uflra, and qf_uflia certificates"):
            proof_to_lean.reconstruct(source, certificate)

    def test_malformed_mixed_declarations_are_rejected(self):
        certificate = copy.deepcopy(self.certificate)
        for declaration in certificate["declarations"]:
            if declaration["name"] == "g":
                declaration["domain"] = ["Real"]  # g takes the sort, not Real
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "wrong argument sort"):
            proof_to_lean.reconstruct(self.source, certificate)
        for domain, range_name, message in [
            (["Proof"], "Real", "unsupported arithmetic function declaration"),
            (["Proof"], "Bool", "unsupported predicate declaration"),
            (["BitVec"], "Bool", "invalid native declaration"),
            (["Real", "Proof"], "U", "unsupported uninterpreted-sort declaration"),
        ]:
            with self.subTest(domain=domain, range=range_name):
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, message):
                    proof_to_lean._declaration({"kind": z3.Z3_OP_UNINTERPRETED, "name": "w", "domain": domain,
                                                "range": range_name, "parameters": []}, ("U",))
        # A Real-valued function over the sort, Bool, and Real is a valid declaration.
        decl = proof_to_lean._declaration({"kind": z3.Z3_OP_UNINTERPRETED, "name": "w", "domain": ["U", "Bool", "Real"],
                                           "range": "Real", "parameters": []}, ("U",))
        self.assertEqual(decl.domain, ("U", "Bool", "Real"))

    def test_rebinding_to_another_signature_is_rejected(self):
        # The same assertion text with g declared over a second sort V and a
        # constant of that sort: the certificate's signatures no longer match.
        other = self.source.replace("(declare-fun g (U) Real)", "(declare-sort V 0)(declare-fun g (V) Real)")
        other = other.replace("(declare-const a U)", "(declare-const a V)").replace("(declare-const b U)", "(declare-const b V)")
        with self.assertRaises(proof_to_lean.ReconstructionError):
            proof_to_lean.reconstruct(other, self.certificate)


class TestMixedInProcess(unittest.TestCase):
    """Checks that need neither the z3 executable nor Lean (only the Python bindings)."""

    def test_numerals_as_arguments_have_distinct_normalizer_keys(self):
        context = z3.Context()
        q = z3.Function("q", z3.RealSort(context), z3.BoolSort(context))
        one, two = z3.RealVal(1, context), z3.RealVal(2, context)
        normalizer = proof_clause_log._Normalizer()
        self.assertNotEqual(normalizer.key(q(one)), normalizer.key(q(two)))
        self.assertEqual(normalizer.key(q(one)), normalizer.key(q(z3.RealVal("1.0", context))))
        self.assertNotEqual(normalizer.key(q(one)), normalizer.key(z3.Not(q(one))))

    def test_bool_only_predicates_with_arithmetic_export_through_both_cores(self):
        certificate = proof_certificate.export_clause_log_certificate(BOOL_PREDICATE_WITH_ARITHMETIC)
        self.assertEqual(certificate["fragment"], "qf_uflra")
        self.assertIn("th-lemma", certificate["rule_counts"])
        self.assertEqual({d["name"] for d in certificate["declarations"] if d["kind"] == z3.Z3_OP_UNINTERPRETED},
                         {"r", "x", "y"})
        text = proof_to_lean.reconstruct(BOOL_PREDICATE_WITH_ARITHMETIC, certificate)
        self.assertIn("No uninterpreted sort", text)
        self.assertIn(proof_to_lean._UFLRA_BINDERS, text)
        certificate = proof_certificate.export_certificate(BOOL_PREDICATE_WITH_ARITHMETIC)
        self.assertEqual(certificate["fragment"], "qf_uflra")
        text = proof_to_lean.reconstruct(BOOL_PREDICATE_WITH_ARITHMETIC, certificate)
        self.assertIn("(congrArg _m.bool (propext ", text)
        self.assertIn("No uninterpreted sort", text)


class _LeanIntegration(unittest.TestCase):
    core = "clause-log"

    def check(self, source):
        if self.core == "legacy":
            certificate = proof_certificate.export_certificate(source)
        else:
            certificate = proof_certificate.export_clause_log_certificate(source)
        self.assertEqual(certificate["fragment"], "qf_uflra")
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "checked.lean"
            proof_to_lean.check_and_write(source, certificate, output)
            text = output.read_text()
            namespace = "Z3Proofs.NativeCertificate.p" + hashlib.sha256(source.encode()).hexdigest()
            statement = text.split("theorem unsat", 1)[1].split(": False :=", 1)[0]
            self.assertEqual(statement.count("    (_h"), len(certificate["assertions"]))
            self.assertIn(proof_to_lean._UFLRA_BINDERS, statement)
            output.write_text(text + "\n#print axioms %s.unsat\n" % namespace)
            result = subprocess.run([str(proof_to_lean._CHECK_LEAN), str(output)],
                                    text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            report = " ".join(result.stdout.split())
            self.assertIn(".unsat' depends on axioms: " + _STANDARD_AXIOMS, report)
            return certificate, text


@unittest.skipUnless(_z3_available(), "the z3 executable is required for the clause log")
class TestMixedLeanIntegration(_LeanIntegration):
    """End-to-end: z3 clause log, certificate, Lean reconstruction, kernel check."""

    def test_documented_inputs_verify_under_the_standard_axioms(self):
        for name, source in UFLRA_INPUTS.items():
            with self.subTest(name=name):
                certificate, text = self.check(source)
                self.assertIn("th-lemma", certificate["rule_counts"])
                if name == "uflra_normalized_arguments":
                    self.assertIn("have _r", text)
                if name == "uflra_single_occurrence":
                    self.assertNotIn("!", json.dumps(certificate["declarations"]))
                if name == "uflra_division_axiom":
                    self.assertIn(["arith"], [d["parameters"] for d in certificate["declarations"]
                                              if d["name"] == "th-lemma"])

    def test_bool_only_predicate_over_real_atoms_verifies_through_the_clause_log(self):
        certificate, text = self.check(BOOL_PREDICATE_WITH_ARITHMETIC)
        self.assertIn("th-lemma", certificate["rule_counts"])
        self.assertIn("No uninterpreted sort", text)

    # Seeds of random_instance whose unsat core has at least three assertions
    # (plain) and the first two such seeds with an uninterpreted sort, pinned
    # so the checked inputs stay the same across Z3 versions; seed 137 (plain)
    # and 66 (sort) need the explicit equalities of Real arguments.
    PLAIN_SEEDS = (63, 160, 208)
    SORT_SEEDS = (79, 218)
    ARGUMENT_SEEDS = ((137, False), (66, True))

    def test_random_instances(self):
        for seed in self.PLAIN_SEEDS:
            source = random_instance(seed)
            with self.subTest(seed=seed):
                self.assertGreaterEqual(_unsat_core_size(source), 3, "re-pick seed %d" % seed)
                certificate, _ = self.check(source)
                self.assertIn("th-lemma", certificate["rule_counts"])
        for seed in self.SORT_SEEDS:
            source = random_instance(seed, with_sort=True)
            with self.subTest(seed=seed):
                self.assertGreaterEqual(_unsat_core_size(source), 3, "re-pick seed %d" % seed)
                self.check(source)
        for seed, with_sort in self.ARGUMENT_SEEDS:
            source = random_instance(seed, with_sort=with_sort)
            with self.subTest(seed=seed):
                _, text = self.check(source)
                self.assertIn("have _r", text)

    def test_small_chunks_cut_every_lemma_shape(self):
        with patch.object(proof_to_lean, "_OUTLINE_PROOF_STEPS", 0), \
                patch.object(proof_to_lean, "_OUTLINE_CHUNK_STEPS", 3):
            source = UFLRA_INPUTS["uflra_binary_split"]
            certificate, text = self.check(source)
            sizes = outlined_lemma_sizes(text)
            self.assertGreater(len(sizes), 1)
            self.assertLessEqual(max(sizes), 3)
            self.assertEqual(sum(sizes), _proof_steps(certificate))


class TestLegacyMixedLeanIntegration(_LeanIntegration):
    """End-to-end through the smt core's proof object."""
    core = "legacy"

    def test_documented_inputs_verify_through_the_legacy_core(self):
        for name, source in UFLRA_INPUTS.items():
            with self.subTest(name=name):
                certificate, text = self.check(source)
                self.assertIn("monotonicity", certificate["rule_counts"])
                if name == "uflra_real_function":
                    # Congruence through a Real argument injects it by _m.real.
                    self.assertIn("(congrArg (_m.rfuns 0) (congr (congrArg List.cons (congrArg _m.real ", text)
                if name == "uflra_real_to_sort":
                    # theory_lra propagates x = y from the two bounds for the
                    # congruence (h x) = (h y): the legacy implied-eq shape,
                    # stated as the implication from its premises.
                    hints = {certificate["declarations"][node["declaration"]]["parameters"][0]
                             for node in certificate["nodes"]
                             if certificate["declarations"][node["declaration"]]["name"] == "th-lemma"}
                    self.assertIn("implied-eq", hints)
                    self.assertRegex(text, r"private theorem th_lemma_\d+ .*\n    : \(formula_\d+ [^)]*\) -> \(formula_\d+ [^)]*\) -> \(formula_\d+ [^)]*\) := by")
        certificate, text = self.check(BOOL_PREDICATE_WITH_ARITHMETIC)
        self.assertIn("monotonicity", certificate["rule_counts"])
        self.assertNotIn("th-lemma", certificate["rule_counts"])
        self.assertIn("(congrArg _m.bool (propext ", text)

    def test_random_instances_through_the_legacy_core(self):
        for seed, with_sort in ((63, False), (79, True)):
            source = random_instance(seed, with_sort=with_sort)
            with self.subTest(seed=seed):
                certificate, _ = self.check(source)
                self.assertIn("monotonicity", certificate["rule_counts"])


if __name__ == "__main__":
    unittest.main()
