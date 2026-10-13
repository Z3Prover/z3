############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Tests for the QF_UF slice of the Lean reconstruction: validation without
# Lean, and end-to-end checks that need the z3 executable and the pinned
# Lean toolchain.
############################################
import copy
import hashlib
import json
from pathlib import Path
import random
import re
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

_STANDARD_AXIOMS = "[propext, Classical.choice, Quot.sound]"

# Quantifier-free uninterpreted functions over one sort: congruence through
# functions and predicates, an equality diamond, a cyclic function chain with
# distinct, and a chained equality (the shape of z3test regression 3732).
UF_INPUTS = {
    "uf_congruence": """\
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun f (U) U)
(declare-fun g (U U) U)
(declare-fun p (U) Bool)
(assert (= a b))
(assert (or (not (= (f a) (f b))) (p (g a c))))
(assert (not (p (g b c))))
(check-sat)
""",
    "uf_diamond": """\
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun x0 () U)
(declare-fun x1 () U)
(declare-fun x2 () U)
(declare-fun y0 () U)
(declare-fun y1 () U)
(declare-fun z0 () U)
(declare-fun z1 () U)
(assert (or (and (= x0 y0) (= y0 x1)) (and (= x0 z0) (= z0 x1))))
(assert (or (and (= x1 y1) (= y1 x2)) (and (= x1 z1) (= z1 x2))))
(assert (not (= x0 x2)))
(check-sat)
""",
    "uf_cycle_distinct": """\
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun f (U) U)
(declare-fun p (U) Bool)
(declare-fun q () Bool)
(assert (= (f (f (f a))) a))
(assert (= (f (f (f (f (f a))))) a))
(assert (or q (not (= (f a) a))))
(assert (=> q (p a)))
(assert (=> q (not (p (f a)))))
(assert (or (not q) (distinct a b (f b))))
(check-sat)
""",
    "uf_chained_equality": """\
(declare-sort a)
(declare-fun b (a a) a)
(declare-fun c () a)
(declare-fun d () a)
(declare-fun e () a)
(declare-fun f () a)
(assert (= e d (b e c) f))
(assert (distinct f (b d c)))
(check-sat)
""",
    # ite over the sort: as an equality side, nested, under a function, inside
    # distinct and a predicate, with constants, equalities, and predicates as conditions.
    "uf_ite": """\
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun p (U) Bool)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-const q Bool)
(assert (= c (ite q a b)))
(assert (or (not q) (p (ite q a c))))
(assert (not (p a)))
(assert (or q (distinct (f (ite (p a) b c)) (f b) (f a))))
(check-sat)
""",
    # Z3 internalizes the distinct after asserting q, so its alldiff clauses
    # mention a instead of the ite; the replay ties them to the distinct and q
    # together with a cnf lemma.
    "uf_ite_alldiff": """\
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun g (U U) U)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-const q Bool)
(assert q)
(assert (= c a))
(assert (distinct (g c a) (ite (not q) b a) c))
(check-sat)
""",
    # Two uninterpreted sorts: functions between them, a predicate over one,
    # and congruence through a function whose arguments mix both sorts.
    "uf_two_sorts": """\
(set-logic QF_UF)
(declare-sort A 0)
(declare-sort B 0)
(declare-fun a1 () A)
(declare-fun a2 () A)
(declare-fun b () B)
(declare-fun f (A) B)
(declare-fun g (B A) A)
(declare-fun p (B) Bool)
(declare-const q Bool)
(assert (= (f a1) b))
(assert (or q (= (f a2) b)))
(assert (not q))
(assert (or (not (= (f a1) (f a2))) (p (f (g b a1)))))
(assert (not (p (f (g (f a1) a1)))))
(check-sat)
""",
    # Two sorts with distinct over one, an ite over the other whose condition
    # is an equality of the first, and a predicate taking one argument of each.
    "uf_two_sorts_ite_distinct": """\
(set-logic QF_UF)
(declare-sort A 0)
(declare-sort B 0)
(declare-fun a1 () A)
(declare-fun a2 () A)
(declare-fun b1 () B)
(declare-fun b2 () B)
(declare-fun f (A) B)
(declare-fun r (A B) Bool)
(assert (distinct b1 b2 (f a2)))
(assert (or (r a1 b1) (= (f (ite (= b1 b2) a1 a2)) b2)))
(assert (=> (r a1 b1) (r a2 (f a1))))
(assert (not (r a2 (f a1))))
(check-sat)
""",
    # Bool arguments and results: a function and a predicate over Bool, a
    # function and a predicate mixing Bool with the sort, with Boolean
    # variables, a conjunction, a predicate application, and an equality (in
    # both orientations) as arguments, all decided during search.
    "uf_bool_args": """\
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun f (Bool) U)
(declare-fun g (U Bool) U)
(declare-fun p (Bool) Bool)
(declare-fun r (Bool U) Bool)
(declare-const q Bool)
(declare-const s Bool)
(assert (or s q))
(assert (or (not s) q))
(assert (= (f q) (g a (and q s))))
(assert (or (not (= (f true) (g a s))) (r (= a b) (f (p q)))))
(assert (not (r (= b a) (f (p true)))))
(check-sat)
""",
    # Bool arguments fixed at level 0: Z3 internalizes (f q) and (r s b) with
    # the units substituted, assumes its true literal, and logs its internal
    # true variable as the phantom constant k!0; t is decided during search.
    # No set-logic line: with (set-logic QF_UF) the sat.smt core logs no
    # phantom for this input, and the live test below checks the raw log.
    "uf_bool_args_units": """\
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun f (Bool) U)
(declare-fun r (Bool U) Bool)
(declare-const q Bool)
(declare-const s Bool)
(declare-const t Bool)
(declare-const u Bool)
(assert q)
(assert (not s))
(assert (or u t))
(assert (or (not u) t))
(assert (= (f q) a))
(assert (r s b))
(assert (or (not (r false b)) (not (= (f t) a))))
(check-sat)
""",
}


def random_bool_argument_instance(seed, constants=3, constraints=14, depth=2):
    """A random QF_UF problem whose functions and predicates take Bool arguments.

    Conditions (Boolean variables, constants, equalities, predicate
    applications, and a predicate over Bool) appear as arguments of a
    function over Bool, a function mixing the sort with Bool, and a predicate
    mixing Bool with the sort; callers filter for unsat instances.
    """
    generator = random.Random(seed)
    lines = ["(set-logic QF_UF)", "(declare-sort U 0)"]
    lines += ["(declare-fun c%d () U)" % i for i in range(constants)]
    lines += ["(declare-fun f (U) U)", "(declare-fun h (Bool) U)", "(declare-fun g (U Bool) U)",
              "(declare-fun p (U) Bool)", "(declare-fun pb (Bool) Bool)", "(declare-fun r (Bool U) Bool)",
              "(declare-const q Bool)", "(declare-const s Bool)"]

    def condition(d):
        roll = generator.random()
        if roll < 0.3:
            return generator.choice(["q", "(not q)", "s", "(not s)", "true", "false"])
        if roll < 0.6:
            return "(= %s %s)" % (term(d), term(d))
        if roll < 0.8:
            return "(p %s)" % term(d)
        if d > 0:
            return "(pb %s)" % condition(d - 1)
        return "q"

    def term(d):
        roll = generator.random()
        if d == 0 or roll < 0.35:
            return "c%d" % generator.randrange(constants)
        if roll < 0.55:
            return "(f %s)" % term(d - 1)
        if roll < 0.8:
            return "(h %s)" % condition(d - 1)
        return "(g %s %s)" % (term(d - 1), condition(d - 1))

    def atom():
        roll = generator.random()
        if roll < 0.45:
            return "(= %s %s)" % (term(depth), term(depth))
        if roll < 0.6:
            return "(p %s)" % term(depth)
        if roll < 0.8:
            return "(r %s %s)" % (condition(depth - 1), term(depth))
        if roll < 0.9:
            return "(pb %s)" % condition(depth - 1)
        return generator.choice(["q", "s"])

    def literal():
        formula = atom()
        return formula if generator.random() < 0.5 else "(not %s)" % formula

    for _ in range(constraints):
        roll = generator.random()
        if roll < 0.35:
            lines.append("(assert (or %s %s))" % (literal(), literal()))
        elif roll < 0.5:
            lines.append("(assert (=> %s %s))" % (literal(), literal()))
        elif roll < 0.6:
            lines.append("(assert (and %s %s))" % (literal(), literal()))
        elif roll < 0.7:
            lines.append("(assert (= %s %s))" % (literal(), literal()))
        else:
            lines.append("(assert %s)" % literal())
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


def random_sorted_instance(seed, sorts=3, constants=2, constraints=16, depth=2, ite=0.3):
    """A random QF_UF problem over several sorts; callers filter for unsat ones.

    Every sort has constants, a unary function from every sort (itself
    included), a binary function from its two neighbouring sorts, and a
    predicate; one predicate takes the first and the last sort. Terms are
    generated by sort, so every input is well-sorted.
    """
    generator = random.Random(seed)
    names = ["S%d" % i for i in range(sorts)]
    lines = ["(set-logic QF_UF)"] + ["(declare-sort %s 0)" % name for name in names]
    elements = {name: ["%s_c%d" % (name.lower(), i) for i in range(constants)] for name in names}
    for name in names:
        lines += ["(declare-fun %s () %s)" % (element, name) for element in elements[name]]
    unary = {(src, dst): "f_%s_%s" % (src.lower(), dst.lower()) for src in names for dst in names}
    lines += ["(declare-fun %s (%s) %s)" % (f, src, dst) for (src, dst), f in unary.items()]
    binary = {dst: ("g_%s" % dst.lower(), names[i - 1], names[(i + 1) % sorts]) for i, dst in enumerate(names)}
    lines += ["(declare-fun %s (%s %s) %s)" % (g, left, right, dst) for dst, (g, left, right) in binary.items()]
    lines += ["(declare-fun p_%s (%s) Bool)" % (name.lower(), name) for name in names]
    lines += ["(declare-fun r (%s %s) Bool)" % (names[0], names[-1]), "(declare-const q Bool)"]

    def condition(d):
        roll = generator.random()
        if roll < 0.3:
            return "q" if roll < 0.15 else "(not q)"
        sort = generator.choice(names)
        if roll < 0.7:
            return "(= %s %s)" % (term(d, sort), term(d, sort))
        return "(p_%s %s)" % (sort.lower(), term(d, sort))

    def term(d, sort):
        if d > 0 and ite and generator.random() < ite:
            return "(ite %s %s %s)" % (condition(d - 1), term(d - 1, sort), term(d - 1, sort))
        roll = generator.random()
        if d == 0 or roll < 0.4:
            return generator.choice(elements[sort])
        if roll < 0.75:
            src = generator.choice(names)
            return "(%s %s)" % (unary[(src, sort)], term(d - 1, src))
        g, left, right = binary[sort]
        return "(%s %s %s)" % (g, term(d - 1, left), term(d - 1, right))

    def atom():
        roll = generator.random()
        sort = generator.choice(names)
        if roll < 0.55:
            return "(= %s %s)" % (term(depth, sort), term(depth, sort))
        if roll < 0.75:
            return "(p_%s %s)" % (sort.lower(), term(depth, sort))
        if roll < 0.85:
            return "(r %s %s)" % (term(depth, names[0]), term(depth, names[-1]))
        if roll < 0.9:
            return "q"
        return "(distinct %s %s %s)" % (term(1, sort), term(1, sort), term(1, sort))

    def literal():
        formula = atom()
        return formula if generator.random() < 0.5 else "(not %s)" % formula

    for _ in range(constraints):
        roll = generator.random()
        if roll < 0.35:
            lines.append("(assert (or %s %s))" % (literal(), literal()))
        elif roll < 0.5:
            lines.append("(assert (=> %s %s))" % (literal(), literal()))
        elif roll < 0.6:
            lines.append("(assert (and %s %s))" % (literal(), literal()))
        elif roll < 0.7:
            lines.append("(assert (= %s %s))" % (literal(), literal()))
        else:
            lines.append("(assert %s)" % literal())
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


def random_instance(seed, constants=5, constraints=14, depth=2, ite=0.0):
    """A random QF_UF problem with Boolean structure; callers filter for unsat ones.

    With a positive ite probability, that share of the compound terms are ite
    terms over the sort, under equality, predicate, and Boolean-variable
    conditions.
    """
    generator = random.Random(seed)
    lines = ["(set-logic QF_UF)", "(declare-sort U 0)"]
    lines += ["(declare-fun c%d () U)" % i for i in range(constants)]
    lines += ["(declare-fun f (U) U)", "(declare-fun g (U U) U)", "(declare-fun p (U) Bool)",
              "(declare-const q Bool)"]

    def condition(d):
        roll = generator.random()
        if roll < 0.3:
            return "q" if roll < 0.15 else "(not q)"
        if roll < 0.7:
            return "(= %s %s)" % (term(d), term(d))
        return "(p %s)" % term(d)

    def term(d):
        if d > 0 and ite and generator.random() < ite:
            return "(ite %s %s %s)" % (condition(d - 1), term(d - 1), term(d - 1))
        roll = generator.random()
        if d == 0 or roll < 0.4:
            return "c%d" % generator.randrange(constants)
        if roll < 0.75:
            return "(f %s)" % term(d - 1)
        return "(g %s %s)" % (term(d - 1), term(d - 1))

    def atom():
        roll = generator.random()
        if roll < 0.6:
            return "(= %s %s)" % (term(depth), term(depth))
        if roll < 0.8:
            return "(p %s)" % term(depth)
        if roll < 0.9:
            return "q"
        return "(distinct %s %s %s)" % (term(1), term(1), term(1))

    def literal():
        formula = atom()
        return formula if generator.random() < 0.5 else "(not %s)" % formula

    for _ in range(constraints):
        roll = generator.random()
        if roll < 0.35:
            lines.append("(assert (or %s %s))" % (literal(), literal()))
        elif roll < 0.5:
            lines.append("(assert (=> %s %s))" % (literal(), literal()))
        elif roll < 0.6:
            lines.append("(assert (and %s %s))" % (literal(), literal()))
        elif roll < 0.7:
            lines.append("(assert (= %s %s))" % (literal(), literal()))
        else:
            lines.append("(assert %s)" % literal())
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


def equality_diamond(levels):
    """A chain of equality diamonds: x_i = x_{i+1} through y_i or through z_i.

    Z3's refutation grows exponentially with the number of levels, so a few
    levels give a refutation far longer than the outlining threshold.
    """
    lines = ["(set-logic QF_UF)", "(declare-sort U 0)"]
    lines += ["(declare-fun x%d () U)" % i for i in range(levels + 1)]
    lines += ["(declare-fun y%d () U)" % i for i in range(levels)]
    lines += ["(declare-fun z%d () U)" % i for i in range(levels)]
    for i in range(levels):
        lines.append("(assert (or (and (= x%d y%d) (= y%d x%d)) (and (= x%d z%d) (= z%d x%d))))" % (
            i, i, i, i + 1, i, i, i, i + 1))
    lines.append("(assert (not (= x0 x%d)))" % levels)
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


def outlined_lemma_sizes(text):
    """Proof steps defined inside each outlined lemma (bindings of other lemmas carry no type)."""
    return [len(re.findall(r"^  let _step_\d+ (?!:=)", block, re.MULTILINE))
            for block in text.split("private theorem proof_step_")[1:]]


def _proof_steps(certificate):
    """Proof steps reachable from the root; unused gate clauses are still checked as lemmas."""
    reachable, pending = set(), [certificate["proof"]]
    while pending:
        node = pending.pop()
        if node not in reachable:
            reachable.add(node)
            pending.extend(certificate["nodes"][node]["arguments"][:-1])
    return len(reachable)


def _unsat_core_size(source):
    """The size of an unsat core over the assertions, or 0 for a satisfiable input."""
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    assertions = z3.parse_smt2_string(source, ctx=context)
    tracking = [z3.Bool("_track%d" % index, context) for index in range(len(assertions))]
    for literal, assertion in zip(tracking, assertions):
        solver.assert_and_track(assertion, literal)
    return len(solver.unsat_core()) if solver.check() == z3.unsat else 0


def _z3_available():
    try:
        return subprocess.run([proof_certificate.default_z3_executable(), "--version"],
                              capture_output=True).returncode == 0
    except OSError:
        return False


def _th_lemma_nodes(certificate):
    return [index for index, node in enumerate(certificate["nodes"])
            if certificate["declarations"][node["declaration"]]["name"] == "th-lemma"]


def _declarations(certificate, predicate):
    return [declaration for declaration in certificate["declarations"] if predicate(declaration)]


class TestUninterpretedValidation(unittest.TestCase):
    """Certificate validation and Lean text generation, without running Lean."""

    @classmethod
    def setUpClass(cls):
        if not _z3_available():
            raise unittest.SkipTest("the z3 executable is required for the clause log")
        cls.source = UF_INPUTS["uf_congruence"]
        cls.certificate = proof_certificate.export_clause_log_certificate(cls.source)

    def test_generated_lean_quantifies_over_an_uninterpreted_interpretation(self):
        text = proof_to_lean.reconstruct(self.source, self.certificate)
        self.assertIn("theorem unsat (_atoms : Nat -> Prop)" + proof_to_lean._UF_BINDERS, text)
        self.assertIn('-- Element 0: "a"', text)
        self.assertIn('-- Function 0: "f"', text)
        self.assertIn('-- Function 1: "g"', text)
        self.assertIn('-- Predicate 0: "p"', text)
        self.assertIn('-- Uninterpreted sort "U" is the type _U', text)
        self.assertIn(" : _U := _elems 0", text)
        self.assertIn(" : _U := _funs 0 [(term_", text)
        self.assertIn(" : _U := _funs 1 [(term_", text)
        self.assertIn(" : Prop := _preds 0 [(term_", text)
        self.assertIn("private theorem th_lemma_", text)
        self.assertIn("  grind", text)
        # No arithmetic: no Rat valuation and none of the arithmetic grind helpers.
        self.assertNotIn("_vars", text)
        self.assertNotIn("Rat", text)
        self.assertNotIn("have _s", text)
        self.assertNotIn("have _g", text)
        self.assertNotIn("sorry", text)
        self.assertNotIn("axiom ", text)
        graph = proof_to_lean._validate_graph(self.source, self.certificate)
        self.assertEqual(graph.sorts, ("U",))
        self.assertFalse(graph.arithmetic)
        for node in _th_lemma_nodes(self.certificate):
            self.assertEqual(graph.decl(node).parameters, ("euf",))
            proof_to_lean._check_th_lemma(graph, node)
            self.assertTrue(proof_to_lean._reachable(graph, graph.conclusion(node))[1])

    def test_fragment_and_sort_consistency(self):
        for fragment in ("propositional", "qf_lra"):
            certificate = copy.deepcopy(self.certificate)
            certificate["fragment"] = fragment
            with self.subTest(fragment=fragment):
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "only qf_uf certificates"):
                    proof_to_lean.reconstruct(self.source, certificate)
        # A Boolean certificate claiming qf_uf has no sort to declare.
        boolean = proof_certificate.export_certificate("(declare-const p Bool)(assert p)(assert (not p))")
        boolean["fragment"] = "qf_uf"
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "only qf_uf certificates"):
            proof_to_lean.reconstruct("(declare-const p Bool)(assert p)(assert (not p))", boolean)

        def rename_sort(certificate, new_name, only_first=False):
            for declaration in certificate["declarations"]:
                changed = False
                if declaration["range"] == "U":
                    declaration["range"], changed = new_name, True
                if "U" in declaration["domain"]:
                    declaration["domain"] = [new_name if sort == "U" else sort for sort in declaration["domain"]]
                    changed = True
                if changed and only_first:
                    return

        # The certificate's sort names must be the input's; renaming the sort of
        # one declaration leaves the proof graph ill-sorted.
        renamed = copy.deepcopy(self.certificate)
        rename_sort(renamed, "V")
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "sort does not match the original input"):
            proof_to_lean.reconstruct(self.source, renamed)
        renamed = copy.deepcopy(self.certificate)
        rename_sort(renamed, "V", only_first=True)
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "wrong argument sort"):
            proof_to_lean.reconstruct(self.source, renamed)
        for reserved in ("Real", "Proof", ""):
            renamed = copy.deepcopy(self.certificate)
            rename_sort(renamed, reserved)
            with self.subTest(reserved=reserved):
                with self.assertRaises(proof_to_lean.ReconstructionError):
                    proof_to_lean.reconstruct(self.source, renamed)
        # Renaming a symbol breaks the binding even when the source text is updated.
        source = self.source.replace("(declare-fun c () U)", "(declare-fun d () U)").replace(" c)", " d)")
        certificate = copy.deepcopy(self.certificate)
        certificate["source_smt2"] = source
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "do not match the original input"):
            proof_to_lean.reconstruct(source, certificate)

    def test_malformed_uninterpreted_declarations_are_rejected(self):
        def mutate(predicate, **changes):
            certificate = copy.deepcopy(self.certificate)
            for declaration in _declarations(certificate, predicate):
                declaration.update(changes)
            return certificate

        is_f = lambda d: d["name"] == "f" and d["kind"] == z3.Z3_OP_UNINTERPRETED
        is_p = lambda d: d["name"] == "p" and d["kind"] == z3.Z3_OP_UNINTERPRETED
        is_eq = lambda d: d["kind"] == z3.Z3_OP_EQ and d["domain"] == ["U", "U"]
        for certificate, message in [
            (mutate(is_f, domain=["Bool"]), "wrong argument sort"),  # f is applied to an element
            (mutate(is_f, domain=["Real"]), "unsupported uninterpreted-sort declaration"),
            (mutate(is_f, kind=z3.Z3_OP_ITE, name="if", domain=["U", "U", "U"]), "invalid uninterpreted-sort ite"),
            (mutate(is_f, kind=z3.Z3_OP_ITE, name="ite", domain=["Bool", "U", "U"]), "invalid uninterpreted-sort ite"),
            (mutate(is_f, kind=z3.Z3_OP_ITE, name="if", domain=["Bool", "U", "U"]), "wrong number of arguments"),
            (mutate(is_f, kind=z3.Z3_OP_ADD, name="+", domain=["U", "U"]), "unsupported uninterpreted-sort"),
            (mutate(is_p, domain=["Bool"]), "wrong argument sort"),  # p is applied to an element
            (mutate(is_p, domain=["Real"]), "unsupported predicate declaration"),
            (mutate(is_p, domain=["U", "U"]), "wrong number of arguments"),
            (mutate(is_eq, domain=["U", "Bool"]), "cannot mix argument sorts"),
            (mutate(is_eq, domain=["Bool", "Bool"]), "wrong argument sort"),
            (mutate(is_f, range="Bool"), "wrong argument sort"),
            (mutate(is_eq, domain=["Proof", "Proof"]), "cannot mix argument sorts"),
        ]:
            with self.subTest(message=message):
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, message):
                    proof_to_lean.reconstruct(self.source, certificate)
        # A function applied to a formula instead of an element.
        certificate = copy.deepcopy(self.certificate)
        graph = proof_to_lean._validate_graph(self.source, certificate)
        application = next(i for i in range(len(graph.nodes)) if graph.decl(i).name == "f")
        formula = next(i for i in range(len(graph.nodes)) if graph.kind(i) == z3.Z3_OP_EQ)
        certificate["nodes"][application]["arguments"] = [formula]
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "wrong argument sort"):
            proof_to_lean.reconstruct(self.source, certificate)
        # An equality over proof terms is a malformed declaration, not an internal error.
        certificate = copy.deepcopy(self.certificate)
        certificate["declarations"].append({"kind": z3.Z3_OP_EQ, "name": "=", "domain": ["Proof", "Proof"],
                                            "range": "Bool", "parameters": []})
        proofs = [i for i, raw in enumerate(certificate["nodes"])
                  if certificate["declarations"][raw["declaration"]]["range"] == "Proof"]
        certificate["nodes"].append({"declaration": len(certificate["declarations"]) - 1,
                                     "arguments": proofs[:1] * 2})
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "cannot mix argument sorts"):
            proof_to_lean.reconstruct(self.source, certificate)

    def test_ite_over_the_sort_is_classical_ite_with_gate_lemmas(self):
        source = UF_INPUTS["uf_ite"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        self.assertEqual(certificate["fragment"], "qf_uf")
        graph = proof_to_lean._validate_graph(source, certificate)
        ites = [node for node in range(len(graph.nodes)) if graph.kind(node) == z3.Z3_OP_ITE]
        self.assertEqual(len(ites), 3)
        self.assertEqual({graph.decl(node).domain for node in ites}, {("Bool", "U", "U")})
        text = proof_to_lean.reconstruct(source, certificate)
        # Every ite term is Lean's ite over _U with the classical instance, so its
        # definition and the definitions containing it are noncomputable.
        for node in ites:
            self.assertIn("noncomputable def term_%d " % node, text)
            self.assertIn(": _U := (@ite _U (formula_%d _atoms%s) (Classical.propDecidable _) " % (
                graph.arguments(node)[0], proof_to_lean._UF_ARGUMENTS), text)
        containing = [node for node in range(len(graph.nodes))
                      if graph.is_term(node) and graph.kind(node) != z3.Z3_OP_ITE
                      and any(arg in ites for arg in graph.arguments(node))]
        self.assertTrue(containing)
        for node in containing:
            self.assertIn("noncomputable def term_%d " % node, text)
        self.assertNotIn("Rat", text)
        # The gate clauses are def-axiom nodes proved by splitting on the condition.
        self.assertGreaterEqual(certificate["rule_counts"]["def-axiom"], 2)
        self.assertIn("(ite_eq_left _hc)", text)
        self.assertIn("(ite_eq_right _hnc)", text)
        self.assertNotIn("have _g", text)  # no arithmetic branch helpers
        # A gate clause naming the wrong branch is rejected before Lean runs.
        gate = next(node for node in range(len(graph.nodes)) if graph.kind(node) == z3.Z3_OP_PR_DEF_AXIOM
                    and any(graph.kind(lit) == z3.Z3_OP_EQ for lit in graph.clause(graph.conclusion(node))))
        clause = graph.clause(graph.conclusion(gate))
        equality = next(lit for lit in clause if graph.kind(lit) == z3.Z3_OP_EQ)
        left, right = graph.arguments(equality)
        ite = left if graph.kind(left) == z3.Z3_OP_ITE else right
        branch = right if ite == left else left
        condition, then_branch, else_branch = graph.arguments(ite)
        other = else_branch if branch == then_branch else then_branch
        tampered = copy.deepcopy(certificate)
        tampered["nodes"][equality]["arguments"] = [ite if arg == ite else other for arg in (left, right)]
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "invalid def-axiom clause"):
            proof_to_lean.reconstruct(source, tampered)

    def test_alldiff_clauses_simplified_under_a_unit_get_a_cnf_lemma(self):
        source = UF_INPUTS["uf_ite_alldiff"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        graph = proof_to_lean._validate_graph(source, certificate)
        cnf = [node for node in _th_lemma_nodes(certificate) if graph.decl(node).parameters == ("cnf",)]
        self.assertTrue(cnf)
        for node in cnf:
            # The lemma is over the implying assertions only, never all of them.
            literals = graph.clause(graph.conclusion(node))
            self.assertLess(len(literals), len(graph.assertions) + 1)
        proof_to_lean.reconstruct(source, certificate)

    def test_boolean_arguments_are_injected_into_the_carrier(self):
        source = UF_INPUTS["uf_bool_args"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        self.assertEqual(certificate["fragment"], "qf_uf")
        signatures = {(d["name"], tuple(d["domain"]), d["range"]) for d in certificate["declarations"]
                      if d["kind"] == z3.Z3_OP_UNINTERPRETED and d["domain"]}
        self.assertEqual(signatures, {("f", ("Bool",), "U"), ("g", ("U", "Bool"), "U"),
                                      ("p", ("Bool",), "Bool"), ("r", ("Bool", "U"), "Bool")})
        graph = proof_to_lean._validate_graph(source, certificate)
        self.assertEqual(graph.sorts, ("U",))
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertIn("(_bool : Prop -> _U)", proof_to_lean._UF_BINDERS)
        self.assertIn("theorem unsat (_atoms : Nat -> Prop)" + proof_to_lean._UF_BINDERS, text)
        self.assertIn("-- Boolean arguments of functions and predicates are injected into _U by _bool.", text)
        # Every Boolean argument is rendered as _bool applied to its formula, in
        # the argument position its declaration gives it.
        applications = [node for node in range(len(graph.nodes))
                        if graph.kind(node) == z3.Z3_OP_UNINTERPRETED and "Bool" in graph.decl(node).domain]
        self.assertTrue(applications)
        for node in applications:
            decl = graph.decl(node)
            expected = ", ".join(
                "(_bool (formula_%d _atoms%s))" % (arg, proof_to_lean._UF_ARGUMENTS) if sort == "Bool"
                else "(term_%d _atoms%s)" % (arg, proof_to_lean._UF_ARGUMENTS)
                for arg, sort in zip(graph.arguments(node), decl.domain))
            family = "_funs" if decl.range == "U" else "_preds"
            self.assertRegex(text, r"%s \d+ \[%s\]" % (family, re.escape(expected)))
        self.assertNotIn("_bool True", text)   # true and false are formulas like any other
        self.assertIn("(_bool (formula_", text)
        self.assertNotIn("Rat", text)
        # Every grind lemma offers the two cases of each Boolean argument it
        # reaches, since Z3's egraph assigns every such argument true or false.
        lemmas = [block for block in text.split("\nprivate theorem ")[1:] if "grind" in block]
        self.assertTrue(lemmas)
        for block in lemmas:
            unfolded = set(re.search(r"\n  unfold (.*)\n", block).group(1).split())
            expected = {arg for node in applications
                        if ("term_%d" if graph.is_term(node) else "formula_%d") % node in unfolded
                        for arg, sort in zip(graph.arguments(node), graph.decl(node).domain)
                        if sort == "Bool" and graph.kind(arg) not in (z3.Z3_OP_TRUE, z3.Z3_OP_FALSE)}
            found = {int(name) for name in re.findall(r"have _b(\d+) : Or \(", block)}
            self.assertEqual(found, expected, block[:200])
        # A Bool argument position is checked like any other: swapping the
        # arguments of r, or declaring f over the sort, leaves the graph ill-sorted.
        r = next(node for node in applications if graph.decl(node).name == "r")
        tampered = copy.deepcopy(certificate)
        tampered["nodes"][r]["arguments"] = list(reversed(tampered["nodes"][r]["arguments"]))
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "wrong argument sort"):
            proof_to_lean.reconstruct(source, tampered)
        tampered = copy.deepcopy(certificate)
        for declaration in _declarations(tampered, lambda d: d["name"] == "f" and d["kind"] == z3.Z3_OP_UNINTERPRETED):
            declaration["domain"] = ["U"]
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "wrong argument sort"):
            proof_to_lean.reconstruct(source, tampered)
        # The binder requires the input's signature: a certificate for the same
        # text with f declared over the sort cannot be bound to this input.
        rebound = source.replace("(declare-fun f (Bool) U)", "(declare-fun f (U) U)")
        for application, replacement in (("(f q)", "(f a)"), ("(f true)", "(f a)"),
                                         ("(f (p q))", "(f b)"), ("(f (p true))", "(f b)")):
            rebound = rebound.replace(application, replacement)
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "do not match the original input"):
            proof_to_lean.reconstruct(rebound, dict(certificate, source_smt2=rebound))
        # A predicate over Bool alone needs the sort: without it the exporter
        # rejects the input, and so does the binder for a certificate claiming qf_uf.
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "over Bool alone"):
            proof_certificate.export_clause_log_certificate(
                "(declare-fun p (Bool) Bool)(declare-const q Bool)(assert (p q))(assert (not (p q)))")

    def test_level_zero_units_inside_boolean_arguments(self):
        source = UF_INPUTS["uf_bool_args_units"]
        # The live run must exercise the phantom path: Z3's raw log declares
        # its internal true variable as k!0 and assumes it as a unit clause.
        log = proof_clause_log.run_clause_log(proof_certificate.default_z3_executable(),
                                              proof_certificate._assertion_commands(source))
        self.assertIn("(declare-fun k!0 () Bool)", log)
        self.assertRegex(log, r"\(assume (\(not )?k!0\)?\)")
        certificate = proof_certificate.export_clause_log_certificate(source)
        graph = proof_to_lean._validate_graph(source, certificate)
        hints = [graph.decl(node).parameters for node in _th_lemma_nodes(certificate)]
        # Z3 substituted q and s into (f q) and (r s b): those assumptions are
        # tied to the units and the assertions by cnf lemmas; the phantom k!0
        # unit and the assumed true literal leave no trace but a def-axiom.
        self.assertIn(("cnf",), hints)
        self.assertIn(("euf",), hints)
        self.assertIn("def-axiom", certificate["rule_counts"])
        self.assertFalse([d for d in certificate["declarations"] if d["name"].startswith("k!")])
        self.assertNotIn("k!", json.dumps(certificate))
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertIn("(_bool (formula_", text)

    def test_quoted_sort_names_are_kept(self):
        source = ("(declare-sort |my sort| 0)(declare-fun a () |my sort|)(declare-fun b () |my sort|)"
                  "(declare-fun f (|my sort|) |my sort|)(assert (= a b))(assert (not (= (f a) (f b))))")
        certificate = proof_certificate.export_clause_log_certificate(source)
        self.assertEqual(certificate["fragment"], "qf_uf")
        self.assertIn("my sort", {d["range"] for d in certificate["declarations"]})
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertIn('-- Uninterpreted sort "my sort" is the type _U', text)
        self.assertNotIn("|", text)

    def test_several_sorts_share_one_lean_carrier(self):
        # The certificate keeps every sort name, so the proof graph is checked
        # to be well-sorted in Python; Lean sees one type _U for all of them.
        source = UF_INPUTS["uf_two_sorts"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        self.assertEqual(certificate["fragment"], "qf_uf")
        signatures = {(d["name"], tuple(d["domain"]), d["range"]) for d in certificate["declarations"]
                      if d["kind"] == z3.Z3_OP_UNINTERPRETED and d["domain"]}
        self.assertEqual(signatures, {("f", ("A",), "B"), ("g", ("B", "A"), "A"), ("p", ("B",), "Bool")})
        equalities = {tuple(d["domain"]) for d in certificate["declarations"] if d["kind"] == z3.Z3_OP_EQ}
        self.assertIn(("B", "B"), equalities)
        self.assertTrue(all(len(set(domain)) == 1 for domain in equalities))
        graph = proof_to_lean._validate_graph(source, certificate)
        self.assertEqual(graph.sorts, ("A", "B"))
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertIn('-- Uninterpreted sorts "A", "B" are the one type _U', text)
        self.assertIn("theorem unsat (_atoms : Nat -> Prop)" + proof_to_lean._UF_BINDERS, text)
        # Every element, application, and equality is over _U, whatever its sort.
        self.assertEqual(text.count(" : _U := "), sum(graph.is_term(node) for node in range(len(graph.nodes))))
        self.assertNotIn("Rat", text)

        def mutate(predicate, **changes):
            mutated = copy.deepcopy(certificate)
            for declaration in _declarations(mutated, predicate):
                declaration.update(changes)
            return mutated

        is_f = lambda d: d["name"] == "f" and d["kind"] == z3.Z3_OP_UNINTERPRETED
        is_g = lambda d: d["name"] == "g" and d["kind"] == z3.Z3_OP_UNINTERPRETED
        is_b = lambda d: d["name"] == "b" and d["kind"] == z3.Z3_OP_UNINTERPRETED
        is_eq_b = lambda d: d["kind"] == z3.Z3_OP_EQ and d["domain"] == ["B", "B"]
        for mutated, message in [
            # Equality and distinct compare terms of one sort; functions and predicates
            # take arguments of the uninterpreted sorts only, and every application
            # must be well-sorted.
            (mutate(is_eq_b, domain=["A", "B"]), "cannot mix argument sorts"),
            (mutate(is_f, domain=["B"]), "wrong argument sort"),
            (mutate(is_f, domain=["Bool"]), "wrong argument sort"),
            (mutate(is_f, domain=["Real"]), "unsupported uninterpreted-sort declaration"),
            (mutate(is_g, domain=["A", "B"]), "wrong argument sort"),
            (mutate(is_g, range="B"), "wrong argument sort"),
            (mutate(is_b, range="A"), "wrong argument sort"),
            (mutate(is_f, kind=z3.Z3_OP_ITE, name="if", domain=["Bool", "A", "B"]), "invalid uninterpreted-sort ite"),
        ]:
            with self.subTest(message=message):
                with self.assertRaisesRegex(proof_to_lean.ReconstructionError, message):
                    proof_to_lean.reconstruct(source, mutated)
        # Collapsing the two sorts inside the certificate itself is rejected: the
        # certificate must name the input's sorts, and only Lean collapses them.
        collapsed = copy.deepcopy(certificate)
        for declaration in collapsed["declarations"]:
            declaration["range"] = "A" if declaration["range"] == "B" else declaration["range"]
            declaration["domain"] = ["A" if sort == "B" else sort for sort in declaration["domain"]]
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "sort does not match the original input"):
            proof_to_lean.reconstruct(source, collapsed)
        # A one-sort certificate cannot be bound to a two-sort input with the same symbols.
        one_sort = re.sub(r"\bB\b", "A", source.replace("(declare-sort B 0)\n", ""))
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "sort does not match the original input"):
            proof_to_lean.reconstruct(one_sort, dict(certificate, source_smt2=one_sort))

    def test_symbols_bind_by_signature(self):
        # A function and a constant may not share a name, and two declarations
        # of one function name cannot both be bound to the input's symbol.
        source = "(declare-sort U 0)(declare-fun f (U) U)(declare-fun a () U)(assert (not (= (f a) (f a))))"
        certificate = proof_certificate.export_clause_log_certificate(source)
        graph = proof_to_lean._validate_graph(source, certificate)
        element = next(i for i in range(len(graph.nodes)) if graph.decl(i).name == "a")

        def with_extra_declaration(domain, arguments):
            extra = copy.deepcopy(certificate)
            extra["declarations"].append({"kind": z3.Z3_OP_UNINTERPRETED, "name": "f", "domain": domain,
                                          "range": "U", "parameters": []})
            extra["nodes"].append({"declaration": len(extra["declarations"]) - 1, "arguments": arguments})
            return extra

        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "two sorts"):
            proof_to_lean.reconstruct(source, with_extra_declaration([], []))
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "ambiguous function symbol"):
            proof_to_lean.reconstruct(source, with_extra_declaration(["U"], [element]))
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "ambiguous function symbol"):
            proof_to_lean.reconstruct(source, with_extra_declaration(["U", "U"], [element, element]))
        # Z3 accepts one name with two signatures; the certificate binds by name, so
        # the frontend rejects such inputs, in the exporter and inside the binder.
        overloaded = ("(declare-sort U 0)(declare-fun a () U)(declare-fun f (U) U)(declare-fun f (U U) U)"
                      "(assert (not (= (f a) (f a))))(assert (= (f a a) a))")
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "several signatures: f"):
            proof_certificate.export_clause_log_certificate(overloaded)
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "several signatures: f"):
            proof_to_lean.reconstruct(overloaded, dict(certificate, source_smt2=overloaded))

    def test_overloaded_symbols_cannot_rebind_a_certificate(self):
        # Z3 tells apart (declare-fun c () A) from (declare-fun c () B); a certificate
        # names symbols without their sorts. Binding the honest refutation of a
        # one-sort input to this satisfiable two-sort input, whose assertions print
        # identically, must fail at every layer: the sort set, the frontend, and
        # the binder's own signature checks.
        satisfiable = """\
(set-logic QF_UF)
(declare-sort A 0)
(declare-sort B 0)
(declare-fun c () A)
(declare-fun c () B)
(declare-fun h (A) B)
(declare-fun p (A) Bool)
(declare-fun p (B) Bool)
(assert (= (h (as c A)) (as c B)))
(assert (p (as c A)))
(assert (not (p (h (as c A)))))
(check-sat)
"""
        unsat = """\
(set-logic QF_UF)
(declare-sort A 0)
(declare-fun c () A)
(declare-fun h (A) A)
(declare-fun p (A) Bool)
(assert (= (h c) c))
(assert (p c))
(assert (not (p (h c))))
(check-sat)
"""
        certificate = proof_certificate.export_clause_log_certificate(unsat)
        self.assertEqual([str(a) for a in proof_certificate.parse_assertions(unsat, z3.Context())[0]],
                         [str(a) for a in z3.parse_smt2_string(proof_certificate._assertion_commands(satisfiable))])
        rebound = dict(certificate, source_smt2=satisfiable)
        padded = copy.deepcopy(rebound)
        padded["declarations"].append({"kind": z3.Z3_OP_UNINTERPRETED, "name": "unused", "domain": [],
                                       "range": "B", "parameters": []})
        # An unused declaration cannot pad the certificate's sort set to {A, B}.
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "unused declaration"):
            proof_to_lean.reconstruct(satisfiable, padded)
        # The frontend rejects the overloaded input before any binding.
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "several signatures"):
            proof_to_lean.reconstruct(satisfiable, rebound)
        # Even if it did not, the one-sort certificate does not know sort B.
        parsed = z3.parse_smt2_string(proof_certificate._assertion_commands(satisfiable))
        with patch.object(proof_to_lean, "parse_assertions", return_value=(parsed, "qf_uf")):
            with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "sort does not match"):
                proof_to_lean.reconstruct(satisfiable, rebound)
        # And a certificate that knows both sorts sees the overloaded name itself.
        source = UF_INPUTS["uf_two_sorts"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        overloaded = source.replace("(check-sat)", "(declare-fun b () A)\n(assert (= (as b A) a1))\n(check-sat)")
        with self.assertRaisesRegex(proof_certificate.ProofExportError, "several signatures: b"):
            proof_to_lean.reconstruct(overloaded, dict(certificate, source_smt2=overloaded))
        parsed = z3.parse_smt2_string(proof_certificate._assertion_commands(overloaded))
        with patch.object(proof_to_lean, "parse_assertions", return_value=(parsed, "qf_uf")):
            with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "several signatures: b"):
                proof_to_lean.reconstruct(overloaded, dict(certificate, source_smt2=overloaded))
        # Every bound symbol must carry the input's full signature: swapping the
        # two sorts throughout a two-sort certificate keeps the graph well-sorted
        # and the sort set unchanged, and is still rejected.
        swapped = copy.deepcopy(certificate)
        for declaration in swapped["declarations"]:
            swap = {"A": "B", "B": "A"}
            declaration["range"] = swap.get(declaration["range"], declaration["range"])
            declaration["domain"] = [swap.get(sort, sort) for sort in declaration["domain"]]
        self.assertEqual(proof_to_lean._validate_graph(source, swapped).sorts, ("A", "B"))
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "signature does not match"):
            proof_to_lean.reconstruct(source, swapped)


@unittest.skipUnless(_z3_available(), "the z3 executable is required for the clause log")
class TestUninterpretedLeanIntegration(unittest.TestCase):
    """End-to-end: z3 clause log, certificate, Lean reconstruction, kernel check."""

    def check(self, source):
        certificate = proof_certificate.export_clause_log_certificate(source)
        self.assertEqual(certificate["fragment"], "qf_uf")
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "checked.lean"
            proof_to_lean.check_and_write(source, certificate, output)
            text = output.read_text()
            namespace = "Z3Proofs.NativeCertificate.p" + hashlib.sha256(source.encode()).hexdigest()
            statement = text.split("theorem unsat", 1)[1].split(": False :=", 1)[0]
            self.assertEqual(statement.count("    (_h"), len(certificate["assertions"]))
            self.assertNotIn("_hyp", statement)
            self.assertIn(proof_to_lean._UF_BINDERS, statement)
            output.write_text(text + "\n#print axioms %s.unsat\n" % namespace)
            result = subprocess.run([str(proof_to_lean._CHECK_LEAN), str(output)],
                                    text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            return certificate, " ".join(result.stdout.split())

    def test_documented_uf_inputs_verify_under_the_standard_axioms(self):
        for name, source in UF_INPUTS.items():
            with self.subTest(name=name):
                certificate, report = self.check(source)
                self.assertIn("th-lemma", certificate["rule_counts"])
                # grind's congruence closure proofs use the classical axioms Lean core relies on.
                self.assertIn(".unsat' depends on axioms: " + _STANDARD_AXIOMS, report)

    # The first three seeds in 1..4999 whose unsat core has at least four
    # assertions, so the refutation needs learned clauses. They are pinned so
    # the checked inputs stay the same across Z3 versions; if a solver change
    # shrinks a core, re-pick the seed with the same scan.
    LEARNED_CLAUSE_SEEDS = (405, 693, 896)

    def test_random_instances_with_learned_clauses(self):
        for seed in self.LEARNED_CLAUSE_SEEDS:
            source = random_instance(seed)
            with self.subTest(seed=seed):
                self.assertGreaterEqual(_unsat_core_size(source), 4, "re-pick seed %d" % seed)
                certificate, _ = self.check(source)
                self.assertIn("th-lemma", certificate["rule_counts"])

    # Seeds of random_instance(seed, ite=0.4) whose unsat core has at least six
    # assertions and whose refutation reasons through ite terms; pinned like
    # LEARNED_CLAUSE_SEEDS.
    ITE_SEEDS = (873, 1467, 1975)

    def test_random_instances_with_ite_terms(self):
        for seed in self.ITE_SEEDS:
            source = random_instance(seed, ite=0.4)
            with self.subTest(seed=seed):
                self.assertIn("(ite ", source)
                self.assertGreaterEqual(_unsat_core_size(source), 6, "re-pick seed %d" % seed)
                certificate, _ = self.check(source)
                self.assertIn("def-axiom", certificate["rule_counts"])  # ite gate clauses
                self.assertIn("@ite _U", proof_to_lean.reconstruct(source, certificate))

    # Seeds of random_sorted_instance(seed) (three sorts, ite terms) whose unsat
    # core has at least four assertions; pinned like LEARNED_CLAUSE_SEEDS.
    MANY_SORTED_SEEDS = (231, 752, 1200)

    def test_random_many_sorted_instances(self):
        for seed in self.MANY_SORTED_SEEDS:
            source = random_sorted_instance(seed)
            with self.subTest(seed=seed):
                self.assertGreaterEqual(_unsat_core_size(source), 4, "re-pick seed %d" % seed)
                certificate, _ = self.check(source)
                self.assertIn("th-lemma", certificate["rule_counts"])
                text = proof_to_lean.reconstruct(source, certificate)
                self.assertIn('-- Uninterpreted sorts "S0", "S1", "S2" are the one type _U', text)

    # Seeds of random_bool_argument_instance(seed) whose unsat core has at
    # least four assertions; pinned like LEARNED_CLAUSE_SEEDS (the generator
    # is sat-heavy: the first three are all such seeds below 400). The last
    # two have lemmas that grind proves only with the explicit case splits on
    # Boolean arguments, as Z3 combined assertions without naming the literal.
    BOOL_ARGUMENT_SEEDS = (4, 98, 347, 1639, 2088)

    def test_random_instances_with_boolean_arguments(self):
        for seed in self.BOOL_ARGUMENT_SEEDS:
            source = random_bool_argument_instance(seed)
            with self.subTest(seed=seed):
                self.assertGreaterEqual(_unsat_core_size(source), 4, "re-pick seed %d" % seed)
                certificate, _ = self.check(source)
                self.assertIn("th-lemma", certificate["rule_counts"])
                self.assertIn("(_bool (formula_", proof_to_lean.reconstruct(source, certificate))

    def test_long_refutations_are_outlined_into_bounded_lemmas(self):
        # Seven levels give about 1,600 proof steps; as one nested term the main
        # theorem exhausts Lean's default heartbeat budget, outlined it checks
        # in a few seconds.
        source = equality_diamond(7)
        certificate, report = self.check(source)
        self.assertGreater(_proof_steps(certificate), proof_to_lean._OUTLINE_PROOF_STEPS)
        self.assertIn(".unsat' depends on axioms: " + _STANDARD_AXIOMS, report)
        text = proof_to_lean.reconstruct(source, certificate)
        sizes = outlined_lemma_sizes(text)
        self.assertGreater(len(sizes), 1)
        self.assertLessEqual(max(sizes), proof_to_lean._OUTLINE_CHUNK_STEPS)
        self.assertEqual(sum(sizes), _proof_steps(certificate))
        self.assertIn("  proof_step_%d _atoms%s " % (certificate["proof"], proof_to_lean._UF_ARGUMENTS), text)

    def test_small_chunks_cut_every_lemma_shape(self):
        # Force boundaries inside lemma subproofs, between shared steps, and at
        # the root; every chunk must still be a closed lemma Lean accepts.
        with patch.object(proof_to_lean, "_OUTLINE_PROOF_STEPS", 0), \
                patch.object(proof_to_lean, "_OUTLINE_CHUNK_STEPS", 3):
            for name, source in UF_INPUTS.items():
                with self.subTest(name=name):
                    certificate, _ = self.check(source)
                    sizes = outlined_lemma_sizes(proof_to_lean.reconstruct(source, certificate))
                    self.assertLessEqual(max(sizes), 3)
                    self.assertEqual(sum(sizes), _proof_steps(certificate))

    def test_tampered_euf_lemmas_never_publish_a_proof(self):
        source = UF_INPUTS["uf_congruence"]
        certificate = proof_certificate.export_clause_log_certificate(source)
        graph = proof_to_lean._validate_graph(source, certificate)

        def declaration(kind, name, domain, parameters=()):
            raw = {"kind": kind, "name": name, "domain": list(domain), "range": "Proof" if kind >= 0x500 else "Bool",
                   "parameters": list(parameters)}
            if raw not in tampered["declarations"]:
                tampered["declarations"].append(raw)
            return tampered["declarations"].index(raw)

        def node(decl, arguments):
            tampered["nodes"].append({"declaration": decl, "arguments": list(arguments)})
            return len(tampered["nodes"]) - 1

        # Claim (not (= a b)) as a euf lemma, which holds in no model with a = b, and resolve it
        # against the asserted equality into the empty clause. Python's shape checks pass: euf
        # hints carry no coefficients to pre-check, so only Lean can reject the lemma.
        tampered = copy.deepcopy(certificate)
        equality = graph.assertions[0]
        asserted = next(i for i in range(len(graph.nodes)) if graph.kind(i) == z3.Z3_OP_PR_ASSERTED
                        and graph.conclusion(i) == equality)
        false = graph.conclusion(graph.proof)
        negation = node(declaration(z3.Z3_OP_NOT, "not", ["Bool"]), [equality])
        lemma = node(declaration(z3.Z3_OP_PR_TH_LEMMA, "th-lemma", ["Bool"], ["euf"]), [negation])
        tampered["proof"] = node(declaration(z3.Z3_OP_PR_UNIT_RESOLUTION, "unit-resolution",
                                             ["Proof", "Proof", "Bool"]), [lemma, asserted, false])
        tampered["rule_counts"]["th-lemma"] += 1
        tampered["rule_counts"]["unit-resolution"] += 1
        text = proof_to_lean.reconstruct(source, tampered)  # accepted by every Python check
        self.assertIn("th_lemma_%d" % lemma, text)
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "checked.lean"
            with self.assertRaises(subprocess.CalledProcessError) as context:
                proof_to_lean.check_and_write(source, tampered, output)
            diagnostics = context.exception.stdout + context.exception.stderr
            self.assertIn("`grind` failed", diagnostics)
            self.assertIn("_elems 0 = _elems 1", diagnostics)  # the false lemma's only hypothesis
            self.assertFalse(output.exists())
        # Swapping two distinct constants in an assertion breaks the binding before Lean.
        tampered = copy.deepcopy(certificate)
        elements = sorted(i for i, raw in enumerate(tampered["nodes"])
                          if tampered["declarations"][raw["declaration"]]["range"] == "U"
                          and not raw["arguments"])
        tampered["nodes"][elements[0]], tampered["nodes"][elements[1]] = (
            tampered["nodes"][elements[1]], tampered["nodes"][elements[0]])
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "do not match the original input"):
            proof_to_lean.reconstruct(source, tampered)


if __name__ == "__main__":
    unittest.main()
