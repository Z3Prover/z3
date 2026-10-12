############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Tests for the QF_UF slice of the Lean reconstruction: validation without
# Lean, and end-to-end checks that need the z3 executable and the pinned
# Lean toolchain.
############################################
import copy
import hashlib
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
}


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
        self.assertEqual(graph.sort, "U")
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

        # The certificate's sort name must be the input's; two sorts are rejected before binding.
        renamed = copy.deepcopy(self.certificate)
        rename_sort(renamed, "V")
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "sort does not match the original input"):
            proof_to_lean.reconstruct(self.source, renamed)
        renamed = copy.deepcopy(self.certificate)
        rename_sort(renamed, "V", only_first=True)
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "only one uninterpreted sort"):
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
            (mutate(is_f, domain=["Bool"]), "unsupported uninterpreted-sort declaration"),
            (mutate(is_f, kind=z3.Z3_OP_ITE, name="if", domain=["U", "U", "U"]), "invalid uninterpreted-sort ite"),
            (mutate(is_f, kind=z3.Z3_OP_ITE, name="ite", domain=["Bool", "U", "U"]), "invalid uninterpreted-sort ite"),
            (mutate(is_f, kind=z3.Z3_OP_ITE, name="if", domain=["Bool", "U", "U"]), "wrong number of arguments"),
            (mutate(is_f, kind=z3.Z3_OP_ADD, name="+", domain=["U", "U"]), "unsupported uninterpreted-sort"),
            (mutate(is_p, domain=["Bool"]), "cannot mix argument sorts"),
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

    def test_quoted_sort_names_are_kept(self):
        source = ("(declare-sort |my sort| 0)(declare-fun a () |my sort|)(declare-fun b () |my sort|)"
                  "(declare-fun f (|my sort|) |my sort|)(assert (= a b))(assert (not (= (f a) (f b))))")
        certificate = proof_certificate.export_clause_log_certificate(source)
        self.assertEqual(certificate["fragment"], "qf_uf")
        self.assertIn("my sort", {d["range"] for d in certificate["declarations"]})
        text = proof_to_lean.reconstruct(source, certificate)
        self.assertIn('-- Uninterpreted sort "my sort" is the type _U', text)
        self.assertNotIn("|", text)

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
        # Z3 accepts one name with two signatures; the certificate cannot bind both.
        overloaded = ("(declare-sort U 0)(declare-fun a () U)(declare-fun f (U) U)(declare-fun f (U U) U)"
                      "(assert (not (= (f a) (f a))))(assert (= (f a a) a))")
        certificate = proof_certificate.export_clause_log_certificate(overloaded)
        with self.assertRaisesRegex(proof_to_lean.ReconstructionError, "ambiguous function symbol"):
            proof_to_lean.reconstruct(overloaded, certificate)


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
