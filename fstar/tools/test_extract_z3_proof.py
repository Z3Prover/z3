import copy
import json
import os
import subprocess
import unittest

import z3

import extract_z3_proof as extractor


class Certificate:
    def __init__(self):
        self.ctx = z3.Context(proof=True)
        self.converter = extractor.ResolutionConverter()
        self.assertions = []
        self.facts = []
        self.oeq_decl = None

    def oeq(self, a, b):
        if self.oeq_decl is None:
            p, q = z3.Bools("_oeq_p _oeq_q", self.ctx)
            solver = z3.Then(z3.Tactic("nnf", ctx=self.ctx),
                             z3.Tactic("smt", ctx=self.ctx)).solver()
            solver.add(z3.Not(z3.And(p, q)), p, q)
            if solver.check() != z3.unsat:
                raise AssertionError("Expected a proof exposing the OEQ declaration")
            stack = [solver.proof()]
            seen = set()
            while stack:
                node = stack.pop()
                if node.get_id() in seen:
                    continue
                seen.add(node.get_id())
                if z3.is_app(node) and node.decl().kind() == z3.Z3_OP_OEQ:
                    self.oeq_decl = node.decl()
                    break
                stack.extend(node.children())
            if self.oeq_decl is None:
                raise AssertionError("NNF proof did not expose an OEQ declaration")
        return self.oeq_decl(a, b)

    def node(self, kind, conclusion, premises=(), **fields):
        nodes = self.converter.proof_json
        index = len(nodes)
        self.facts.append(conclusion)
        nodes.append({
            "kind": kind,
            "conclusion": self.converter._idx(self.converter.expr(conclusion)),
            "premises": list(premises),
            **fields,
        })
        return index

    def asserted(self, fact):
        self.assertions.append(fact)
        return self.node("asserted", fact)

    def document(self, root):
        return extractor.build_resolution_doc(
            self.converter, "rp_%d" % root, self.assertions)


class ExtractionTests(unittest.TestCase):
    def test_boolean_flatten_classification_is_specific_to_full_proofs(self):
        ctx = z3.Context()
        p, q, r = z3.Bools("p q r", ctx)
        for op, name in ((z3.And, "and_flatten"), (z3.Or, "or_flatten")):
            with self.subTest(op=name):
                left, right = op(op(p, q), r), op(p, q, r)
                self.assertEqual(extractor.classify_full_rewrite(left, right), name)
                self.assertIsNone(extractor.classify_rewrite(left, right))
                self.assertEqual(extractor.classify_full_rewrite(left, op(r, q, p)),
                                 "boolean_equiv")

    def test_real_definition_and_commutativity_rules_are_not_obligations(self):
        ctx = z3.Context(proof=True)
        p, q, r = z3.Bools("p q r", ctx)
        x, y = z3.Consts("x y", z3.DeclareSort("U", ctx))
        for assertions, required in (
                ([z3.Or(z3.And(p, q), r), z3.Not(p), z3.Not(r)], "def-axiom"),
                ([z3.Or(x == y, p), z3.Not(y == x), z3.Not(p)], "commutativity")):
            with self.subTest(rule=required):
                solver = z3.Solver(ctx=ctx)
                solver.add(*assertions)
                self.assertEqual(solver.check(), z3.unsat)
                converter = extractor.ResolutionConverter()
                root = converter.proof(solver.proof())
                doc = extractor.build_resolution_doc(converter, root, solver.assertions())
                self.assertIn(required, {node["kind"] for node in doc["proofs"]})
                self.assertNotIn(required, {rule for rule, _ in converter.trusted_log})
                if os.environ.get("Z3_FSTAR_CHECKER"):
                    pending = len(converter.trusted_log) + sum(
                        name not in extractor.FULL_PROOF_REWRITES
                        for _, _, name in converter.rewrite_log)
                    NativeCheckerTests().check(doc, 3 if pending else 0,
                                               obligations=pending if pending else None)
                    if required == "def-axiom":
                        NativeCheckerTests().check(doc, 1, strict=True)

    def test_commutativity_support_is_theory_and_shape_specific(self):
        ctx = z3.Context()
        x, y = z3.Ints("x y", ctx)
        p, q = z3.Bools("p q", ctx)
        r, s = z3.Reals("r s", ctx)
        f = z3.Function("f", x.sort(), x.sort(), x.sort())
        for a, b, supported in (
                (x == y, y == x, True),
                (x + y, y + x, True),
                (x * y, y * x, True),
                (z3.And(p, q), z3.And(q, p), True),
                (z3.Or(p, q), z3.Or(q, p), True),
                (r + s, s + r, False),
                (x - y, y - x, False),
                (f(x, y), f(y, x), False),
                (x + y, x + x, False)):
            with self.subTest(a=str(a), b=str(b)):
                self.assertEqual(extractor.supported_commutativity(a == b), supported)

    def test_nnf_proof_preserves_observational_equality(self):
        ctx = z3.Context(proof=True)
        p, q = z3.Bools("p q", ctx)
        solver = z3.Then(z3.Tactic("nnf", ctx=ctx),
                         z3.Tactic("smt", ctx=ctx)).solver()
        solver.add(z3.Not(z3.And(p, q)), p, q)
        self.assertEqual(solver.check(), z3.unsat)
        converter = extractor.ResolutionConverter()
        root = converter.proof(solver.proof())
        doc = extractor.build_resolution_doc(converter, root, solver.assertions())
        self.assertIn("mp~", {n["kind"] for n in doc["proofs"]})
        oeq = next(d for d in doc["decls"] if d["name"] == "~")
        self.assertEqual(oeq["interp"], "op_oeq")
        self.assertNotIn("mp~", {rule for rule, _ in converter.trusted_log})
        self.assertIn("refl", {n["kind"] for n in doc["proofs"]})
        if os.environ.get("Z3_FSTAR_CHECKER"):
            NativeCheckerTests().check(doc, 3, obligations=1)

    def test_observational_and_boolean_equality_have_distinct_declarations(self):
        c = Certificate()
        p, q = z3.Bools("p q", c.ctx)
        c.converter.expr(c.oeq(p, q))
        c.converter.expr(p == q)
        relations = {d["name"]: d for d in c.converter.decl_json
                     if d["name"] in ("=", "~")}
        self.assertEqual(relations["~"]["interp"], "op_oeq")
        self.assertEqual(relations["="]["interp"], "op_eq")
        self.assertNotEqual(c.converter.expr(c.oeq(p, q)), c.converter.expr(p == q))

    def test_complete_resolution_derivation_is_not_an_opaque_rewrite(self):
        ctx = z3.Context(proof=True)
        x, y = z3.Consts("x y", z3.DeclareSort("U", ctx))
        p = z3.Bool("p", ctx)
        f = z3.Function("f", x.sort(), x.sort())
        solver = z3.Solver(ctx=ctx)
        solver.add(z3.Or(p, x == y), z3.Not(p), f(x) != f(y))
        self.assertEqual(solver.check(), z3.unsat)
        converter = extractor.ResolutionConverter()
        root = converter.proof(solver.proof())
        doc = extractor.build_resolution_doc(converter, root, solver.assertions())
        self.assertIn("unit-resolution", {n["kind"] for n in doc["proofs"]})
        self.assertIn("monotonicity", {n["kind"] for n in doc["proofs"]})
        self.assertEqual(converter.expr_json[
            doc["proofs"][doc["root"]]["conclusion"]]["kind"], "app")
        for index, node in enumerate(doc["proofs"]):
            self.assertTrue(all(0 <= p < index for p in node["premises"]))
            if node["kind"] == "trusted":
                self.assertNotIn(node["rule"], converter.SUPPORTED_RULES)

    def test_overloaded_equality_declarations_remain_distinct(self):
        ctx = z3.Context()
        x, y = z3.Ints("x y", ctx)
        p, q = z3.Bools("p q", ctx)
        converter = extractor.ResolutionConverter()
        terms = [x == y, p == q, z3.And(p, q, p)]
        for term in terms:
            converter.expr(term)
        equalities = [d for d in converter.decl_json if d["name"] == "="]
        self.assertEqual(len(equalities), 2)
        self.assertNotEqual(equalities[0]["domain"], equalities[1]["domain"])
        conjunction = next(d for d in converter.decl_json if d["name"] == "and")
        self.assertEqual(conjunction["interp"], "op_and")

    def test_array_sorts_with_different_domains_are_not_collapsed(self):
        ctx = z3.Context()
        a = z3.Array("a", z3.IntSort(ctx), z3.BoolSort(ctx))
        b = z3.Array("b", z3.BoolSort(ctx), z3.IntSort(ctx))
        converter = extractor.ResolutionConverter()
        converter.expr(a)
        converter.expr(b)
        arrays = [s for s in converter.sort_json if s["kind"] == "array"]
        self.assertEqual(len(arrays), 2)
        self.assertNotEqual(arrays[0], arrays[1])

    def test_array_lemma_classification_checks_instances_not_rule_names(self):
        ctx = z3.Context()
        index, element = z3.DeclareSort("Index", ctx), z3.DeclareSort("Element", ctx)
        a, b = z3.Consts("a b", z3.ArraySort(index, element))
        i, j = z3.Consts("i j", index)
        v = z3.Const("v", element)
        stored = z3.Store(a, i, v)
        witness = z3.Ext(a, b)
        for conclusion, expected in (
                (z3.Select(stored, i) == v, "array_read_over_write_same"),
                (z3.Or(i == j, z3.Select(stored, j) == z3.Select(a, j)),
                 "array_read_over_write_other"),
                (z3.Or(a == b, z3.Not(z3.Select(a, witness) == z3.Select(b, witness))),
                 "array_extensionality"),
                (z3.Select(stored, j) == v, None),
                (z3.Or(i != j, z3.Select(stored, j) == z3.Select(a, j)), None),
                (z3.Or(a == b, z3.Not(z3.Select(a, i) == z3.Select(b, i))), None)):
            with self.subTest(conclusion=str(conclusion)):
                self.assertEqual(extractor.classify_array_lemma(conclusion), expected)


@unittest.skipUnless(os.environ.get("Z3_FSTAR_CHECKER"),
                     "Set Z3_FSTAR_CHECKER to the built native checker")
class NativeCheckerTests(unittest.TestCase):
    def check(self, document, expected, obligations=None, strict=False):
        checker = os.environ["Z3_FSTAR_CHECKER"]
        command = (["wsl", "-e", "bash", "-c", checker] if os.name == "nt"
                   else [os.path.expanduser(checker)])
        if strict:
            if os.name == "nt":
                command[-1] += " --check-original-assertions"
            else:
                command.append("--check-original-assertions")
        result = subprocess.run(command, input=json.dumps(document),
                                capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, expected,
                         result.stdout + result.stderr)
        self.assertEqual(result.stdout.strip().split()[0],
                         {0: "ACCEPT", 1: "REJECT", 3: "PARTIAL"}[expected])
        if obligations is not None:
            self.assertEqual(result.stdout.strip(), "PARTIAL %d" % obligations)

    def test_identity_rewrites_are_discharged_for_all_sorts(self):
        for form in ("bool", "int", "uf", "array", "application", "observational"):
            with self.subTest(form=form):
                c = Certificate()
                p, q = z3.Bools("p q", c.ctx)
                sort = {"int": z3.IntSort(c.ctx),
                        "uf": z3.DeclareSort("U", c.ctx),
                        "array": z3.ArraySort(z3.IntSort(c.ctx), z3.BoolSort(c.ctx))}
                term = (z3.Const("x", sort[form]) if form in sort else
                        z3.Or(p, q) if form == "application" else p)
                if form == "observational":
                    rewrite = c.node("rewrite", c.oeq(term, term))
                    original = c.asserted(term)
                    result = c.node("mp~", term, [original, rewrite])
                    opposite = c.asserted(z3.Not(term))
                else:
                    equality = term == term
                    result = c.node("rewrite", equality)
                    opposite = c.asserted(z3.Not(equality))
                root = c.node("unit-resolution", z3.BoolVal(False, c.ctx),
                              [result, opposite])
                self.check(c.document(root), 0)

    def test_unsupported_rewrites_remain_obligations(self):
        for form in ("distinct", "dropped"):
            with self.subTest(form=form):
                c = Certificate()
                p, q, r = z3.Bools("p q r", c.ctx)
                left, right = ((p, q) if form == "distinct" else
                               (z3.Or(z3.Or(p, q), r), z3.Or(q, p)))
                equality = left == right
                rewrite = c.node("rewrite", equality)
                opposite = c.asserted(z3.Not(equality))
                root = c.node("unit-resolution", z3.BoolVal(False, c.ctx),
                              [rewrite, opposite])
                self.check(c.document(root), 3, obligations=1)

    def test_nary_boolean_flattening_preserves_order_and_other_connectives(self):
        for op, other in ((z3.And, z3.Or), (z3.Or, z3.And)):
            for form in ("nested", "empty", "singleton", "mixed", "duplicates",
                         "observational"):
                with self.subTest(op=op.__name__, form=form):
                    c = Certificate()
                    p, q, r, s = z3.Bools("p q r s", c.ctx)
                    empty = op(c.ctx)
                    left, right = {
                        "nested": (op(op(p, q), op(r, op(s))), op(p, q, r, s)),
                        "empty": (op(empty, p, op(q, empty)), op(p, q)),
                        "singleton": (op(op(p), q), op(p, q)),
                        "mixed": (op(other(p, q), op(r, s)), op(other(p, q), r, s)),
                        "duplicates": (op(op(p, p), q), op(p, p, q)),
                        "observational": (op(op(p, q), r), op(p, q, r)),
                    }[form]
                    if form == "observational":
                        rewrite = c.node("rewrite", c.oeq(left, right))
                        original = c.asserted(left)
                        result = c.node("mp~", right, [original, rewrite])
                        opposite = c.asserted(z3.Not(right))
                    else:
                        equality = left == right
                        result = c.node("rewrite", equality)
                        opposite = c.asserted(z3.Not(equality))
                    root = c.node("unit-resolution", z3.BoolVal(False, c.ctx),
                                  [result, opposite])
                    self.check(c.document(root), 0)

    def test_flattening_does_not_license_other_rewrites_or_spoofed_operators(self):
        for op, other in ((z3.And, z3.Or), (z3.Or, z3.And)):
            for form in ("drop", "reorder", "deduplicate", "other", "reverse",
                         "uninterpreted", "spoofed_tag", "spoofed_name"):
                with self.subTest(op=op.__name__, form=form):
                    c = Certificate()
                    p, q, r = z3.Bools("p q r", c.ctx)
                    left = op(op(p, q), r)
                    right = {"drop": op(p, q), "reorder": op(r, q, p),
                             "deduplicate": op(p, q, r), "other": other(p, q, r),
                             "reverse": op(op(p, q), r)}.get(form, op(p, q, r))
                    if form == "deduplicate":
                        left = op(op(p, p), q, r)
                    elif form == "reverse":
                        left = op(p, q, r)
                    elif form == "uninterpreted":
                        f = z3.Function("f", p.sort(), p.sort(), p.sort())
                        left, right = f(f(p, q), r), f(p, f(q, r))
                    equality = left == right
                    rewrite = c.node("rewrite", equality)
                    opposite = c.asserted(z3.Not(equality))
                    root = c.node("unit-resolution", z3.BoolVal(False, c.ctx),
                                  [rewrite, opposite])
                    doc = c.document(root)
                    if form in ("spoofed_tag", "spoofed_name"):
                        for decl in doc["decls"]:
                            if decl["name"] == op.__name__.lower():
                                if form == "spoofed_tag":
                                    decl["interp"] = "op_or" if op == z3.And else "op_and"
                                else:
                                    decl["name"] = "fake"
                    if form in ("reorder", "deduplicate", "reverse"):
                        self.check(doc, 0)
                    else:
                        self.check(doc, 1 if form == "spoofed_tag" else 3,
                                   obligations=None if form == "spoofed_tag" else 1)

    def test_boolean_normalization_and_truth_table_rewrites(self):
        for form in ("demorgan", "contextual", "aci", "contradiction", "identity",
                     "implies", "boolean_eq", "distribution", "opaque", "shared",
                     "absorption_and", "absorption_or", "wide_complement",
                     "wide_identity", "singleton", "contextual_eq_reflexive"):
            with self.subTest(form=form):
                c = Certificate()
                ps = z3.Bools(" ".join("p%d" % i for i in range(20)), c.ctx)
                p, q, r = ps[:3]
                u, v = z3.Consts("u v", z3.DeclareSort("U", c.ctx))
                shared = z3.And(*ps)
                left, right = {
                    "demorgan": (z3.And(*ps), z3.Not(z3.Or(*[z3.Not(a) for a in ps]))),
                    "contextual": (z3.Or(z3.And(p, z3.And(q, r)), shared),
                                   z3.Or(z3.And(p, q, r), shared)),
                    "aci": (z3.Or(p, q, p, r), z3.Or(r, p, q)),
                    "contradiction": (z3.And(p, z3.Not(p), q), z3.BoolVal(False, c.ctx)),
                    "identity": (z3.Or(z3.BoolVal(False, c.ctx), p), p),
                    "implies": (z3.Implies(p, q), z3.Or(z3.Not(p), q)),
                    "boolean_eq": (p == q, z3.Or(z3.And(p, q),
                                               z3.And(z3.Not(p), z3.Not(q)))),
                    "distribution": (z3.And(p, z3.Or(q, r)),
                                     z3.Or(z3.And(p, q), z3.And(p, r))),
                    "opaque": (z3.And(u == v, z3.Not(u == v)), z3.BoolVal(False, c.ctx)),
                    "shared": (z3.Not(z3.Not(shared)), shared),
                    "absorption_and": (z3.And(*ps, z3.Or(p, q)), shared),
                    "absorption_or": (z3.Or(*ps, z3.And(p, q)), z3.Or(*ps)),
                    "wide_complement": (z3.Or(z3.And(p, z3.Not(p), *ps), q), q),
                    "wide_identity": (z3.And(*ps, z3.BoolVal(True, c.ctx)), shared),
                    "singleton": (z3.Or(*[p] * 20), p),
                    "contextual_eq_reflexive": (z3.And(u == u, *ps), shared),
                }[form]
                self.assertEqual(extractor.classify_full_rewrite(left, right), "boolean_equiv")
                equality = left == right
                rewrite = c.node("rewrite", equality)
                opposite = c.asserted(z3.Not(equality))
                root = c.node("unit-resolution", z3.BoolVal(False, c.ctx), [rewrite, opposite])
                self.check(c.document(root), 0)

    def test_boolean_fallback_budget_and_nonboolean_atoms(self):
        for form in ("width", "depth", "opaque", "not_equivalent"):
            with self.subTest(form=form):
                c = Certificate()
                ps = z3.Bools(" ".join("p%d" % i for i in range(11)), c.ctx)
                p, q = ps[:2]
                u, v = z3.Consts("u v", z3.DeclareSort("U", c.ctx))
                deep = z3.And(p, z3.Or(q, ps[2]))
                deep_other = z3.Or(z3.And(p, q), z3.And(p, ps[2]))
                for _ in range(12):
                    deep = z3.Not(deep)
                    deep_other = z3.Not(deep_other)
                left, right = {
                    "width": (z3.And(p, z3.Or(*ps[1:])),
                              z3.Or(*[z3.And(p, a) for a in ps[1:]])),
                    "depth": (deep, deep_other),
                    "opaque": (u == v, v == u),
                    "not_equivalent": (z3.Implies(p, q), z3.Implies(q, p)),
                }[form]
                self.assertFalse(extractor._bounded_boolean_equiv(left, right))
                equality = left == right
                rewrite = c.node("rewrite", equality)
                opposite = c.asserted(z3.Not(equality))
                root = c.node("unit-resolution", z3.BoolVal(False, c.ctx), [rewrite, opposite])
                self.check(c.document(root), 3, obligations=1)

    def test_equality_reflexivity_simplifies_at_any_sort(self):
        for form in ("bool", "int", "uf", "array"):
            with self.subTest(form=form):
                c = Certificate()
                sort = {"bool": z3.BoolSort(c.ctx), "int": z3.IntSort(c.ctx),
                        "uf": z3.DeclareSort("U", c.ctx),
                        "array": z3.ArraySort(z3.IntSort(c.ctx), z3.BoolSort(c.ctx))}[form]
                x = z3.Const("x", sort)
                equality = (x == x) == z3.BoolVal(True, c.ctx)
                self.assertEqual(extractor.classify_full_rewrite(
                    equality.arg(0), equality.arg(1)), "eq_reflexive")
                rewrite = c.node("rewrite", equality)
                opposite = c.asserted(z3.Not(equality))
                root = c.node("unit-resolution", z3.BoolVal(False, c.ctx), [rewrite, opposite])
                self.check(c.document(root), 0)

    def test_identity_rewrite_still_requires_a_relational_leaf(self):
        for form in ("nonrelational", "premise"):
            with self.subTest(form=form):
                c = Certificate()
                p = z3.Bool("p", c.ctx)
                premises = [c.asserted(p)] if form == "premise" else []
                c.node("rewrite", p == p if form == "premise" else p, premises)
                root = c.asserted(z3.BoolVal(False, c.ctx))
                self.check(c.document(root), 1)

    def test_def_axiom_trust_and_original_assertion_membership(self):
        for old_tag in (False, True):
            for strict in (False, True):
                for matching in (False, True):
                    with self.subTest(old_tag=old_tag, strict=strict, matching=matching):
                        c = Certificate()
                        p = z3.Bool("p", c.ctx)
                        axiom = c.node("trusted" if old_tag else "def-axiom", p,
                                       **({"rule": "def-axiom"} if old_tag else {}))
                        if matching:
                            c.assertions.append(p)
                        opposite = c.asserted(z3.Not(p))
                        root = c.node("unit-resolution", z3.BoolVal(False, c.ctx),
                                      [axiom, opposite])
                        doc = c.document(root)
                        doc["check_original_assertions"] = strict
                        self.check(doc, 1 if strict and not matching else 0)
                        if not strict and not matching:
                            self.check(doc, 1, strict=True)

    def test_def_axiom_must_be_an_ordinary_leaf(self):
        for form in ("premise", "observational", "malformed_policy"):
            with self.subTest(form=form):
                c = Certificate()
                p, q = z3.Bools("p q", c.ctx)
                fact = c.oeq(p, q) if form == "observational" else p
                premises = [c.asserted(p)] if form == "premise" else []
                c.node("def-axiom", fact, premises)
                root = c.asserted(z3.BoolVal(False, c.ctx))
                doc = c.document(root)
                if form == "malformed_policy":
                    doc["check_original_assertions"] = "false"
                self.check(doc, 1)

    def test_binary_commutativity_checks_operators_sorts_and_endpoints(self):
        for form in ("eq_uf", "eq_bool", "eq_array", "add", "mul", "and", "or",
                     "subtract", "uninterpreted", "wrong_endpoint", "different_decl",
                     "real_add", "nary", "premise", "spoofed_tag", "spoofed_name",
                     "observational"):
            with self.subTest(form=form):
                c = Certificate()
                x, y = z3.Ints("x y", c.ctx)
                p, q = z3.Bools("p q", c.ctx)
                if form.startswith("eq_"):
                    sort = {"eq_uf": z3.DeclareSort("U", c.ctx),
                            "eq_bool": z3.BoolSort(c.ctx),
                            "eq_array": z3.ArraySort(x.sort(), x.sort())}[form]
                    a, b = z3.Consts("a b", sort)
                    left, right = a == b, b == a
                elif form in ("and", "or", "observational"):
                    op = z3.Or if form == "or" else z3.And
                    left, right = op(p, q), op(q, p)
                elif form == "real_add":
                    a, b = z3.Reals("a b", c.ctx)
                    left, right = a + b, b + a
                elif form == "subtract":
                    left, right = x - y, y - x
                elif form == "uninterpreted":
                    f = z3.Function("f", x.sort(), x.sort(), x.sort())
                    left, right = f(x, y), f(y, x)
                elif form == "mul":
                    left, right = x * y, y * x
                elif form == "nary":
                    left, right = z3.Sum(x, y, x), z3.Sum(y, x, x)
                else:
                    left = x + y
                    right = (x + x if form == "wrong_endpoint" else
                             y * x if form == "different_decl" else y + x)
                equality = c.oeq(left, right) if form == "observational" else left == right
                premises = [c.asserted(p)] if form == "premise" else []
                commute = c.node("commutativity", equality, premises)
                opposite = c.asserted(z3.Not(equality)) if form != "observational" else c.asserted(p)
                root = (c.asserted(z3.BoolVal(False, c.ctx)) if form == "observational"
                        else c.node("unit-resolution", z3.BoolVal(False, c.ctx),
                                    [commute, opposite]))
                doc = c.document(root)
                if form in ("spoofed_tag", "spoofed_name"):
                    decl = next(d for d in doc["decls"] if d["name"] == "+")
                    decl["interp" if form == "spoofed_tag" else "name"] = (
                        "op_eq" if form == "spoofed_tag" else "fake_plus")
                valid = form in ("eq_uf", "eq_bool", "eq_array", "add", "mul", "and", "or")
                self.check(doc, 0 if valid else 1)

    def test_resolution_consequences(self):
        for form in ("literal", "singleton_or", "nested_or", "reordered",
                     "weakened", "dropped", "premature_false"):
            with self.subTest(form=form):
                c = Certificate()
                p, q, r, extra = z3.Bools("p q r extra", c.ctx)
                survivor = z3.Or(q, r) if form == "nested_or" else q
                literals = [p, q, r] if form in ("reordered", "weakened") else [p, survivor]
                first = c.asserted(z3.Or(*literals))
                unit = c.asserted(z3.Not(p))
                conclusion = {
                    "literal": q,
                    "singleton_or": z3.Or(q),
                    "nested_or": survivor,
                    "reordered": z3.Or(r, q),
                    "weakened": z3.Or(extra, r, q),
                    "dropped": r,
                    "premature_false": z3.BoolVal(False, c.ctx),
                }[form]
                derived = c.node("unit-resolution", conclusion, [first, unit])
                opposite = c.asserted(z3.Not(conclusion))
                root = c.node("unit-resolution", z3.BoolVal(False, c.ctx),
                              [derived, opposite])
                self.check(c.document(root),
                           1 if form in ("dropped", "premature_false") else 0)

    def test_direct_complementary_units_and_empty_or(self):
        for wrapped in (False, True):
            with self.subTest(wrapped=wrapped):
                c = Certificate()
                p = z3.Bool("p", c.ctx)
                first, second = c.asserted(p), c.asserted(z3.Not(p))
                conclusion = z3.BoolVal(False, c.ctx)
                resolved = c.node("unit-resolution", conclusion, [first, second])
                if wrapped:
                    root = c.node("unit-resolution", conclusion, [resolved])
                    document = c.document(root)
                    decl = len(document["decls"])
                    document["decls"].append({
                        "name": "or", "domain": [],
                        "range": document["decls"][0]["range"],
                        "interp": "op_or", "int_params": [],
                    })
                    expr = len(document["exprs"])
                    document["exprs"].append({"kind": "app", "decl": decl, "args": []})
                    document["proofs"][resolved]["conclusion"] = expr
                else:
                    document = c.document(resolved)
                self.check(document, 0)

    def test_mp_and_resolution_equalities_feed_congruence(self):
        for rule in ("mp", "mp-eq", "mp~", "unit-resolution"):
            with self.subTest(rule=rule):
                c = Certificate()
                sort = z3.DeclareSort("U", c.ctx)
                x, y = z3.Consts("x y", sort)
                p = z3.Bool("p", c.ctx)
                f = z3.Function("f", sort, sort)
                if rule.startswith("mp"):
                    relation = z3.Implies(p, x == y) if rule == "mp" else p == (x == y)
                    a, b = c.asserted(p), c.asserted(relation)
                    if rule == "mp~":
                        b = c.node("iff~", c.oeq(p, x == y), [b])
                else:
                    a = c.asserted(z3.Or(p, x == y))
                    b = c.asserted(z3.Not(p))
                equality = c.node("mp" if rule == "mp-eq" else rule,
                                  x == y, [a, b])
                congr = c.node("monotonicity", f(x) == f(y), [equality])
                opposite = c.asserted(z3.Not(f(x) == f(y)))
                root = c.node("unit-resolution", z3.BoolVal(False, c.ctx),
                              [congr, opposite])
                self.check(c.document(root), 0)

    def test_mp_checks_antecedent_and_consequent(self):
        for wrong in ("antecedent", "consequent"):
            with self.subTest(wrong=wrong):
                c = Certificate()
                p, q, r = z3.Bools("p q r", c.ctx)
                a = c.asserted(r if wrong == "antecedent" else p)
                implication = c.asserted(z3.Implies(p, q))
                conclusion = r if wrong == "consequent" else q
                derived = c.node("mp", conclusion, [a, implication])
                opposite = c.asserted(z3.Not(conclusion))
                root = c.node("unit-resolution", z3.BoolVal(False, c.ctx),
                              [derived, opposite])
                self.check(c.document(root), 1)

    def test_interleaved_resolution_equality_observation_and_mp(self):
        c = Certificate()
        sort = z3.DeclareSort("U", c.ctx)
        x, y = z3.Consts("x y", sort)
        p, q = z3.Bools("p q", c.ctx)
        f, g, h = [z3.Function(name, sort, sort) for name in ("f", "g", "h")]
        clause = c.asserted(z3.Or(p, x == y))
        unit = c.asserted(z3.Not(p))
        equal = c.node("unit-resolution", x == y, [clause, unit])
        congr = c.node("monotonicity", f(x) == f(y), [equal])
        bridge = c.asserted((f(x) == f(y)) == q)
        observed = c.node("iff~", c.oeq(f(x) == f(y), q), [bridge])
        logical = c.node("mp~", q, [congr, observed])
        implication = c.asserted(z3.Implies(q, g(x) == g(y)))
        equal_again = c.node("mp", g(x) == g(y), [logical, implication])
        outer = c.node("monotonicity", h(g(x)) == h(g(y)), [equal_again])
        opposite = c.asserted(z3.Not(h(g(x)) == h(g(y))))
        root = c.node("unit-resolution", z3.BoolVal(False, c.ctx), [outer, opposite])
        self.check(c.document(root), 0)

    def test_equality_hypothesis_discharge_feeds_congruence(self):
        c = Certificate()
        sort = z3.DeclareSort("U", c.ctx)
        x, y = z3.Consts("x y", sort)
        f = z3.Function("f", sort, sort)
        equality = c.asserted(x == y)
        hypothesis = c.node("hypothesis", z3.Not(x == y))
        contradiction = c.node("unit-resolution", z3.BoolVal(False, c.ctx),
                               [equality, hypothesis])
        discharged = c.node("lemma", x == y, [contradiction])
        congr = c.node("monotonicity", f(x) == f(y), [discharged])
        opposite = c.asserted(z3.Not(f(x) == f(y)))
        root = c.node("unit-resolution", z3.BoolVal(False, c.ctx), [congr, opposite])
        self.check(c.document(root), 0)

    def test_oeq_rule_shapes(self):
        for form in ("valid", "antecedent", "consequent", "implication",
                     "iff_conclusion", "iff_non_boolean", "iff_missing_premise",
                     "iff_equality_conclusion", "iff_oeq_premise"):
            with self.subTest(form=form):
                c = Certificate()
                p, q, r = z3.Bools("p q r", c.ctx)
                relation = z3.Implies(p, q) if form == "implication" else p == q
                if form == "iff_non_boolean":
                    x, y = z3.Ints("x y", c.ctx)
                    relation = x == y
                fact = (c.node("refl", c.oeq(p, p)) if form == "iff_oeq_premise"
                        else c.asserted(relation))
                converted_conclusion = c.oeq(p, r if form == "iff_conclusion" else q)
                if form == "iff_equality_conclusion":
                    converted_conclusion = p == q
                converted = c.node("iff~", converted_conclusion,
                                   [] if form == "iff_missing_premise" else [fact])
                a = c.asserted(r if form == "antecedent" else p)
                conclusion = r if form == "consequent" else q
                derived = c.node("mp~", conclusion, [a, converted])
                opposite = c.asserted(z3.Not(conclusion))
                root = c.node("unit-resolution", z3.BoolVal(False, c.ctx),
                              [derived, opposite])
                self.check(c.document(root), 0 if form == "valid" else 1)

    def test_mp_rules_do_not_exchange_relations(self):
        for rule, relation in (("mp~", "implies"), ("mp~", "="), ("mp", "~")):
            with self.subTest(rule=rule, relation=relation):
                c = Certificate()
                p, q = z3.Bools("p q", c.ctx)
                a = c.asserted(p)
                b = c.asserted(z3.Implies(p, q) if relation == "implies" else p == q)
                if relation == "~":
                    b = c.node("iff~", c.oeq(p, q), [b])
                derived = c.node(rule, q, [a, b])
                opposite = c.asserted(z3.Not(q))
                root = c.node("unit-resolution", z3.BoolVal(False, c.ctx),
                              [derived, opposite])
                self.check(c.document(root), 1)

    def test_oeq_composition_preserves_the_observational_judgment(self):
        for kind in ("refl", "symm", "trans", "mixed-trans", "trans*",
                     "monotonicity", "mixed-domain-congruence"):
            with self.subTest(kind=kind):
                c = Certificate()
                p, q, r = z3.Bools("p q r", c.ctx)
                first = c.asserted(p == q)
                pq = c.node("iff~", c.oeq(p, q), [first])
                last = c.asserted(q == r)
                qr = c.node("iff~", c.oeq(q, r), [last])
                source, target = p, r
                if kind == "refl":
                    source, target = p, p
                    derived = c.node(kind, c.oeq(p, p))
                elif kind == "symm":
                    source, target = q, p
                    derived = c.node(kind, c.oeq(q, p), [pq])
                elif kind == "trans*":
                    derived = c.node(kind, c.oeq(p, r), [qr, pq])
                elif kind in ("monotonicity", "mixed-domain-congruence"):
                    if kind == "monotonicity":
                        h = z3.Function("h", p.sort(), p.sort())
                        source, target = h(p), h(q)
                    else:
                        x = z3.Int("x", c.ctx)
                        h = z3.Function("h", x.sort(), p.sort(), p.sort())
                        source, target = h(x, p), h(x, q)
                    derived = c.node("monotonicity", c.oeq(source, target), [pq])
                else:
                    derived = c.node("trans", c.oeq(p, r),
                                     [first if kind == "mixed-trans" else pq, qr])
                initial = c.asserted(source)
                result = c.node("mp~", target, [initial, derived])
                opposite = c.asserted(z3.Not(target))
                root = c.node("unit-resolution", z3.BoolVal(False, c.ctx),
                              [result, opposite])
                document = c.document(root)
                self.check(document, 0)
                bad = copy.deepcopy(document)
                equality = c.converter._idx(c.converter.expr(source == target))
                bad["exprs"] = copy.deepcopy(c.converter.expr_json)
                bad["decls"] = copy.deepcopy(c.converter.decl_json)
                bad["proofs"][derived]["conclusion"] = equality
                self.check(bad, 1)

    def test_oeq_cannot_be_asserted_or_embedded_as_a_boolean_atom(self):
        for form in ("asserted", "hypothesis", "nested", "bad_tag"):
            with self.subTest(form=form):
                c = Certificate()
                p = z3.Bool("p", c.ctx)
                relation = c.oeq(p, p)
                if form in ("asserted", "hypothesis"):
                    relation_node = (c.asserted(relation) if form == "asserted"
                                     else c.node("hypothesis", relation))
                else:
                    relation_node = c.node("refl", relation)
                a = c.asserted(p)
                derived = c.node("mp~", p, [a, relation_node])
                opposite = c.asserted(z3.Not(p))
                if form == "nested":
                    c.asserted(z3.Not(relation))
                root = c.node("unit-resolution", z3.BoolVal(False, c.ctx),
                              [derived, opposite])
                doc = c.document(root)
                if form == "bad_tag":
                    next(d for d in doc["decls"] if d["name"] == "~")["interp"] = "op_eq"
                self.check(doc, 1)

    def test_refl_checks_identical_endpoints(self):
        for valid in (True, False):
            with self.subTest(valid=valid):
                c = Certificate()
                p, q = z3.Bools("p q", c.ctx)
                equality = p == (p if valid else q)
                derived = c.node("refl", equality)
                opposite = c.asserted(z3.Not(equality))
                root = c.node("unit-resolution", z3.BoolVal(False, c.ctx),
                              [derived, opposite])
                self.check(c.document(root), 0 if valid else 1)

    def test_hypothesis_discharge_is_local_to_a_derivation(self):
        for form in ("closed", "reused", "disjunction"):
            with self.subTest(form=form):
                c = Certificate()
                p = z3.Bool("p", c.ctx)
                if form == "disjunction":
                    p = z3.Or(p, z3.Bool("q", c.ctx))
                asserted = c.asserted(p)
                hypothesis = c.node("hypothesis", z3.Not(p))
                contradiction = c.node("unit-resolution", z3.BoolVal(False, c.ctx),
                                       [asserted, hypothesis])
                lemma = c.node("lemma", p, [contradiction])
                opposite = hypothesis if form == "reused" else c.asserted(z3.Not(p))
                root = c.node("unit-resolution", z3.BoolVal(False, c.ctx),
                              [lemma, opposite])
                self.check(c.document(root), 1 if form == "reused" else 0)

    def test_unverified_leaves_are_partial_not_certified(self):
        c = Certificate()
        root = c.node("trusted", z3.BoolVal(False, c.ctx), rule="th-lemma")
        self.check(c.document(root), 3)

    def test_not_or_elimination_handles_both_literal_polarities(self):
        for form in ("positive", "negative", "equality", "unrelated"):
            with self.subTest(form=form):
                c = Certificate()
                p, q, r = z3.Bools("p q r", c.ctx)
                x, y = z3.Ints("x y", c.ctx)
                target = z3.Not(p) if form == "negative" else x == y if form == "equality" else p
                selected = p if form == "negative" else z3.Not(target)
                premise = c.asserted(z3.Not(z3.Or(selected, q)))
                result = r if form == "unrelated" else target
                leaf = c.node("not-or-elim", result, [premise])
                opposite = c.asserted(z3.Not(result))
                root = c.node("unit-resolution", z3.BoolVal(False, c.ctx), [leaf, opposite])
                self.check(c.document(root), 1 if form == "unrelated" else 0)

    def test_array_theory_lemma_instances_are_checked(self):
        for form in ("same", "same_reversed", "other", "other_reordered", "ext",
                     "ext_reordered", "wrong_index", "wrong_guard", "wrong_base",
                     "arbitrary_witness", "unrelated_witness", "wrong_tag",
                     "unexpected_premise", "uninterpreted_select", "uninterpreted_ext"):
            with self.subTest(form=form):
                c = Certificate()
                index = z3.DeclareSort("Index", c.ctx)
                element = z3.DeclareSort("Element", c.ctx)
                a, b, d = z3.Consts("a b d", z3.ArraySort(index, element))
                i, j = z3.Consts("i j", index)
                v = z3.Const("v", element)
                stored = z3.Store(a, i, v)
                if form in ("same", "same_reversed", "wrong_index", "wrong_tag",
                            "unexpected_premise", "uninterpreted_select"):
                    selected = z3.Select(stored, j if form == "wrong_index" else i)
                    conclusion = v == selected if form == "same_reversed" else selected == v
                elif form in ("other", "other_reordered", "wrong_guard", "wrong_base"):
                    guard = i != j if form == "wrong_guard" else i == j
                    base = d if form == "wrong_base" else a
                    result = z3.Select(stored, j) == z3.Select(base, j)
                    conclusion = (z3.Or(z3.Select(base, j) == z3.Select(stored, j), j == i)
                                  if form == "other_reordered" else z3.Or(guard, result))
                else:
                    witness = (z3.Function("array-ext", a.sort(), a.sort(), index)(a, b)
                               if form == "uninterpreted_ext" else
                               i if form == "arbitrary_witness" else
                               z3.Ext(a, d) if form == "unrelated_witness" else z3.Ext(a, b))
                    opposite = z3.Not(z3.Select(a, witness) == z3.Select(b, witness))
                    conclusion = (z3.Or(opposite, b == a) if form == "ext_reordered"
                                  else z3.Or(a == b, opposite))
                premises = [c.asserted(z3.BoolVal(True, c.ctx))] if form == "unexpected_premise" else []
                leaf = c.node("trusted", conclusion, premises,
                              rule="arith" if form == "wrong_tag" else "th-lemma")
                opposite = c.asserted(z3.Not(conclusion))
                root = c.node("unit-resolution", z3.BoolVal(False, c.ctx), [leaf, opposite])
                document = c.document(root)
                if form == "uninterpreted_select":
                    for declaration in document["decls"]:
                        if declaration["name"] == "select":
                            declaration["interp"] = None
                valid = form in ("same", "same_reversed", "other", "other_reordered",
                                 "ext", "ext_reordered")
                self.check(document, 0 if valid else 3, obligations=None if valid else 1)

    def test_unverified_observational_steps_remain_partial(self):
        c = Certificate()
        p, q = z3.Bools("p q", c.ctx)
        relation = c.node("trusted", c.oeq(p, q), rule="apply-def")
        a = c.asserted(p)
        result = c.node("mp~", q, [a, relation])
        opposite = c.asserted(z3.Not(q))
        root = c.node("unit-resolution", z3.BoolVal(False, c.ctx),
                      [result, opposite])
        self.check(c.document(root), 3, obligations=1)

    def test_invalid_or_dangling_dependencies_are_rejected(self):
        for invalid in ("undeclared_assertion", "hypothesis", "forward", "negative", "self"):
            with self.subTest(invalid=invalid):
                c = Certificate()
                false = z3.BoolVal(False, c.ctx)
                if invalid == "undeclared_assertion":
                    root = c.node("asserted", false)
                elif invalid == "hypothesis":
                    root = c.node("hypothesis", false)
                else:
                    root = c.node("unit-resolution", false,
                                  [1 if invalid == "forward" else 0 if invalid == "self" else -1])
                self.check(c.document(root), 1)

    def test_false_cannot_be_spoofed_by_an_uninterpreted_declaration(self):
        c = Certificate()
        fake = z3.Bool("false", c.ctx)
        root = c.asserted(fake)
        document = c.document(root)
        self.assertIsNone(document["decls"][0]["interp"])
        self.check(document, 1)

    def test_transitivity_star_reconstructs_an_equality_path(self):
        c = Certificate()
        sort = z3.DeclareSort("U", c.ctx)
        x, y, z = z3.Consts("x y z", sort)
        a, b = c.asserted(z == y), c.asserted(x == y)
        trans = c.node("trans*", x == z, [a, b])
        opposite = c.asserted(z3.Not(x == z))
        root = c.node("unit-resolution", z3.BoolVal(False, c.ctx),
                      [trans, opposite])
        self.check(c.document(root), 0)
        bad = copy.deepcopy(c.document(root))
        bad["proofs"][trans]["premises"] = [a]
        self.check(bad, 1)

    def test_legacy_equational_documents_remain_accepted(self):
        _, proof = extractor.build_example()
        converter = extractor.Converter()
        root = converter.proof(extractor.find_equational_root(proof))
        unmatched = sum(name is None for _, _, name in converter.rewrite_log)
        self.check(extractor.build_proof_doc(converter, root, unmatched), 0)

    def test_full_shared_dag_counts_a_shared_obligation_once(self):
        c = Certificate()
        p, q = z3.Bools("p q", c.ctx)
        leaf = c.node("rewrite", p == q)
        reverse = c.node("symm", q == p, [leaf])
        shared = c.node("trans", p == p, [leaf, reverse])
        for _ in range(40):
            shared = c.node("trans", p == p, [shared, shared])
        opposite = c.asserted(z3.Not(p == p))
        root = c.node("unit-resolution", z3.BoolVal(False, c.ctx), [shared, opposite])
        self.check(c.document(root), 3, obligations=1)

    def test_legacy_shared_dag_caches_success_and_failure(self):
        for form in ("valid", "invalid", "unused_invalid", "self", "forward", "negative"):
            with self.subTest(form=form):
                doc = {
                    "sorts": [{"kind": "base", "name": "Bool"}],
                    "decls": [{"name": name, "domain": [], "range": 0, "interp": None}
                              for name in ("p", "q")],
                    "exprs": [{"kind": "app", "decl": i, "args": []} for i in range(2)],
                    "proofs": [{"kind": "refl", "e": 0}, {"kind": "refl", "e": 1}],
                    "root": 0,
                    "unmatched_count": 0,
                }
                proofs = doc["proofs"]
                proofs.append({"kind": "trans", "p1": 0, "p2": 1 if form != "valid" else 0})
                if form in ("self", "forward", "negative"):
                    proofs[-1]["p1"] = {"self": 2, "forward": 3, "negative": -1}[form]
                for _ in range(40):
                    previous = len(proofs) - 1
                    proofs.append({"kind": "trans", "p1": previous, "p2": previous})
                if form != "unused_invalid":
                    doc["root"] = len(proofs) - 1
                self.check(doc, 0 if form in ("valid", "unused_invalid") else 1)

    def test_expression_cache_rejects_invalid_references(self):
        for index in (-1, 0, 1):
            with self.subTest(index=index):
                c = Certificate()
                root = c.asserted(z3.BoolVal(False, c.ctx))
                doc = c.document(root)
                doc["exprs"][0]["args"] = [index]
                self.check(doc, 1)


if __name__ == "__main__":
    unittest.main()
