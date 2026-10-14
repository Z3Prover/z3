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


@unittest.skipUnless(os.environ.get("Z3_FSTAR_CHECKER"),
                     "Set Z3_FSTAR_CHECKER to the built native checker")
class NativeCheckerTests(unittest.TestCase):
    def check(self, document, expected, obligations=None):
        checker = os.environ["Z3_FSTAR_CHECKER"]
        command = (["wsl", "-e", "bash", "-c", checker] if os.name == "nt"
                   else [os.path.expanduser(checker)])
        result = subprocess.run(command, input=json.dumps(document),
                                capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, expected,
                         result.stdout + result.stderr)
        self.assertEqual(result.stdout.strip().split()[0],
                         {0: "ACCEPT", 1: "REJECT", 3: "PARTIAL"}[expected])
        if obligations is not None:
            self.assertEqual(result.stdout.strip(), "PARTIAL %d" % obligations)

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
        for invalid in ("undeclared_assertion", "hypothesis", "forward", "negative"):
            with self.subTest(invalid=invalid):
                c = Certificate()
                false = z3.BoolVal(False, c.ctx)
                if invalid == "undeclared_assertion":
                    root = c.node("asserted", false)
                elif invalid == "hypothesis":
                    root = c.node("hypothesis", false)
                else:
                    root = c.node("unit-resolution", false,
                                  [1 if invalid == "forward" else -1])
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


if __name__ == "__main__":
    unittest.main()
