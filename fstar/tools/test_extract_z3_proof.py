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
                        NativeCheckerTests().check(doc, 3 if pending else 0, strict=True,
                                                   obligations=pending if pending else None)

    def test_real_nnf_definition_introductions_are_checked_not_trusted(self):
        ctx = z3.Context(proof=True)
        x, y = z3.Ints("x y", ctx)
        p = z3.Bool("p", ctx)
        solver = z3.Then(z3.With(z3.Tactic("nnf", ctx=ctx), mode="full"),
                         z3.Tactic("smt", ctx=ctx)).solver()
        solver.add(z3.If(p, x, y) > 0, x <= 0, y <= 0)
        self.assertEqual(solver.check(), z3.unsat)
        converter = extractor.ResolutionConverter()
        root = converter.proof(solver.proof())
        doc = extractor.build_resolution_doc(converter, root, solver.assertions())
        self.assertIn("intro-def", {n["kind"] for n in doc["proofs"]})
        self.assertNotIn("intro-def", {rule for rule, _ in converter.trusted_log})
        if os.environ.get("Z3_FSTAR_CHECKER"):
            NativeCheckerTests().check(doc, 3)
            isolated = copy.deepcopy(doc)
            intro = next(n for n in isolated["proofs"] if n["kind"] == "intro-def")
            false = isolated["proofs"][isolated["root"]]["conclusion"]
            isolated["proofs"] = [intro, {"kind": "asserted", "conclusion": false,
                                           "premises": []}]
            isolated["assertions"] = [false]
            isolated["root"] = 1
            NativeCheckerTests().check(isolated, 0, strict=True)

    def test_real_distinct_def_axioms_are_independently_checked(self):
        ctx = z3.Context(proof=True)
        args = z3.Consts("a b c d e f g h i", z3.DeclareSort("DistinctU", ctx))
        p = z3.Bool("p", ctx)
        solver = z3.Solver(ctx=ctx)
        solver.add(z3.Or(z3.Distinct(args), p), args[0] == args[1], z3.Not(p))
        self.assertEqual(solver.check(), z3.unsat)
        converter = extractor.ResolutionConverter()
        root = converter.proof(solver.proof())
        doc = extractor.build_resolution_doc(converter, root, solver.assertions())
        self.assertTrue(any(d["interp"] == "op_distinct" for d in doc["decls"]))
        self.assertTrue(any(n["kind"] == "def-axiom" for n in doc["proofs"]))
        if os.environ.get("Z3_FSTAR_CHECKER"):
            NativeCheckerTests().check(doc, 0, strict=True)

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

    def test_full_proof_numerals_have_distinct_structural_identities(self):
        ctx = z3.Context()
        for values in ((z3.IntVal(1, ctx), z3.IntVal(2, ctx)),
                       (z3.RealVal("1/3", ctx), z3.RealVal("2/3", ctx)),
                       (z3.BitVecVal(1, 8, ctx), z3.BitVecVal(2, 8, ctx))):
            with self.subTest(sort=str(values[0].sort())):
                converter = extractor.ResolutionConverter()
                for value in values:
                    converter.expr(value)
                self.assertNotEqual(converter.decl_json[0], converter.decl_json[1])

    def test_arithmetic_export_preserves_exact_numbers_and_authentic_parameters(self):
        c = Certificate()
        x = z3.Real("x", c.ctx)
        solver = z3.Solver(ctx=c.ctx)
        solver.set("arith.solver", 2)
        solver.add(x > 1, x < 0)
        self.assertEqual(solver.check(), z3.unsat)
        root = c.converter.proof(solver.proof())
        document = extractor.build_resolution_doc(c.converter, root, solver.assertions())
        lemmas = [n for n in document["proofs"] if n.get("theory_params", [])[:2]
                  == ["arith", "farkas"]]
        self.assertTrue(lemmas)
        for lemma in lemmas:
            certificate = lemma["arithmetic_certificate"]
            self.assertEqual(certificate["origin"], "z3")
            expected = [extractor.Fraction(p) for p in lemma["theory_params"][2:]]
            self.assertEqual(certificate["coefficients"],
                             [[p.numerator, p.denominator] for p in expected])
        converter = extractor.ResolutionConverter()
        for n, d in ((1 << 150, 1), (-(1 << 145), 17)):
            number = z3.RealVal("%d/%d" % (n, d), c.ctx)
            declaration = converter.decl_json[
                converter._idx(converter.func_decl(number.decl(), 0))]
            self.assertEqual(declaration["interp"], "op_num_rational")
            fraction = extractor.Fraction(n, d)
            self.assertEqual(declaration["int_params"],
                             [fraction.numerator, fraction.denominator])

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

    def test_farkas_checks_exact_arithmetic_ast_bridges(self):
        for form in ("rational", "subtraction", "unary", "nary", "division",
                     "to_real", "positive_eq", "negative_eq", "fractional_weights",
                     "huge", "opaque_product"):
            with self.subTest(form=form):
                c = Certificate()
                x, y, z = z3.Reals("x y z", c.ctx)
                weights = [[1, 1], [1, 1]]
                if form == "rational":
                    facts, weights = [x / 3 >= z3.RealVal("2/3", c.ctx), x <= 1], [[3, 1], [1, 1]]
                elif form == "subtraction":
                    facts = [x - y >= 1, y - x >= 0]
                elif form == "unary":
                    facts = [-x > 0, x >= 0]
                elif form == "nary":
                    facts = [x + y + z > 0, -x - y - z >= 0]
                elif form == "division":
                    facts, weights = [x / -2 >= 1, x >= 0], [[2, 1], [1, 1]]
                elif form == "to_real":
                    a = z3.Int("a", c.ctx)
                    facts = [z3.ToReal(a) >= 1, z3.ToReal(a) <= 0]
                elif form == "positive_eq":
                    facts = [x == 1, x >= 2]
                elif form == "negative_eq":
                    facts, weights = [x == 1, x <= 0], [[-1, 1], [1, 1]]
                elif form == "fractional_weights":
                    facts, weights = [x > 0, x <= 0], [[1, 3], [1, 3]]
                elif form == "huge":
                    facts = [x >= 1 << 150, x <= (1 << 150) - 1]
                else:
                    facts = [x * y >= 1, x * y <= 0]
                premises = [c.asserted(f) for f in facts]
                root = c.node("trusted", z3.BoolVal(False, c.ctx), premises, rule="th-lemma",
                              arithmetic_certificate={"kind": "farkas", "coefficients": weights})
                self.check(c.document(root), 0, strict=True)

    def test_integer_strict_bounds_are_not_rounded_for_reals(self):
        for integral in (False, True):
            with self.subTest(integral=integral):
                c = Certificate()
                x = z3.Int("x", c.ctx) if integral else z3.Real("x", c.ctx)
                premises = [c.asserted(x > 0), c.asserted(x < 1)]
                root = c.node("trusted", z3.BoolVal(False, c.ctx), premises, rule="th-lemma",
                              arithmetic_certificate={"kind": "farkas", "coefficients": [[1, 1], [1, 1]]})
                self.check(c.document(root), 0 if integral else 3,
                           obligations=None if integral else 1)

    def test_composed_bound_weights_must_be_preserved(self):
        for composed in (False, True):
            with self.subTest(composed=composed):
                c = Certificate()
                x, y, z = z3.Reals("x y z", c.ctx)
                premises = [c.asserted(f) for f in (x == 2 * y, y == 3 * z, z >= 1, x <= 5)]
                weights = [-1, -2, 6, 1] if composed else [-1, -1, 1, 1]
                root = c.node("trusted", z3.BoolVal(False, c.ctx), premises, rule="th-lemma",
                              arithmetic_certificate={"kind": "farkas",
                                                      "coefficients": [[w, 1] for w in weights]})
                self.check(c.document(root), 0 if composed else 3,
                           obligations=None if composed else 1)

    def test_actual_z3_farkas_clause_is_checked_without_its_other_proof_steps(self):
        c = Certificate()
        x = z3.Real("x", c.ctx)
        solver = z3.Solver(ctx=c.ctx)
        solver.set("arith.solver", 2)
        solver.add(x > 1, x < 0)
        self.assertEqual(solver.check(), z3.unsat)
        stack = [solver.proof()]
        seen = set()
        checked = 0
        while stack:
            node = stack.pop()
            if node.get_id() in seen:
                continue
            seen.add(node.get_id())
            if str(node.decl().name()) == "th-lemma":
                params = [str(p) for p in node.decl().params()]
                if params[:2] == ["arith", "farkas"]:
                    conclusion = node.arg(node.num_args() - 1)
                    cs = [extractor.Fraction(p) for p in params[2:]]
                    leaf = c.node("trusted", conclusion, rule="th-lemma", theory_params=params,
                                  arithmetic_certificate={"kind": "farkas", "origin": "z3",
                                                          "coefficients": [[v.numerator, v.denominator] for v in cs]})
                    opposite = c.asserted(z3.Not(conclusion))
                    root = c.node("unit-resolution", z3.BoolVal(False, c.ctx), [leaf, opposite])
                    self.check(c.document(root), 0, strict=True)
                    checked += 1
            stack.extend(child for child in node.children() if child.sort().kind() == 1000)
        self.assertGreater(checked, 0)

    def test_invalid_or_missing_arithmetic_evidence_is_not_certified(self):
        for form in ("bare", "wrong_rule", "wrong_weights", "too_short", "too_long",
                     "negated_eq", "zero_strict", "different_atoms", "spoofed_operator",
                     "unsupported_cut", "integer_cut"):
            with self.subTest(form=form):
                c = Certificate()
                x, y = z3.Reals("x y", c.ctx)
                facts, weights = [x >= 1, x <= 0], [[1, 1], [1, 1]]
                if form == "wrong_weights":
                    weights = [[2, 1], [1, 1]]
                elif form == "too_short":
                    weights = weights[:1]
                elif form == "too_long":
                    weights += [[1, 1]]
                elif form == "negated_eq":
                    facts = [x != 0, x == 0]
                elif form == "zero_strict":
                    facts, weights = [x > x, x <= x], [[0, 1], [1, 1]]
                elif form == "different_atoms":
                    facts = [x * x >= 1, x * y <= 0]
                elif form == "spoofed_operator":
                    fake = z3.Function("+", x.sort(), x.sort(), x.sort())
                    facts = [fake(x, y) >= 1, x + y <= 0]
                elif form == "integer_cut":
                    a = z3.Int("a", c.ctx)
                    facts = [2 * a >= 1, 2 * a <= 1]
                premises = [c.asserted(f) for f in facts]
                certificate = {"kind": "gomory" if form == "unsupported_cut" else "farkas",
                               "coefficients": weights}
                root = c.node("trusted", z3.BoolVal(False, c.ctx), premises,
                              rule="not-arithmetic" if form == "wrong_rule" else "th-lemma",
                              **({} if form == "bare" else {"arithmetic_certificate": certificate}))
                self.check(c.document(root), 3, obligations=1)

    def test_malformed_arithmetic_coefficients_are_rejected(self):
        for coefficients in ([[1, 0], [1, 1]], [[1, -1], [1, 1]], [[True, 1], [1, 1]],
                             [[1, 1, 1], [1, 1]], "1 1"):
            with self.subTest(coefficients=coefficients):
                c = Certificate()
                x = z3.Int("x", c.ctx)
                premises = [c.asserted(x >= 1), c.asserted(x <= 0)]
                root = c.node("trusted", z3.BoolVal(False, c.ctx), premises, rule="th-lemma",
                              arithmetic_certificate={"kind": "farkas", "coefficients": coefficients})
                self.check(c.document(root), 1)

    def test_arithmetic_lemmas_preserve_and_discharge_hypotheses(self):
        for discharge in (False, True):
            with self.subTest(discharge=discharge):
                c = Certificate()
                x = z3.Real("x", c.ctx)
                facts = [x >= 1, x <= 0]
                premises = [c.node("hypothesis", f) for f in facts]
                root = c.node("trusted", z3.BoolVal(False, c.ctx), premises, rule="th-lemma",
                              arithmetic_certificate={"kind": "farkas", "coefficients": [[1, 1], [1, 1]]})
                if discharge:
                    conclusion = z3.Or(*[z3.Not(f) for f in facts])
                    lemma = c.node("lemma", conclusion, [root])
                    opposite = c.asserted(z3.Not(conclusion))
                    root = c.node("unit-resolution", z3.BoolVal(False, c.ctx), [lemma, opposite])
                self.check(c.document(root), 0 if discharge else 1)

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

    def test_boolean_ite_rewrites(self):
        for form in ("expanded", "negation", "nested", "wide",
                     "wide_then_true", "wide_else_true", "true_condition", "false_condition",
                     "non_equivalent", "non_boolean", "uninterpreted",
                     "spoofed_name", "spoofed_tag"):
            with self.subTest(form=form):
                c = Certificate()
                p, q, r = z3.Bools("p q r", c.ctx)
                ps = z3.Bools(" ".join("a%d" % i for i in range(12)), c.ctx)
                left, right = {
                    "expanded": (z3.If(p, q, r), z3.Or(z3.And(p, q), z3.And(z3.Not(p), r))),
                    "negation": (z3.If(p, False, True), z3.Not(p)),
                    "nested": (z3.If(z3.If(p, False, True),
                                     z3.If(q, r, False), False),
                               z3.And(z3.Not(p), q, r)),
                    "wide": (z3.If(ps[0], z3.And(*ps[1:]), False), z3.And(*ps)),
                    "wide_then_true": (z3.If(ps[0], True, z3.And(*ps[1:])),
                                       z3.Or(ps[0], z3.And(*ps[1:]))),
                    "wide_else_true": (z3.If(ps[0], z3.And(*ps[1:]), True),
                                       z3.Or(z3.Not(ps[0]), z3.And(*ps[1:]))),
                    "true_condition": (z3.If(True, p, q), p),
                    "false_condition": (z3.If(False, p, q), q),
                    "non_equivalent": (z3.If(p, q, r), z3.If(p, r, q)),
                    "non_boolean": (z3.If(p, 1, 2), z3.If(z3.Not(p), 2, 1)),
                }.get(form, (z3.If(p, q, r), z3.Or(z3.And(p, q), z3.And(z3.Not(p), r))))
                valid = form not in ("non_equivalent", "non_boolean")
                self.assertEqual(extractor._bounded_boolean_equiv(left, right), valid)
                equality = left == right
                rewrite = c.node("rewrite", equality)
                opposite = c.asserted(z3.Not(equality))
                root = c.node("unit-resolution", z3.BoolVal(False, c.ctx), [rewrite, opposite])
                doc = c.document(root)
                if form in ("uninterpreted", "spoofed_name", "spoofed_tag"):
                    declaration = next(d for d in doc["decls"] if d["name"] == "if")
                    if form == "spoofed_name":
                        declaration["name"] = "fake_ite"
                    else:
                        declaration["interp"] = None if form == "uninterpreted" else "op_implies"
                    valid = False
                self.check(doc, 0 if valid else 3, obligations=None if valid else 1)

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
                self.check(c.document(root), 0 if form == "opaque" else 3,
                           obligations=None if form == "opaque" else 1)

    def test_contextual_array_rewrites(self):
        for form in ("overwrite", "redundant", "same_index", "read_ite",
                     "reversed_guard", "nested", "array_ite", "true_ite",
                     "false_ite", "reflexive_guard", "equal_branches", "context_branches"):
            with self.subTest(form=form):
                c = Certificate()
                index, element = z3.DeclareSort("I", c.ctx), z3.DeclareSort("E", c.ctx)
                a, b = z3.Consts("a b", z3.ArraySort(index, element))
                i, j = z3.Consts("i j", index)
                v, w = z3.Consts("v w", element)
                p = z3.Bool("p", c.ctx)
                stored = z3.Store(a, i, v)
                overwritten = z3.Store(stored, i, w)
                reduced = z3.Store(a, i, w)
                expanded = z3.If(i == j, v, z3.Select(a, j))
                left, right = {
                    "overwrite": (overwritten, reduced),
                    "redundant": (z3.Store(a, i, z3.Select(a, i)), a),
                    "same_index": (z3.Select(stored, i), v),
                    "read_ite": (z3.Select(stored, j), expanded),
                    "reversed_guard": (z3.Select(stored, j),
                                       z3.If(j == i, v, z3.Select(a, j))),
                    "nested": (z3.Not(z3.Store(overwritten, j, z3.Select(stored, j)) == b),
                               z3.Not(z3.Store(reduced, j, expanded) == b)),
                    "array_ite": (z3.If(p, overwritten, reduced), reduced),
                    "true_ite": (z3.If(True, v, w), v),
                    "false_ite": (z3.If(False, v, w), w),
                    "reflexive_guard": (z3.If(i == i, v, w), v),
                    "equal_branches": (z3.If(p, v, v), v),
                    "context_branches": (z3.If(p, z3.Select(stored, i), v), v),
                }[form]
                self.assertTrue(extractor._contextual_array_equiv(left, right))
                self.assertEqual(extractor.classify_full_rewrite(left, right),
                                 "contextual_array")
                for source, target in ((left, right), (right, left)):
                    equality = source == target
                    rewrite = c.node("rewrite", equality)
                    opposite = c.asserted(z3.Not(equality))
                    root = c.node("unit-resolution", z3.BoolVal(False, c.ctx),
                                  [rewrite, opposite])
                    self.check(c.document(root), 0)

    def test_contextual_array_rewrites_preserve_unknowns_and_sorts(self):
        for form in ("fresh", "distinct_indices", "wrong_value", "wrong_base",
                     "bool_element", "nested_array", "budget", "spoof_select",
                     "spoof_store", "spoof_ite", "wrong_ite_type", "distinct_numerals"):
            with self.subTest(form=form):
                c = Certificate()
                integer = z3.IntSort(c.ctx)
                a, b = z3.Consts("a b", z3.ArraySort(integer, integer))
                i, j, v, w = z3.Ints("i j v w", c.ctx)
                stored = z3.Store(a, i, v)
                left, right = {
                    "fresh": (stored, b),
                    "distinct_indices": (z3.Select(stored, j), z3.Select(a, j)),
                    "wrong_value": (z3.Select(stored, j),
                                    z3.If(i == j, w, z3.Select(a, j))),
                    "wrong_base": (z3.Select(stored, j),
                                   z3.If(i == j, v, z3.Select(b, j))),
                }.get(form, (z3.Select(stored, j), z3.If(i == j, v, z3.Select(a, j))))
                if form == "distinct_numerals":
                    left, right = z3.IntVal(1, c.ctx), z3.IntVal(2, c.ctx)
                elif form in ("bool_element", "nested_array"):
                    sort = z3.BoolSort(c.ctx) if form == "bool_element" else a.sort()
                    base = z3.Const("base", z3.ArraySort(integer, sort))
                    value = z3.Const("value", sort)
                    left, right = z3.Store(z3.Store(base, i, value), i, value), z3.Store(base, i, value)
                elif form == "budget":
                    f = z3.Function("f", integer, integer)
                    left, right = z3.Select(stored, i), v
                    for _ in range(65):
                        left, right = f(left), f(right)
                if not form.startswith("spoof") and form != "wrong_ite_type":
                    self.assertFalse(extractor._contextual_array_equiv(left, right))
                equality = left == right
                rewrite = c.node("rewrite", equality)
                opposite = c.asserted(z3.Not(equality))
                root = c.node("unit-resolution", z3.BoolVal(False, c.ctx), [rewrite, opposite])
                doc = c.document(root)
                if form.startswith("spoof"):
                    name = {"spoof_select": "select", "spoof_store": "store",
                            "spoof_ite": "if"}[form]
                    next(d for d in doc["decls"] if d["name"] == name)["interp"] = None
                elif form == "wrong_ite_type":
                    next(d for d in doc["decls"] if d["name"] == "if")["domain"][1] = \
                        next(n for n, s in enumerate(doc["sorts"]) if s.get("name") == "Bool")
                self.check(doc, 1 if form == "wrong_ite_type" else 3,
                           obligations=None if form == "wrong_ite_type" else 1)

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

    def test_def_axiom_is_not_discharged_by_input_membership(self):
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
                        self.check(doc, 3, obligations=1)
                        self.check(doc, 3, strict=True, obligations=1)

    def test_def_axiom_checks_tseitin_and_fresh_skolem_witnesses(self):
        for form in ("tseitin", "ite_term", "equation", "boolean_pair",
                     "reversed_boolean_pair", "guard_pair", "quantified_pair",
                     "used_symbol", "conflict", "cycle", "missing_guard",
                     "arbitrary_false", "spoofed_gate"):
            with self.subTest(form=form):
                c = Certificate()
                p, q, k = z3.Bools("p q k", c.ctx)
                x, y, n = z3.Ints("x y n", c.ctx)
                if form == "tseitin":
                    axioms = [z3.Or(z3.Not(z3.And(p, q)), p)]
                elif form == "ite_term":
                    axioms = [z3.Or(z3.Not(p), z3.If(p, x, y) == x),
                              z3.Or(p, z3.If(p, x, y) == y)]
                elif form in ("boolean_pair", "reversed_boolean_pair"):
                    body = z3.And(p, q)
                    clauses = [z3.Or(k, z3.Not(body)), z3.Or(z3.Not(k), body)]
                    axioms = [z3.And(*(reversed(clauses) if form.startswith("reversed")
                                       else clauses))]
                elif form in ("equation", "used_symbol", "conflict", "cycle"):
                    axioms = [k == z3.And(p, q)]
                    if form == "used_symbol":
                        c.assertions.append(k)
                    elif form == "conflict":
                        axioms.append(k == z3.Or(p, q))
                    elif form == "cycle":
                        axioms = [k == z3.Not(k)]
                elif form == "quantified_pair":
                    f = z3.Function("sk", x.sort(), x.sort())
                    axioms = [z3.ForAll(x, z3.Or(z3.Not(p), f(x) == x)),
                              z3.ForAll(x, z3.Or(p, f(x) == y))]
                elif form in ("guard_pair", "missing_guard"):
                    axioms = [z3.Or(z3.Not(p), n == x)]
                    if form == "guard_pair":
                        axioms.append(z3.Or(p, n == y))
                elif form == "spoofed_gate":
                    fake = z3.Function("fake_and", p.sort(), p.sort(), p.sort())
                    axioms = [z3.Or(z3.Not(fake(p, q)), p)]
                else:
                    axioms = [z3.BoolVal(False, c.ctx)]
                for axiom in axioms:
                    c.node("def-axiom", axiom)
                root = c.asserted(z3.BoolVal(False, c.ctx))
                doc = c.document(root)
                if form == "spoofed_gate":
                    next(d for d in doc["decls"] if d["name"] == "fake_and")["name"] = "and"
                rejected = form in ("used_symbol", "conflict", "cycle", "spoofed_gate")
                pending = form in ("missing_guard", "arbitrary_false")
                self.check(doc, 1 if rejected else 3 if pending else 0, strict=True,
                           obligations=1 if pending else None)

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

    def test_def_axiom_tseitin_schemas_with_wide_compound_operands(self):
        c = Certificate()
        atoms = z3.Bools(" ".join("p%d" % i for i in range(48)), c.ctx)
        p, q, r = (z3.And(*atoms[i:i + 16]) for i in (0, 16, 32))
        for arguments in ([p, q], atoms):
            conjunction, disjunction = z3.And(*arguments), z3.Or(*arguments)
            for a in arguments:
                c.node("def-axiom", z3.Or(z3.Not(conjunction), a))
                c.node("def-axiom", z3.Or(disjunction, z3.Not(a)))
            c.node("def-axiom", z3.Or(conjunction, *[z3.Not(a) for a in arguments]))
            c.node("def-axiom", z3.Or(z3.Not(disjunction), *arguments))
        for gate in (p == q, z3.Xor(p, q)):
            xor = z3.is_app_of(gate, z3.Z3_OP_XOR)
            for left in (False, True):
                for right in (False, True):
                    value = left != right if xor else left == right
                    c.node("def-axiom", z3.Or(gate if value else z3.Not(gate),
                                             z3.Not(p) if left else p,
                                             z3.Not(q) if right else q))
        implication = z3.Implies(p, q)
        for axiom in (z3.Or(z3.Not(implication), z3.Not(p), q),
                      z3.Or(implication, p), z3.Or(implication, z3.Not(q)),
                      z3.Or(z3.Not(z3.If(p, q, r)), z3.Not(p), q),
                      z3.Or(z3.Not(z3.If(p, q, r)), p, r),
                      z3.Or(z3.If(p, q, r), z3.Not(p), z3.Not(q)),
                      z3.Or(z3.If(p, q, r), p, z3.Not(r)),
                      z3.Or(z3.Not(z3.Not(p)), z3.Not(p))):
            c.node("def-axiom", axiom)
        root = c.asserted(z3.BoolVal(False, c.ctx))
        self.check(c.document(root), 0, strict=True)

    def test_asserted_leaves_require_exact_input_membership_in_both_modes(self):
        for strict in (False, True):
            for form in ("missing", "equivalent", "matching"):
                with self.subTest(strict=strict, form=form):
                    c = Certificate()
                    false = z3.BoolVal(False, c.ctx)
                    root = c.node("asserted", false)
                    if form != "missing":
                        c.assertions.append(false if form == "matching" else
                                            z3.Or(false, false))
                    self.check(c.document(root), 0 if form == "matching" else 1,
                               strict=strict)

    def test_distinct_expansion_axioms_cover_arities_sorts_and_both_directions(self):
        for arity, kind in ((0, "uf"), (1, "uf"), (2, "uf"), (3, "uf"),
                            (9, "uf"), (209, "uf"), (3, "bool"), (3, "array")):
            with self.subTest(arity=arity, kind=kind):
                c = Certificate()
                sort = {"uf": z3.DeclareSort("DistinctU", c.ctx),
                        "bool": z3.BoolSort(c.ctx),
                        "array": z3.ArraySort(z3.IntSort(c.ctx), z3.IntSort(c.ctx))}[kind]
                args = [z3.Const("a%d" % i, sort) for i in range(arity)]
                distinct = (z3.Distinct(args) if args else
                            z3.Bool("empty_distinct", c.ctx))
                pairs = [z3.Not(a == b) for i, a in enumerate(args) for b in args[i + 1:]]
                expanded = (z3.BoolVal(True, c.ctx) if arity < 2 else
                            pairs[0] if arity == 2 else z3.And(*pairs))
                for a, b in ((z3.Not(distinct), expanded),
                             (distinct, z3.Not(expanded))):
                    c.node("def-axiom", z3.Or(a, b))
                    c.node("def-axiom", z3.Or(b, a))
                if arity == 2:
                    c.node("def-axiom", z3.Or(distinct, args[0] == args[1]))
                root = c.asserted(z3.BoolVal(False, c.ctx))
                doc = c.document(root)
                if not args:
                    declaration = next(d for d in doc["decls"] if d["name"] == "empty_distinct")
                    declaration.update(name="distinct", interp="op_distinct")
                self.check(doc, 0, strict=True)

    def test_distinct_expansion_is_used_in_a_refutation(self):
        c = Certificate()
        a, b, d = z3.Consts("a b d", z3.DeclareSort("DistinctU", c.ctx))
        distinct = z3.Distinct(a, b, d)
        expanded = z3.And(z3.Not(a == b), z3.Not(a == d), z3.Not(b == d))
        axiom = c.node("def-axiom", z3.Or(z3.Not(distinct), expanded))
        original = c.asserted(distinct)
        consequence = c.node("unit-resolution", expanded, [axiom, original])
        opposite = c.asserted(z3.Not(expanded))
        root = c.node("unit-resolution", z3.BoolVal(False, c.ctx), [consequence, opposite])
        self.check(c.document(root), 0, strict=True)

    def test_invalid_distinct_expansions_are_not_certified(self):
        for form in ("missing_pair", "duplicate_pair", "wrong_pair", "wrong_polarity",
                     "spoofed_tag", "missing_tag", "spoofed_name", "parameters",
                     "heterogeneous"):
            with self.subTest(form=form):
                c = Certificate()
                sort = z3.DeclareSort("DistinctU", c.ctx)
                a, b, d, other = z3.Consts("a b d other", sort)
                distinct = z3.Distinct(a, b, d)
                pairs = [z3.Not(a == b), z3.Not(a == d), z3.Not(b == d)]
                if form == "missing_pair":
                    pairs.pop()
                elif form == "duplicate_pair":
                    pairs[2] = pairs[1]
                elif form == "wrong_pair":
                    pairs[2] = z3.Not(b == other)
                elif form == "heterogeneous":
                    x = z3.Int("x", c.ctx)
                    distinct = z3.Function("heterogeneous", sort, x.sort(), z3.BoolSort(c.ctx))(a, x)
                    pairs = [z3.Not(a == b)]
                expanded = z3.And(*pairs)
                clause = (z3.Or(z3.Not(distinct), z3.Not(expanded))
                          if form == "wrong_polarity" else
                          z3.Or(distinct, z3.Not(expanded)))
                c.node("def-axiom", clause)
                root = c.asserted(z3.BoolVal(False, c.ctx))
                doc = c.document(root)
                declaration = next(d for d in doc["decls"]
                                   if d["name"] in ("distinct", "heterogeneous"))
                if form == "spoofed_tag":
                    declaration["interp"] = "op_eq"
                elif form == "missing_tag":
                    declaration["interp"] = None
                elif form == "spoofed_name":
                    declaration["name"] = "not_distinct"
                elif form == "parameters":
                    declaration["int_params"] = [1]
                elif form == "heterogeneous":
                    declaration.update(name="distinct", interp="op_distinct")
                rejected = form in ("spoofed_tag", "missing_tag", "parameters", "heterogeneous")
                self.check(doc, 1 if rejected else 3,
                           obligations=None if rejected else 1)

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
        relation = c.node("trusted", c.oeq(p, q), rule="nnf-pos")
        a = c.asserted(p)
        result = c.node("mp~", q, [a, relation])
        opposite = c.asserted(z3.Not(q))
        root = c.node("unit-resolution", z3.BoolVal(False, c.ctx),
                      [result, opposite])
        self.check(c.document(root), 3, obligations=1)

    def test_accumulated_definitions_feed_the_checked_derivation(self):
        for legacy in (False, True):
            with self.subTest(legacy=legacy):
                c = Certificate()
                p, k, k2 = z3.Bools("p k k2", c.ctx)
                intro = c.node("trusted" if legacy else "intro-def", p == k,
                               **({"rule": "intro-def"} if legacy else {}))
                intro2 = c.node("intro-def", z3.Not(k) == k2)
                relation = c.node("trusted" if legacy else "apply-def", c.oeq(p, k),
                                  [intro], **({"rule": "apply-def"} if legacy else {}))
                original = c.asserted(p)
                renamed = c.node("mp~", k, [original, relation])
                inverse = c.node("apply-def", c.oeq(k, z3.Not(k2)), [intro, intro2])
                renamed_again = c.node("mp~", z3.Not(k2), [renamed, inverse])
                opposite = c.asserted(z3.Not(p))
                forward = c.node("apply-def", c.oeq(z3.Not(p), k2), [intro2])
                other = c.node("mp~", k2, [opposite, forward])
                root = c.node("unit-resolution", z3.BoolVal(False, c.ctx),
                              [renamed_again, other])
                self.check(c.document(root), 0)
                self.check(c.document(root), 0, strict=True)

    def test_ground_and_quantified_definition_schemas(self):
        for form in ("equation", "boolean", "positive", "ite", "function",
                     "permuted_parameters", "quantified_boolean", "quantified_ite",
                     "capture_avoidance", "forward_dependencies", "repeated"):
            with self.subTest(form=form):
                c = Certificate()
                u = z3.DeclareSort("U", c.ctx)
                x, y, a, b = z3.Consts("x y a b", u)
                p, q, k, k2 = z3.Bools("p q k k2", c.ctx)
                f, g = z3.Function("f", u, u), z3.Function("g", u, u)
                bf, bg = z3.Function("bf", u, p.sort()), z3.Function("bg", u, p.sort())
                conditions = [p == k]
                left, right = k, p
                if form in ("boolean", "quantified_boolean"):
                    if form == "boolean":
                        conditions = [z3.And(z3.Or(z3.Not(k), p), z3.Or(k, z3.Not(p)))]
                    else:
                        conditions = [z3.And(
                            z3.ForAll([x], z3.Or(z3.Not(bf(x)), bg(x))),
                            z3.ForAll([x], z3.Or(bf(x), z3.Not(bg(x)))))]
                        left, right = bf(a), bg(a)
                elif form == "positive":
                    conditions = [z3.Or(z3.Not(k), p)]
                elif form in ("ite", "quantified_ite"):
                    if form == "ite":
                        value = z3.Const("value", u)
                        conditions = [z3.And(z3.Or(z3.Not(p), value == a),
                                             z3.Or(p, value == b))]
                        left, right = value, z3.If(p, a, b)
                    else:
                        conditions = [z3.And(
                            z3.ForAll([x], z3.Or(z3.Not(bg(x)), f(x) == x)),
                            z3.ForAll([x], z3.Or(bg(x), f(x) == g(x))))]
                        left, right = f(a), z3.If(bg(a), a, g(a))
                elif form == "function":
                    conditions = [z3.ForAll([x], g(x) == f(x))]
                    left, right = f(a), g(a)
                elif form == "permuted_parameters":
                    ff, gg = z3.Function("ff", u, u, u), z3.Function("gg", u, u, u)
                    conditions = [z3.ForAll([x, y], gg(y, x) == ff(x, y))]
                    left, right = ff(a, b), gg(b, a)
                elif form == "capture_avoidance":
                    predicate = z3.Function("predicate", u, u, p.sort())
                    conditions = [z3.ForAll([x], z3.ForAll([y], predicate(x, y)) == bf(x))]
                    left = z3.ForAll([x], bf(x))
                    right = z3.ForAll([x], z3.ForAll([y], predicate(x, y)))
                elif form == "forward_dependencies":
                    conditions = [k2 == k, z3.Not(p) == k2]
                    left, right = k, z3.Not(p)
                elif form == "repeated":
                    conditions = [p == k, p == k]
                introductions = [c.node("intro-def", definition) for definition in conditions]
                c.node("apply-def", left == right, introductions)
                root = c.asserted(z3.BoolVal(False, c.ctx))
                self.check(c.document(root), 0)
                self.check(c.document(root), 0, strict=True)

    def test_definition_freshness_blocks_rewriting_a_satisfiable_input(self):
        c = Certificate()
        k = z3.Bool("k", c.ctx)
        true = z3.BoolVal(True, c.ctx)
        intro = c.node("intro-def", true == k)
        original = c.asserted(true)
        derived = c.node("mp", k, [original, intro])
        opposite = c.asserted(z3.Not(k))
        root = c.node("unit-resolution", z3.BoolVal(False, c.ctx), [derived, opposite])
        solver = z3.Solver(ctx=c.ctx)
        solver.add(*c.assertions)
        self.assertEqual(solver.check(), z3.sat)
        self.check(c.document(root), 1)
        self.check(c.document(root), 1, strict=True)

    def test_freshness_scans_unused_assertions_and_quantifier_bodies(self):
        for form in ("ground", "nested", "quantified", "overloaded"):
            with self.subTest(form=form):
                c = Certificate()
                u = z3.DeclareSort("U", c.ctx)
                x, a = z3.Consts("x a", u)
                f, g = z3.Function("f", u, u), z3.Function("g", u, u)
                root = c.asserted(z3.BoolVal(False, c.ctx))
                c.node("intro-def", z3.ForAll([x], g(x) == f(x)))
                occurrence = {"ground": f(a) == a, "nested": g(f(a)) == a,
                              "quantified": z3.ForAll([x], f(x) == x)}.get(form)
                if form == "overloaded":
                    other_f = z3.Function("f", z3.BoolSort(c.ctx), z3.BoolSort(c.ctx))
                    occurrence = other_f(z3.BoolVal(True, c.ctx))
                c.assertions.append(occurrence)
                self.check(c.document(root), 0 if form == "overloaded" else 1)

    def test_invalid_definition_introductions_and_applications_are_rejected(self):
        for form in ("self", "cycle", "conflict", "contradictory_clause", "premise",
                     "duplicate_parameter", "unused_parameter", "wrong_parameter_sort",
                     "missing_definition", "invalid_application", "free_variable"):
            with self.subTest(form=form):
                c = Certificate()
                p, q, k, k2 = z3.Bools("p q k k2", c.ctx)
                u = z3.DeclareSort("U", c.ctx)
                x, y = z3.Consts("x y", u)
                f = z3.Function("f", u, u, u)
                if form == "self":
                    c.node("intro-def", z3.Not(k) == k)
                elif form == "cycle":
                    c.node("intro-def", k2 == k)
                    c.node("intro-def", z3.Not(k) == k2)
                elif form == "conflict":
                    c.node("intro-def", p == k)
                    c.node("intro-def", z3.Not(p) == k)
                elif form == "contradictory_clause":
                    c.node("intro-def", z3.And(z3.Or(z3.Not(k), p), z3.Or(k, q)))
                elif form == "premise":
                    premise = c.asserted(p)
                    c.node("intro-def", p == k, [premise])
                elif form == "duplicate_parameter":
                    c.node("intro-def", z3.ForAll([x, y], x == f(x, x)))
                elif form == "unused_parameter":
                    unary = z3.Function("unary", u, u)
                    c.node("intro-def", z3.ForAll([x, y], x == unary(x)))
                elif form == "wrong_parameter_sort":
                    unary = z3.Function("unary", u, u)
                    c.node("intro-def", z3.ForAll([x], x == unary(x)))
                elif form == "free_variable":
                    c.node("apply-def", z3.Var(0, p.sort()) == z3.Var(0, p.sort()))
                else:
                    if form == "invalid_application":
                        intro = c.node("intro-def", p == k)
                        c.node("apply-def", c.oeq(k, q), [intro])
                    else:
                        c.node("apply-def", c.oeq(p, q))
                root = c.asserted(z3.BoolVal(False, c.ctx))
                doc = c.document(root)
                if form == "wrong_parameter_sort":
                    var = next(e for e in doc["exprs"] if e["kind"] == "var")
                    var["sort"] = next(i for i, s in enumerate(doc["sorts"])
                                       if s.get("name") == "Bool")
                self.check(doc, 1)

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
        ctx = z3.Context(proof=True)
        x = z3.Bool("x", ctx)
        solver = z3.Solver(ctx=ctx)
        solver.add(z3.Xor(z3.Not(z3.Not(x)), x))
        self.assertEqual(solver.check(), z3.unsat)
        proof = solver.proof()
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

    def test_large_integer_references_do_not_wrap_to_existing_nodes(self):
        for field in ("root", "declaration", "conclusion"):
            with self.subTest(field=field):
                c = Certificate()
                root = c.asserted(z3.BoolVal(False, c.ctx))
                document = c.document(root)
                large = 1 << 126
                if field == "root":
                    document["root"] = large
                elif field == "declaration":
                    document["exprs"][0]["decl"] = large
                else:
                    document["proofs"][root]["conclusion"] = large
                self.check(document, 1)


if __name__ == "__main__":
    unittest.main()
