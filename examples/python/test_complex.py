############################################
# Copyright (c) 2026 Microsoft Corporation
############################################
import unittest

import z3
from z3 import z3core
from z3.z3 import _to_expr_ref, _to_sort_ref


class TestComplex(unittest.TestCase):
    def formulas(self, source):
        return z3.parse_smt2_string(
            "(declare-const z Complex) (declare-const w Complex) " + source)

    def engines(self, ctx=None):
        return [
            z3.TryFor(z3.Tactic("smt", ctx), 5000),
            z3.TryFor(z3.Tactic("qfnra-nlsat", ctx), 5000),
            z3.TryFor(z3.Then(z3.Tactic("simplify", ctx), z3.With(z3.Tactic("sat", ctx), smt=True)), 5000),
        ]

    def test_old_operator_names_are_not_builtins(self):
        for name, term in [
            ("complex", "(complex 1.0 2.0)"),
            ("real", "(real 1.0)"),
            ("imag", "(imag 1.0)"),
        ]:
            with self.subTest(name=name):
                with self.assertRaisesRegex(z3.Z3Exception, f"unknown constant {name}"):
                    z3.parse_smt2_string(f"(assert (= {term} {term}))")

    def test_python_complex_api(self):
        ctx = z3.Context()
        z, w = z3.Complexes("z w", ctx)
        value = z3.ComplexVal("1/2", 2, ctx)
        self.assertTrue(z3.is_complex_sort(z.sort()))
        expressions = [
            z + 1, 1 + z, z + z3.RealVal(1, ctx), z3.IntVal(1, ctx) + z,
            z3.IntVal(1, ctx) + 1j, 1j - z3.RealVal(1, ctx),
            z - w, 1 - z, z * w, 2 * z, z / 2, 1 / z, -z,
            z3.Sum(z, w, 1), z3.Product(z, w, 2),
            z3.Sum(z3.IntVal(1, ctx), 2j),
            z3.If(z3.Bool("b", ctx), z, z3.RealVal(1, ctx)),
            z3.Select(z3.Array("a", z3.IntSort(ctx), z.sort()), 0),
        ]
        for expression in expressions:
            self.assertIsInstance(expression, z3.ComplexRef)
        for tactic in self.engines(ctx):
            solver = tactic.solver()
            solver.add(z == value)
            self.assertEqual(solver.check(), z3.sat)
            evaluated = solver.model().eval(z)
            self.assertIsInstance(evaluated, z3.ComplexRef)
            self.assertTrue(z3.is_true(z3.simplify(evaluated == value)))
        self.assertEqual(z3.simplify(value.real_part()).as_fraction(), z3.RealVal("1/2", ctx).as_fraction())
        self.assertEqual(z3.simplify(value.imag_part()).as_long(), 2)
        self.assertTrue(z3.is_true(z3.simplify(z3.ComplexVal(1 + 2j) == z3.ComplexVal(1, 2))))
        for expression in [
            z3.IntVal(1, ctx) + 2j,
            z3.Sum(z3.RealVal(1, ctx), 2j),
        ]:
            self.assertTrue(z3.is_true(z3.simplify(expression == z3.ComplexVal(1, 2, ctx))))
        with self.assertRaises(z3.Z3Exception):
            z3.RealPart(z3.IntVal(1, ctx))
        with self.assertRaises(z3.Z3Exception):
            z < w
        with self.assertRaises(z3.Z3Exception):
            z3.ComplexVal(z3.RealVal(1, z3.Context()), ctx=ctx)

    def test_arithmetic_and_components(self):
        cases = [
            "(assert (not (= (* (complex.make 0 1) (complex.make 0 1)) (complex.make (- 1) 0))))",
            "(assert (not (= (+ (complex.make 1 2) (complex.make 3 4)) (complex.make 4 6))))",
            "(assert (not (= (- (complex.make 1 2)) (complex.make (- 1) (- 2)))))",
            "(assert (not (= (- (complex.make 5 6) (complex.make 1 2) (complex.make 3 4)) (complex.make 1 0))))",
            "(assert (not (= (/ (complex.make 1 2) (complex.make 3 4)) (complex.make (/ 11 25) (/ 2 25)))))",
            "(assert (not (= (+ (complex.make 1 2) 3) (complex.make 4 2))))",
            "(assert (not (= z (complex.make (complex.real z) (complex.imag z)))))",
            "(assert (= z (complex.make 3 4))) (assert (distinct (complex.imag z) 4))",
            "(assert (= (complex.real z) (complex.real w))) (assert (= (complex.imag z) (complex.imag w))) "
            "(assert (distinct z w))",
        ]
        for tactic in self.engines():
            for source in cases:
                with self.subTest(engine=str(tactic), source=source):
                    solver = tactic.solver()
                    solver.add(self.formulas(source))
                    self.assertEqual(solver.check(), z3.unsat)

    def test_models_and_incrementality(self):
        for tactic in self.engines():
            with self.subTest(engine=str(tactic)):
                solver = tactic.solver()
                assertions = self.formulas(
                    "(assert (= (complex.real z) 3)) (assert (= (complex.imag z) 4))")
                solver.add(assertions)
                self.assertEqual(solver.check(), z3.sat)
                model = solver.model()
                for assertion in assertions:
                    self.assertTrue(z3.is_true(model.eval(assertion, model_completion=True)))
                solver.push()
                solver.add(self.formulas("(assert (= z (complex.make 0 0)))"))
                self.assertEqual(solver.check(), z3.unsat)
                solver.pop()
                self.assertEqual(solver.check(), z3.sat)

    def test_scalar_multiplication(self):
        cases = [
            "(assert (distinct (* r z) (complex.make (* r (complex.real z)) (* r (complex.imag z)))))",
            "(assert (distinct (* z r) (complex.make (* r (complex.real z)) (* r (complex.imag z)))))",
            "(assert (distinct (* r z) (* z r)))",
            "(assert (distinct (* 0.0 z) (complex.make 0 0)))",
            "(assert (distinct (* z 1.0) z))",
            "(assert (distinct (* (- 2.0) (complex.make 3 4)) (complex.make (- 6) (- 8))))",
            "(assert (distinct (* (complex.make 3 4) (/ 1.0 2.0)) (complex.make (/ 3 2) 2)))",
            "(assert (distinct (* 2 z) (* 2.0 z)))",
            "(assert (distinct (* z 2) (* z 2.0)))",
            "(assert (distinct (* r z 2.0) (* (* r z) 2.0)))",
        ]
        for tactic in self.engines():
            for source in cases:
                with self.subTest(engine=str(tactic), source=source):
                    solver = tactic.solver()
                    solver.add(self.formulas("(declare-const r Real)" + source))
                    self.assertEqual(solver.check(), z3.unsat)

        ctx = z3.Context()
        sort = _to_sort_ref(z3core.Z3_mk_complex_sort(ctx.ref()), ctx)
        z = z3.Const("z", sort)
        r = z3.Real("r", ctx)
        for lhs, rhs in [(r, z), (z, r)]:
            with self.subTest(lhs=lhs, rhs=rhs):
                args = (z3core.Ast * 2)(lhs.as_ast(), rhs.as_ast())
                product = _to_expr_ref(z3core.Z3_mk_mul(ctx.ref(), 2, args), ctx)
                self.assertEqual(product.sort(), sort)
                self.assertEqual(product.decl().domain(0), lhs.sort())
                self.assertEqual(product.decl().domain(1), rhs.sort())
                self.assertTrue(product.arg(0).eq(lhs))
                self.assertTrue(product.arg(1).eq(rhs))

    def test_algebraic_model(self):
        for tactic in self.engines():
            with self.subTest(engine=str(tactic)):
                solver = tactic.solver()
                assertions = self.formulas(
                    "(assert (= (* z z) (complex.make (- 2) 0)))")
                solver.add(assertions)
                self.assertEqual(solver.check(), z3.sat)
                self.assertTrue(z3.is_true(solver.model().eval(assertions[0])))

    def test_uf_congruence(self):
        assertions = self.formulas(
            "(declare-fun f (Complex) Int)"
            "(assert (= (complex.real z) (complex.real w))) (assert (= (complex.imag z) (complex.imag w)))"
            "(assert (distinct (f z) (f w)))")
        for tactic in [self.engines()[0], self.engines()[2]]:
            solver = tactic.solver()
            solver.add(assertions)
            self.assertEqual(solver.check(), z3.unsat)

    def test_quantified_components(self):
        solver = z3.Tactic("smt").solver()
        solver.set(timeout=5000)
        solver.add(z3.parse_smt2_string(
            "(assert (forall ((z Complex)) (= (complex.imag z) 0)))"))
        self.assertEqual(solver.check(), z3.unsat)

    def test_shared_complex_models(self):
        declarations = [
            ("(declare-fun f (Complex) Int)", "(f z)", "(f w)"),
            ("(declare-const a (Array Complex Int))", "(select a z)", "(select a w)"),
        ]
        constraints = [
            "",
            "(assert (= (complex.real z) 0)) (assert (= (complex.real w) 0))",
            "(assert (= (complex.imag z) 0)) (assert (= (complex.imag w) 0))",
            "(assert (= (* z z) (complex.make 1 0)))"
            "(assert (= (* w w) (complex.make 1 0)))",
            "(assert (= (* z z) (complex.make (- 2) 0)))"
            "(assert (= (* w w) (complex.make (- 2) 0)))",
        ]
        for tactic in [self.engines()[0], self.engines()[2]]:
            for declaration, lhs, rhs in declarations:
                for constraint in constraints:
                    with self.subTest(engine=str(tactic), declaration=declaration, constraint=constraint):
                        solver = tactic.solver()
                        assertions = self.formulas(
                            declaration + constraint + f"(assert (distinct {lhs} {rhs}))")
                        solver.add(assertions)
                        self.assertEqual(solver.check(), z3.sat)
                        model = solver.model()
                        for assertion in assertions:
                            self.assertTrue(z3.is_true(model.eval(assertion, model_completion=True)))

    def test_shared_complex_finite_domain(self):
        for tactic in [self.engines()[0], self.engines()[2]]:
            for declaration, values in [
                ("(declare-fun f (Complex) Int)", "(f z) (f w) (f u)"),
                ("(declare-const a (Array Complex Int))",
                 "(select a z) (select a w) (select a u)"),
            ]:
                with self.subTest(engine=str(tactic), declaration=declaration):
                    solver = tactic.solver()
                    assertions = self.formulas(
                        "(declare-const u Complex)" + declaration +
                        "(assert (= (* z z) (complex.make 1 0)))"
                        "(assert (= (* w w) (complex.make 1 0)))"
                        f"(assert (distinct {values}))")
                    solver.add(assertions)
                    self.assertEqual(solver.check(), z3.sat)
                    solver.push()
                    solver.add(self.formulas(
                        "(declare-const u Complex)"
                        "(assert (= (* u u) (complex.make 1 0)))"))
                    self.assertEqual(solver.check(), z3.unsat)
                    solver.pop()
                    self.assertEqual(solver.check(), z3.sat)
                    model = solver.model()
                    for assertion in assertions:
                        self.assertTrue(z3.is_true(model.eval(assertion, model_completion=True)))

    def test_nlsat_rejects_uninterpreted_complex_functions(self):
        solver = self.engines()[1].solver()
        solver.add(self.formulas(
            "(declare-fun f (Int) Complex)"
            "(assert (= (complex.imag (f 0)) 1))"))
        self.assertEqual(solver.check(), z3.unknown)

    def test_ite_and_zero_division(self):
        for tactic in self.engines():
            solver = tactic.solver()
            solver.add(self.formulas(
                "(declare-const b Bool)"
                "(assert (= z (ite b (complex.make 1 2) (complex.make 3 4))))"
                "(assert (= (complex.real z) 1)) (assert (= (complex.imag z) 4))"))
            self.assertEqual(solver.check(), z3.unsat)
        solver = z3.Tactic("smt").solver()
        assertions = self.formulas(
            "(assert (= z (/ (complex.make 1 2) (complex.make 0 0))))")
        solver.add(assertions)
        self.assertEqual(solver.check(), z3.sat)
        self.assertTrue(z3.is_true(solver.model().eval(assertions[0])))

    def test_c_api_and_sort_errors(self):
        ctx = z3.Context()
        sort = _to_sort_ref(z3core.Z3_mk_complex_sort(ctx.ref()), ctx)
        self.assertEqual(sort.kind(), z3.Z3_COMPLEX_SORT)
        one, two = z3.IntVal(1, ctx), z3.RealVal(2, ctx)
        term = _to_expr_ref(z3core.Z3_mk_complex(ctx.ref(), one.as_ast(), two.as_ast()), ctx)
        self.assertEqual(term.decl().kind(), z3.Z3_OP_COMPLEX)
        for mk_part, value in [(z3core.Z3_mk_real_part, 1), (z3core.Z3_mk_imag_part, 2)]:
            part = _to_expr_ref(mk_part(ctx.ref(), term.as_ast()), ctx)
            self.assertEqual(z3.simplify(part).as_long(), value)
        quotient = _to_expr_ref(z3core.Z3_mk_div(ctx.ref(), term.as_ast(), term.as_ast()), ctx)
        self.assertEqual(quotient.sort(), sort)
        self.assertEqual(z3.simplify(quotient).sexpr(), "(complex.make 1.0 0.0)")
        numeral = _to_expr_ref(z3core.Z3_mk_numeral(ctx.ref(), "3/2", sort.ast), ctx)
        self.assertEqual(numeral.sort(), sort)
        self.assertEqual(z3.simplify(numeral).sexpr(), "(complex.make (/ 3.0 2.0) 0.0)")
        with self.assertRaises(z3.Z3Exception):
            z3core.Z3_mk_lt(ctx.ref(), term.as_ast(), term.as_ast())
        with self.assertRaises(z3.Z3Exception):
            z3core.Z3_mk_real_part(ctx.ref(), z3.StringVal("invalid", ctx).as_ast())


if __name__ == "__main__":
    unittest.main()
