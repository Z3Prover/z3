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

    def engines(self):
        return [
            z3.TryFor(z3.Tactic("smt"), 5000),
            z3.TryFor(z3.Tactic("qfnra-nlsat"), 5000),
            z3.TryFor(z3.Then("simplify", z3.With("sat", smt=True)), 5000),
        ]

    def test_arithmetic_and_components(self):
        cases = [
            "(assert (not (= (* (complex 0 1) (complex 0 1)) (complex (- 1) 0))))",
            "(assert (not (= (+ (complex 1 2) (complex 3 4)) (complex 4 6))))",
            "(assert (not (= (- (complex 1 2)) (complex (- 1) (- 2)))))",
            "(assert (not (= (- (complex 5 6) (complex 1 2) (complex 3 4)) (complex 1 0))))",
            "(assert (not (= (/ (complex 1 2) (complex 3 4)) (complex (/ 11 25) (/ 2 25)))))",
            "(assert (not (= (+ (complex 1 2) 3) (complex 4 2))))",
            "(assert (not (= z (complex (real z) (imag z)))))",
            "(assert (= z (complex 3 4))) (assert (distinct (imag z) 4))",
            "(assert (= (real z) (real w))) (assert (= (imag z) (imag w))) "
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
                    "(assert (= (real z) 3)) (assert (= (imag z) 4))")
                solver.add(assertions)
                self.assertEqual(solver.check(), z3.sat)
                model = solver.model()
                for assertion in assertions:
                    self.assertTrue(z3.is_true(model.eval(assertion, model_completion=True)))
                solver.push()
                solver.add(self.formulas("(assert (= z (complex 0 0)))"))
                self.assertEqual(solver.check(), z3.unsat)
                solver.pop()
                self.assertEqual(solver.check(), z3.sat)

    def test_algebraic_model(self):
        for tactic in self.engines():
            with self.subTest(engine=str(tactic)):
                solver = tactic.solver()
                assertions = self.formulas(
                    "(assert (= (* z z) (complex (- 2) 0)))")
                solver.add(assertions)
                self.assertEqual(solver.check(), z3.sat)
                self.assertTrue(z3.is_true(solver.model().eval(assertions[0])))

    def test_uf_congruence(self):
        assertions = self.formulas(
            "(declare-fun f (Complex) Int)"
            "(assert (= (real z) (real w))) (assert (= (imag z) (imag w)))"
            "(assert (distinct (f z) (f w)))")
        for tactic in [self.engines()[0], self.engines()[2]]:
            solver = tactic.solver()
            solver.add(assertions)
            self.assertEqual(solver.check(), z3.unsat)

    def test_quantified_components(self):
        solver = z3.Tactic("smt").solver()
        solver.set(timeout=5000)
        solver.add(z3.parse_smt2_string(
            "(assert (forall ((z Complex)) (= (imag z) 0)))"))
        self.assertEqual(solver.check(), z3.unsat)

    def test_nlsat_rejects_uninterpreted_complex_functions(self):
        solver = self.engines()[1].solver()
        solver.add(self.formulas(
            "(declare-fun f (Int) Complex)"
            "(assert (= (imag (f 0)) 1))"))
        self.assertEqual(solver.check(), z3.unknown)

    def test_ite_and_zero_division(self):
        for tactic in self.engines():
            solver = tactic.solver()
            solver.add(self.formulas(
                "(declare-const b Bool)"
                "(assert (= z (ite b (complex 1 2) (complex 3 4))))"
                "(assert (= (real z) 1)) (assert (= (imag z) 4))"))
            self.assertEqual(solver.check(), z3.unsat)
        solver = z3.Tactic("smt").solver()
        assertions = self.formulas(
            "(assert (= z (/ (complex 1 2) (complex 0 0))))")
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
        self.assertEqual(z3.simplify(quotient).sexpr(), "(complex 1.0 0.0)")
        numeral = _to_expr_ref(z3core.Z3_mk_numeral(ctx.ref(), "3/2", sort.ast), ctx)
        self.assertEqual(numeral.sort(), sort)
        self.assertEqual(z3.simplify(numeral).sexpr(), "(complex (/ 3.0 2.0) 0.0)")
        with self.assertRaises(z3.Z3Exception):
            z3core.Z3_mk_lt(ctx.ref(), term.as_ast(), term.as_ast())
        with self.assertRaises(z3.Z3Exception):
            z3core.Z3_mk_real_part(ctx.ref(), z3.StringVal("invalid", ctx).as_ast())


if __name__ == "__main__":
    unittest.main()
