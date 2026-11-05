############################################
# Copyright (c) 2026 Microsoft Corporation
############################################
import unittest

import z3


class TestRealPower(unittest.TestCase):
    def test_purified_roots_and_models(self):
        for proofs in (False, True):
            ctx = z3.Context(proof=proofs)
            x, y = z3.Reals("x y", ctx=ctx)
            half = z3.RealVal("1/2", ctx)
            third = z3.RealVal("1/3", ctx)
            cases = [
                (x == -1, x**half, z3.RealVal(0, ctx)),
                (x == -8, x**third, z3.RealVal(-2, ctx)),
                (x == -8, x**(-third), -half),
                (x == 4, x**half, z3.RealVal(2, ctx)),
                (x == 2, x**half, z3.Sqrt(z3.RealVal(2, ctx))),
                (x == 0, x**(-half), z3.RealVal(0, ctx)),
            ]
            for premise, power, value in cases:
                for contradict in (False, True):
                    with self.subTest(proofs=proofs, power=power, contradict=contradict):
                        solver = z3.Then(
                            z3.Tactic("purify-arith", ctx=ctx),
                            z3.With(z3.Tactic("simplify", ctx=ctx), expand_power=True),
                            z3.Tactic("smt", ctx=ctx),
                        ).solver()
                        formula = power != value if contradict else power == value
                        solver.add(premise, formula)
                        self.assertEqual(solver.check(), z3.unsat if contradict else z3.sat)
                        if contradict and proofs:
                            self.assertIsNotNone(solver.proof())
                        elif not contradict:
                            self.assertTrue(z3.is_true(solver.model().eval(formula, model_completion=True)))

            goal = z3.Goal(ctx=ctx)
            goal.add(y == half, (-z3.RealVal(1, ctx))**y != (-z3.RealVal(1, ctx))**half)
            purified = z3.Tactic("purify-arith", ctx=ctx)(goal)
            self.assertNotIn("neg-root", purified.sexpr())
            solver = z3.SimpleSolver(ctx=ctx)
            solver.add(purified.as_expr())
            self.assertEqual(solver.check(), z3.unsat)

            root = z3.simplify(z3.Sqrt(z3.RealVal(2, ctx)))
            for value, wrong_sign in ((root, x < 0), (-root, x > 0)):
                goal = z3.Goal(ctx=ctx)
                goal.add(x == value, wrong_sign)
                purified = z3.Tactic("purify-arith", ctx=ctx)(goal)
                solver = z3.SimpleSolver(ctx=ctx)
                solver.add(purified.as_expr())
                self.assertEqual(solver.check(), z3.unsat)

    def test_exceptional_model_evaluation(self):
        ctx = z3.Context()
        x, y = z3.Reals("x y", ctx=ctx)
        solver = z3.Solver(ctx=ctx)
        solver.add(x == -1, y == z3.RealVal("1/2", ctx))
        self.assertEqual(solver.check(), z3.sat)
        self.assertEqual(solver.model().eval(x**y).as_long(), 0)
        self.assertEqual(solver.model().eval(x**(2*y)).as_long(), -1)

    def test_irrational_exponent(self):
        ctx = z3.Context()
        x, y = z3.Reals("x y", ctx=ctx)
        solver = z3.SimpleSolver(ctx=ctx)
        solver.set(timeout=10000)
        solver.add(x < 0, y*y == 2, x**y != 0)
        self.assertEqual(solver.check(), z3.unsat)


if __name__ == "__main__":
    unittest.main()
