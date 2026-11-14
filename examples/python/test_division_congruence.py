############################################
# Copyright (c) 2026 Microsoft Corporation
############################################
import random
import unittest

import z3


LARGE_QUERY = """
(declare-fun eps!3010 () Real)
(declare-fun absR (Real) Real)
(declare-fun y!3009 () Real)
(declare-fun x!3008 () Real)
(declare-fun n!3020 () Int)
(declare-fun b!3007 () (Array Int Real))
(declare-fun a!3006 () (Array Int Real))
(declare-fun min (Real Real) Real)
(declare-fun N!3018 () Int)
(declare-fun N!3017 () Int)
(assert (let ((a!1 (> (/ (* eps!3010 (absR y!3009)) 4.0) 0.0))
      (a!2 (/ (* (* eps!3010 (absR y!3009)) (absR y!3009))
              (* 4.0 (+ (absR x!3008) 1.0))))
      (a!4 (< (absR (- (select a!3006 n!3020) x!3008))
              (/ (* eps!3010 (absR y!3009)) 4.0)))
      (a!6 (< (absR (- (select b!3007 n!3020) y!3009)) (/ (absR y!3009) 2.0)))
      (a!7 (* (absR (- (select b!3007 n!3020) y!3009))
              (* 4.0 (+ (absR x!3008) 1.0))))
      (a!9 (= (absR (- y!3009 (select b!3007 n!3020)))
              (absR (- (select b!3007 n!3020) y!3009))))
      (a!10 (+ (absR (- (select b!3007 n!3020) y!3009))
               (absR (select b!3007 n!3020))))
      (a!11 (- (/ (select a!3006 n!3020) (select b!3007 n!3020))
               (/ x!3008 y!3009)))
      (a!12 (* x!3008
               (/ (- y!3009 (select b!3007 n!3020))
                  (* (select b!3007 n!3020) y!3009))))
      (a!14 (absR (/ (- (select a!3006 n!3020) x!3008) (select b!3007 n!3020))))
      (a!15 (/ (absR (- (select a!3006 n!3020) x!3008))
               (absR (select b!3007 n!3020))))
      (a!16 (/ (absR (- (select b!3007 n!3020) y!3009))
               (* (absR (select b!3007 n!3020)) (absR y!3009)))))
(let ((a!3 (> (min (/ (absR y!3009) 2.0) a!2) 0.0))
      (a!5 (< (absR (- (select b!3007 n!3020) y!3009))
              (min (/ (absR y!3009) 2.0) a!2)))
      (a!8 (< a!7 (* (* eps!3010 (absR y!3009)) (absR y!3009))))
      (a!13 (+ (/ (- (select a!3006 n!3020) x!3008) (select b!3007 n!3020))
               a!12)))
(let ((a!17 (and (distinct y!3009 0.0)
                 (> eps!3010 0.0)
                 (> (absR y!3009) 0.0)
                 a!1 a!3 (>= N!3017 0)
                 (forall ((n Int))
                   (let ((a!1 (< (absR (- (select a!3006 n) x!3008))
                                 (/ (* eps!3010 (absR y!3009)) 4.0))))
                     (=> (> n N!3017) a!1)))
                 (>= N!3018 0)
                 (forall ((n Int))
                   (let ((a!1 (/ (* (* eps!3010 (absR y!3009)) (absR y!3009))
                                 (* 4.0 (+ (absR x!3008) 1.0)))))
                   (let ((a!2 (< (absR (- (select b!3007 n) y!3009))
                                 (min (/ (absR y!3009) 2.0) a!1))))
                     (=> (> n N!3018) a!2))))
                 (> n!3020 (ite (> N!3017 N!3018) N!3017 N!3018))
                 a!4 a!5 a!6 a!8 a!9
                 (<= (absR y!3009) a!10)
                 (> (absR (select b!3007 n!3020)) (/ (absR y!3009) 2.0))
                 (distinct (select b!3007 n!3020) 0.0)
                 (= a!11 a!13)
                 (= a!14 a!15)
                 (= (absR a!12) (* (absR x!3008) a!16))
                 (< a!15 (/ eps!3010 2.0))
                 (< (* (absR x!3008) a!16) (/ eps!3010 2.0))
                 (< (absR a!13) eps!3010))))
  (not (=> a!17 (< (absR a!11) eps!3010)))))))
"""


class TestDivisionCongruence(unittest.TestCase):
    def test_small_construction_orders(self):
        a, b, x, y, eps = z3.Reals("a b x y eps")
        abs_r = z3.Function("absR", z3.RealSort(), z3.RealSort())
        quotient = a / b - x / y
        split = (a - x) / b + x * ((y - b) / (b * y))
        premises = [
            y != 0,
            eps > 0,
            eps * abs_r(y) / 4 > 0,
            quotient == split,
            abs_r(split) < eps,
        ]
        query = z3.Not(z3.Implies(z3.And(*premises), abs_r(quotient) < eps))
        for solver_kind in (z3.Solver, z3.SimpleSolver):
            dumps = []
            for order in ([2, 1, 0, 4, 3], [3, 0, 4, 2, 1]):
                with self.subTest(solver=solver_kind.__name__, order=order):
                    ctx = z3.Context()
                    prebuilt = [premises[i].translate(ctx) for i in order]
                    solver = solver_kind(ctx=ctx)
                    solver.set(random_seed=13, rlimit=10_000)
                    solver.add(query.translate(ctx))
                    dumps.append(solver.sexpr())
                    self.assertEqual(solver.check(), z3.unsat, solver.reason_unknown())
                    self.assertEqual(len(prebuilt), len(premises))
            if solver_kind is z3.Solver:
                self.assertEqual(*dumps)

    def test_quantified_construction_orders(self):
        query = z3.parse_smt2_string(LARGE_QUERY)[0]
        dumps = []
        for order in (0, 17):
            with self.subTest(order=order):
                ctx = z3.Context()
                conjuncts = query.arg(0).arg(0).children()
                random.Random(order).shuffle(conjuncts)
                prebuilt = [term.translate(ctx) for term in conjuncts]
                solver = z3.Solver(ctx=ctx)
                solver.set(random_seed=13, rlimit=200_000)
                solver.add(query.translate(ctx))
                dumps.append(solver.sexpr())
                self.assertEqual(solver.check(), z3.unsat, solver.reason_unknown())
                self.assertEqual(len(prebuilt), len(conjuncts))
        self.assertEqual(*dumps)

    def test_incremental_proofs_and_zero_denominator(self):
        for proofs in (False, True):
            with self.subTest(proofs=proofs):
                ctx = z3.Context(proof=proofs)
                a, b, c, d = z3.Reals("a b c d", ctx=ctx)
                f = z3.Function("f", z3.RealSort(ctx), z3.RealSort(ctx))
                quotient = a / b + c
                other = c + d
                solver = z3.SimpleSolver(ctx=ctx)
                solver.add(b == 0, f(quotient) < 0, f(other) >= 0)
                self.assertEqual(solver.check(), z3.sat)
                solver.push()
                solver.add(quotient == other)
                self.assertEqual(solver.check(), z3.unsat)
                if proofs:
                    self.assertIsNotNone(solver.proof())
                solver.pop()
                self.assertEqual(solver.check(), z3.sat)

    def test_tracked_unsat_core(self):
        ctx = z3.Context()
        a, b, c, d = z3.Reals("a b c d", ctx=ctx)
        f = z3.Function("f", z3.RealSort(ctx), z3.RealSort(ctx))
        quotient = a / b + c
        other = c + d
        assertions = [quotient == other, f(quotient) < 0, f(other) >= 0, b == 0]
        labels = [z3.Bool("p%d" % i, ctx=ctx) for i in range(len(assertions))]
        solver = z3.Solver(ctx=ctx)
        for assertion, label in zip(assertions, labels):
            solver.assert_and_track(assertion, label)
        self.assertEqual(solver.check(), z3.unsat)
        core = {str(label) for label in solver.unsat_core()}
        check = z3.Solver(ctx=ctx)
        check.add(*(assertion for assertion, label in zip(assertions, labels) if str(label) in core))
        self.assertEqual(check.check(), z3.unsat)


if __name__ == "__main__":
    unittest.main()
