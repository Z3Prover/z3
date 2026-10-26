############################################
# Copyright (c) 2026 Microsoft Corporation
############################################
"""Regressions for the solver API's open predicate assumptions."""

import unittest

import z3


class OpenAssumptionsTests(unittest.TestCase):
    def setUp(self):
        self.item = z3.DeclareSort("Item")
        self.a, self.b, self.x = z3.Consts("a b x", self.item)
        self.p = z3.Function("p", self.item, self.item, z3.BoolSort())
        self.template = self.p(z3.Var(1, self.item), z3.Var(0, self.item))

    def assert_core(self, solver, expected):
        core = solver.unsat_core()
        self.assertEqual({e.sexpr() for e in core}, {e.sexpr() for e in expected})
        check = z3.SimpleSolver()
        check.add(*solver.assertions())
        self.assertEqual(check.check(*core), z3.unsat)

    def test_multiple_ground_instances_and_cleanup(self):
        for factory in (z3.SimpleSolver, z3.Solver):
            with self.subTest(solver=factory.__name__):
                s = factory()
                pa, pb = self.p(self.a, self.b), self.p(self.b, self.a)
                s.add(z3.Or(z3.Not(pa), z3.Not(pb)))
                self.assertEqual(s.check(self.template), z3.unsat)
                self.assert_core(s, [pa, pb])
                self.assertEqual(s.check(), z3.sat)
                self.assertEqual(s.check(self.template), z3.unsat)
                self.assert_core(s, [pa, pb])

    def test_already_internalized_terms_and_scopes(self):
        s = z3.SimpleSolver()
        pa = self.p(self.a, self.b)
        s.add(z3.Not(pa))
        self.assertEqual(s.check(), z3.sat)
        s.push()
        self.assertEqual(s.check(self.template), z3.unsat)
        self.assert_core(s, [pa])
        s.pop()
        self.assertEqual(s.check(), z3.sat)

    def test_mixed_closed_and_open_assumptions(self):
        s = z3.Solver()
        enabled = z3.Bool("enabled")
        pa = self.p(self.a, self.b)
        s.add(z3.Implies(enabled, z3.Not(pa)))
        self.assertEqual(s.check(self.template, enabled), z3.unsat)
        self.assert_core(s, [enabled, pa])
        self.assertEqual(s.check(self.template), z3.sat)
        self.assertTrue(z3.is_true(s.model().eval(pa)))

    def test_quantifier_created_instances(self):
        s = z3.SimpleSolver()
        trigger = z3.Function("trigger", self.item, z3.BoolSort())
        pa, pb = self.p(self.a, self.a), self.p(self.b, self.b)
        s.add(trigger(self.a), trigger(self.b))
        s.add(
            z3.ForAll(
                [self.x],
                z3.Implies(trigger(self.x), z3.Not(self.p(self.x, self.x))),
                patterns=[trigger(self.x)],
            )
        )
        self.assertEqual(s.check(self.template), z3.unsat)
        core = s.unsat_core()
        self.assertGreater(len(core), 0)
        self.assertTrue(all(e.eq(pa) or e.eq(pb) for e in core))
        check = z3.SimpleSolver()
        check.add(*s.assertions())
        self.assertEqual(check.check(*core), z3.unsat)
        self.assertEqual(s.check(), z3.sat)

    def test_vacuous_and_unused_predicates(self):
        s = z3.SimpleSolver()
        self.assertEqual(s.check(self.template), z3.sat)
        s.add(z3.BoolVal(False))
        self.assertEqual(s.check(self.template), z3.unsat)
        self.assertEqual(len(s.unsat_core()), 0)

    def test_core_minimization(self):
        s = z3.SimpleSolver()
        s.set("core.minimize", True)
        pa = self.p(self.a, self.b)
        s.add(z3.Not(pa))
        self.assertEqual(s.check(self.template), z3.unsat)
        self.assert_core(s, [pa])

    def test_core_after_boolean_conflict_learning(self):
        s = z3.SimpleSolver()
        pa = self.p(self.a, self.b)
        left, right = z3.Bools("left right")
        for l in (left, z3.Not(left)):
            for r in (right, z3.Not(right)):
                s.add(z3.Or(z3.Not(pa), l, r))
        self.assertEqual(s.check(self.template), z3.unsat)
        self.assert_core(s, [pa])
        self.assertEqual(s.check(), z3.sat)

    def test_instance_discovered_above_the_assumption_level(self):
        s = z3.SimpleSolver()
        pa = self.p(self.a, self.b)

        class LateInstance(z3.UserPropagateBase):
            def __init__(self):
                super().__init__(s)
                self.depth = 0
                self.discovery_depth = None
                self.add_final(self.on_final)

            def push(self):
                self.depth += 1

            def pop(self, n):
                self.depth -= n

            def on_final(self):
                if self.discovery_depth is None:
                    self.discovery_depth = self.depth
                self.propagate(z3.Not(pa), [])

        propagator = LateInstance()
        s.add(z3.Or(z3.Bool("left"), z3.Bool("right")))
        self.assertEqual(s.check(self.template), z3.unsat)
        self.assertGreater(propagator.discovery_depth, 1)
        self.assertEqual([e.sexpr() for e in s.unsat_core()], [pa.sexpr()])

    def test_multiple_predicates_and_nested_boolean_arguments(self):
        s = z3.SimpleSolver()
        q = z3.Function("q", z3.BoolSort(), z3.BoolSort())
        pa = self.p(self.a, self.b)
        qp = q(pa)
        s.add(z3.Not(qp))
        self.assertEqual(s.check(self.template, q(z3.Var(0, z3.BoolSort()))), z3.unsat)
        self.assert_core(s, [qp])

    def test_proofs_and_core_validation(self):
        context = z3.Context(proof=True)
        integer = z3.IntSort(context)
        p = z3.Function("p", integer, z3.BoolSort(context))
        s = z3.SimpleSolver(context)
        s.set("core.validate", True)
        s.add(z3.Not(p(3)))
        self.assertEqual(s.check(p(z3.Var(0, integer))), z3.unsat)
        self.assertEqual([e.sexpr() for e in s.unsat_core()], [p(3).sexpr()])
        self.assertIsNotNone(s.proof())

    def test_malformed_templates_are_rejected(self):
        x, y = z3.Var(1, self.item), z3.Var(0, self.item)
        malformed = [
            self.p(y, x), self.p(y, y), self.p(self.a, y),
            z3.Not(self.template), z3.Or(self.template, z3.Bool("q")),
            z3.Var(0, z3.BoolSort()),
        ]
        for a in malformed:
            with self.subTest(assumption=a):
                with self.assertRaises(z3.Z3Exception):
                    z3.SimpleSolver().check(a)

    def test_unsupported_solver_is_rejected(self):
        with self.assertRaisesRegex(z3.Z3Exception, "not supported"):
            z3.Tactic("smt").solver().check(self.template)
        s = z3.SimpleSolver()
        s.set(threads=2)
        with self.assertRaisesRegex(z3.Z3Exception, "single-threaded"):
            s.check(self.template)


if __name__ == "__main__":
    unittest.main()
