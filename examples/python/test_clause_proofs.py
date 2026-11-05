"""SMT search proof-mode and clause-trail regressions."""
import unittest

import z3


class ClauseProofTests(unittest.TestCase):
    def setUp(self):
        self.ctx = z3.Context(proof=True)
        self.a, self.b = z3.Bools("a b", self.ctx)

    def solver(self, clausal=True):
        solver = z3.Tactic("smt", ctx=self.ctx).solver()
        solver.set(clause_proof=clausal)
        return solver

    def branching(self):
        a, b = self.a, self.b
        return [z3.Or(a, b), z3.Or(a, z3.Not(b)),
                z3.Or(z3.Not(a), b), z3.Or(z3.Not(a), z3.Not(b))]

    def test_standard_proofs_remain_the_default(self):
        solver = z3.Tactic("smt", ctx=self.ctx).solver()
        solver.add(*self.branching())
        self.assertEqual(solver.check(), z3.unsat)
        self.assertNotEqual(solver.proof().decl().kind(), z3.Z3_OP_PR_CLAUSE_TRAIL)

    def test_clause_trail_has_typed_entries_and_a_false_conclusion(self):
        solver = self.solver()
        solver.add(*self.branching())
        self.assertEqual(solver.check(), z3.unsat)
        trail = solver.proof()
        self.assertEqual(trail.decl().kind(), z3.Z3_OP_PR_CLAUSE_TRAIL)
        self.assertTrue(z3.is_false(trail.arg(trail.num_args() - 1)))
        kinds = {z3.Z3_OP_PR_ASSUMPTION_ADD, z3.Z3_OP_PR_LEMMA_ADD,
                 z3.Z3_OP_PR_TH_ASSUMPTION_ADD, z3.Z3_OP_PR_TH_LEMMA_ADD,
                 z3.Z3_OP_PR_REDUNDANT_DEL}
        self.assertTrue(any(e.decl().kind() == z3.Z3_OP_PR_LEMMA_ADD
                            for e in trail.children()[:-1]))
        for event in trail.children()[:-1]:
            self.assertIn(event.decl().kind(), kinds)
            self.assertTrue(z3.is_bool(event.arg(event.num_args() - 1)))

    def test_theory_certificates_and_preprocessing_conflicts(self):
        for source in (
            "(assert false)",
            "(declare-sort U 0)(declare-const x U)(declare-const y U)"
            "(declare-fun f (U) U)(assert (= x y))(assert (not (= (f x) (f y))))",
            "(declare-const x Real)(declare-const y Real)"
            "(assert (<= (+ x y) 0))(assert (> x 0))(assert (> y 0))",
            "(declare-const x Real)(declare-const y Real)(declare-const p Bool)"
            "(assert (or p (<= x (- 6.0))))(assert (=> p (>= (+ x y) 1.5)))"
            "(assert (< y (/ 1.0 3.0)))(assert (> x 0.0))(assert (<= x 1.0))",
            "(declare-const a (Array Int Int))(declare-const i Int)"
            "(assert (not (= (select (store a i 1) i) 1)))",
            "(declare-sort I 0)(declare-sort E 0)(declare-const a (Array I E))"
            "(declare-const i I)(declare-const j I)(declare-const v E)"
            "(assert (distinct i j))"
            "(assert (distinct (select (store a i v) j) (select a j)))",
        ):
            with self.subTest(source=source):
                solver = self.solver()
                solver.add(z3.parse_smt2_string(source, ctx=self.ctx))
                self.assertEqual(solver.check(), z3.unsat, solver.reason_unknown())
                self.assertEqual(solver.proof().decl().kind(), z3.Z3_OP_PR_CLAUSE_TRAIL)

    def test_mode_changes_require_reset_after_assertions(self):
        for clausal in (False, True):
            with self.subTest(clausal=clausal):
                solver = z3.Solver(ctx=self.ctx)
                solver.set(clause_proof=clausal)
                solver.add(self.a)
                self.assertEqual(solver.check(), z3.sat)
                with self.assertRaisesRegex(z3.Z3Exception, "clause_proof cannot be changed"):
                    solver.set(clause_proof=not clausal)
                    solver.check()
                solver.reset()
                solver.set(clause_proof=not clausal)
                solver.add(*self.branching())
                self.assertEqual(solver.check(), z3.unsat)
                self.assertEqual(solver.proof().decl().kind() == z3.Z3_OP_PR_CLAUSE_TRAIL,
                                 not clausal)

    def test_push_pop_and_repeated_checks(self):
        solver = self.solver()
        solver.add(z3.Or(self.a, self.b))
        solver.push()
        solver.add(z3.Not(self.a), z3.Not(self.b))
        self.assertEqual(solver.check(), z3.unsat)
        solver.proof()
        solver.pop()
        self.assertEqual(solver.check(), z3.sat)
        solver.push()
        solver.add(*self.branching()[1:])
        self.assertEqual(solver.check(), z3.unsat)
        self.assertEqual(solver.proof().decl().kind(), z3.Z3_OP_PR_CLAUSE_TRAIL)
        solver.pop()
        self.assertEqual(solver.check(), z3.sat)

    def test_assumptions_and_reset(self):
        solver = self.solver()
        solver.add(z3.Or(self.a, self.b))
        self.assertEqual(solver.check(z3.Not(self.a), z3.Not(self.b)), z3.unsat)
        self.assertIsNotNone(solver.proof())
        self.assertEqual(solver.check(self.a), z3.sat)
        solver.reset()
        solver.add(*self.branching())
        self.assertEqual(solver.check(), z3.unsat)
        self.assertIsNotNone(solver.proof())

    def test_satisfiable_and_proof_disabled_contexts(self):
        solver = self.solver()
        solver.add(self.a)
        self.assertEqual(solver.check(), z3.sat)
        ctx = z3.Context()
        a, b = z3.Bools("a b", ctx)
        solver = z3.Tactic("smt", ctx=ctx).solver()
        solver.set(clause_proof=True)
        solver.add(a, z3.Not(a))
        self.assertEqual(solver.check(), z3.unsat)

    def test_array_demorgan_with_and_without_proof_production(self):
        source = """
        (declare-const a (Array Int Bool))
        (declare-const b (Array Int Bool))
        (assert (not (= ((_ map and) a b)
                        ((_ map not) ((_ map or) ((_ map not) a) ((_ map not) b))))))
        """
        for proofs in (False, True):
            with self.subTest(proofs=proofs):
                ctx = z3.Context(proof=proofs)
                solver = z3.Tactic("smt", ctx=ctx).solver()
                solver.set(clause_proof=True)
                solver.add(z3.parse_smt2_string(source, ctx=ctx))
                self.assertEqual(solver.check(), z3.unsat, solver.reason_unknown())
                if proofs:
                    self.assertEqual(solver.proof().decl().kind(), z3.Z3_OP_PR_CLAUSE_TRAIL)

    def test_learned_clauses_can_be_simplified_without_standard_justifications(self):
        solver = self.solver()
        places = [[z3.Bool("p%d_%d" % (p, h), self.ctx) for h in range(4)]
                  for p in range(5)]
        solver.add(*[z3.Or(*row) for row in places])
        for h in range(4):
            for p in range(5):
                for q in range(p):
                    solver.add(z3.Or(z3.Not(places[p][h]), z3.Not(places[q][h])))
        self.assertEqual(solver.check(), z3.unsat)
        self.assertEqual(solver.proof().decl().kind(), z3.Z3_OP_PR_CLAUSE_TRAIL)


if __name__ == "__main__":
    unittest.main()
