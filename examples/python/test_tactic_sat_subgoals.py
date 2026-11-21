############################################
# Copyright (c) 2026 Microsoft Corporation
############################################
import unittest

import z3


class TestTacticSatSubgoals(unittest.TestCase):
    def setUp(self):
        self.x, self.y = z3.Ints("x y")
        self.goal = z3.Goal()
        self.goal.add(z3.Or(self.x == 0, self.x == 1))

    def test_application_is_scoped_and_models_are_preserved(self):
        tactic = z3.Then("split-clause", "solve-eqs")
        self.assertEqual(len(tactic(self.goal)), 1)
        result = tactic(self.goal, keep_sat_subgoals=True)
        self.assertEqual(len(result), 2)
        self.assertEqual(
            sorted(g.convert_model(z3.Model()).eval(self.x).as_long() for g in result),
            [0, 1],
        )
        self.assertEqual(len(self.goal), 1)
        self.assertEqual(len(tactic(self.goal, keep_sat_subgoals=False)), 1)
        self.assertEqual(len(tactic(self.goal)), 1)
        solver = tactic.solver()
        solver.add(self.goal.as_expr())
        self.assertEqual(solver.check(), z3.sat)
        self.assertTrue(z3.is_true(solver.model().eval(self.goal.as_expr())))

    def test_nested_and_repeat(self):
        nested = z3.Then("split-clause", z3.Then("solve-eqs", "skip"))
        repeated = z3.Repeat(z3.OrElse("split-clause", "solve-eqs"))
        parallel = z3.ParThen("split-clause", "solve-eqs")
        for tactic in (nested, repeated, parallel):
            with self.subTest(tactic=str(tactic)):
                self.assertEqual(len(tactic(self.goal)), 1)
                result = tactic(self.goal, keep_sat_subgoals=True)
                self.assertEqual(len(result), 2)
                self.assertEqual(
                    sorted(g.convert_model(z3.Model()).eval(self.x).as_long() for g in result),
                    [0, 1],
                )
                self.assertEqual(len(tactic(self.goal)), 1)

    def test_sat_and_undecided_branches(self):
        tactics = (
            z3.Then("split-clause", "solve-eqs"),
            z3.ParThen("split-clause", "solve-eqs"),
            z3.Repeat(z3.OrElse("split-clause", "solve-eqs")),
        )
        for tactic in tactics:
            for clause in (z3.Or(self.x == 0, self.y > 0),
                           z3.Or(self.y > 0, self.x == 0)):
                with self.subTest(tactic=str(tactic), clause=clause):
                    result = tactic(clause, keep_sat_subgoals=True)
                    self.assertEqual(len(result), 2)
                    self.assertEqual(sorted(len(g) for g in result), [0, 1])
                    self.assertEqual(len(tactic(clause)), 1)
                    self.assertEqual(len(tactic(clause)[0]), 0)

    def test_reused_subgoal_and_validation(self):
        self.goal.add(z3.Or(self.y == 0, self.y == 1))
        subgoal = z3.Tactic("split-clause")(self.goal, keep_sat_subgoals=True)[0]
        tactic = z3.Then("split-clause", "solve-eqs")
        self.assertEqual(len(tactic(subgoal, keep_sat_subgoals=True)), 2)
        self.assertEqual(len(tactic(subgoal)), 1)
        self.assertEqual(len(z3.Tactic("skip")(self.goal, keep_sat_subgoals=True)), 1)
        with self.assertRaises(z3.Z3Exception):
            tactic(self.goal, keep_sat_subgoals=42)
        with self.assertRaises(z3.Z3Exception):
            z3.With(tactic, keep_sat_subgoals=True)

    def test_all_unsat(self):
        self.goal.add(self.x > 1)
        tactic = z3.Then("split-clause", "smt")
        for keep in (False, True):
            result = tactic(self.goal, keep_sat_subgoals=keep)
            self.assertEqual(len(result), 1)
            self.assertTrue(result[0].inconsistent())


if __name__ == "__main__":
    unittest.main()
