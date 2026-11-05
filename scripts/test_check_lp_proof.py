import unittest
from dataclasses import replace
from fractions import Fraction as Q
from unittest.mock import patch

import z3

from check_lp_proof import (
    Certificate, Fact, Step, InvalidProof, NONE, EQ, LE, LT, GE,
    check_lp_nodes,
)


def fact(kind=EQ, rhs=0, lhs=(), contradiction=False):
    return Fact(kind, contradiction, Q(rhs), Q(0), [(Q(c), j) for c, j in lhs])


def step(kind, conclusion, premises=(), coefficients=(), **kwargs):
    return Step(kind, conclusion, kwargs.get("input", NONE), kwargs.get("assumption", NONE),
                0, kwargs.get("equation", fact()), kwargs.get("pivot", NONE),
                kwargs.get("definition", NONE), kwargs.get("source", NONE),
                Q(kwargs.get("divisor", 1)), list(premises), list(map(Q, coefficients)),
                kwargs.get("bounds", []))


class LpProofTests(unittest.TestCase):
    def native_proof(self, integer):
        ctx = z3.Context(proof=True)
        x, y, z = (z3.Ints if integer else z3.Reals)("x y z", ctx=ctx)
        solver = z3.Solver(ctx=ctx)
        solver.set("arith.solver", 6)
        if integer:
            solver.add(x + 2 * y == 0, x + 2 * z == 1)
        else:
            solver.add(x == 2 * y, y == 3 * z, z >= 1, x <= 5)
        self.assertEqual(solver.check(), z3.unsat)
        return solver.proof()

    def context_parameters(self, proof):
        todo, seen = [proof], set()
        while todo:
            p = todo.pop()
            if p.get_id() in seen:
                continue
            seen.add(p.get_id())
            ps = p.decl().params()
            if ps[:2] == ["arith", "lp-context"]:
                return ps[2:]
            todo.extend(p.children()[:-1])
        self.fail("No LP context in native proof")

    def test_native_real_without_solver_or_rewriter(self):
        proof = self.native_proof(False)
        with patch.object(z3.Solver, "check", side_effect=AssertionError("solver called")), \
                patch.object(z3, "simplify", side_effect=AssertionError("rewriter called")):
            counts = check_lp_nodes(proof)
        self.assertGreater(counts["lp-linear"], 0)
        self.assertGreater(counts["lp-input"], 0)
        self.assertEqual(counts["lp-context"], 1)

    def test_native_integer_and_mutations(self):
        proof = self.native_proof(True)
        self.assertGreater(check_lp_nodes(proof)["lp-integer-tighten"], 0)
        parameters = self.context_parameters(proof)
        cert = Certificate.decode(parameters)
        for s in cert.steps:
            if s.kind == 2:
                s.fact = replace(s.fact, rhs=s.fact.rhs + 1)
                break
        with self.assertRaises(InvalidProof):
            cert.check()
        with self.assertRaises(InvalidProof):
            Certificate.decode(parameters[:-1] + [str(NONE)])
        with self.assertRaises(InvalidProof):
            Certificate.decode(parameters + ["0"])

    def test_wrong_native_variable_binding(self):
        parameters = self.context_parameters(self.native_proof(False))
        cert = Certificate.decode(parameters)
        for i, (term, integral, definition) in enumerate(cert.variables):
            if definition:
                cert.variables[i] = (z3.FreshReal(ctx=term.ctx), integral, definition)
                break
        else:
            self.fail("Expected a linear definition")
        with self.assertRaises(InvalidProof):
            cert.check()

    def test_lattice_and_gomory(self):
        x = z3.Int("x")
        variables = [(x, True, []), (2 * x, True, [(Q(2), 0)])]
        premise = step(0, fact(GE, 1, [(1, 1)]), input=0)
        lattice = step(3, fact(GE, 2, [(1, 1)]), [0], [1],
                       equation=fact(lhs=[(2, 0), (-1, 1)]), pivot=1,
                       divisor=2, bounds=[(1, 0, NONE)])
        Certificate(variables, [], [premise, lattice], 1).check()
        gomory = step(4, fact(GE, 2, [(1, 1)]), [0], [1],
                      equation=fact(lhs=[(1, 0), (Q(-1, 2), 1)]), pivot=0,
                      bounds=[(1, 0, NONE)])
        cert = Certificate(variables, [], [premise, gomory], 1)
        cert.check()
        gomory.fact = replace(gomory.fact, rhs=Q(3))
        with self.assertRaises(InvalidProof):
            cert.check()

    def test_monomial_substitution_and_interval(self):
        x, y = z3.Reals("x y")
        variables = [(x, False, []), (y, False, []), (x * y, False, [])]
        monomials = [(2, [0, 1])]
        fixed = step(0, fact(EQ, 2, [(1, 0)]), input=0)
        substitution = step(5, fact(lhs=[(1, 2), (-2, 1)]), [0], [1],
                            pivot=2, definition=0, bounds=[(0, 0, 0)])
        Certificate(variables, monomials, [fixed, substitution], 1).check()
        lower_x = step(0, fact(GE, 2, [(1, 0)]), input=0)
        lower_y = step(0, fact(GE, 3, [(1, 1)]), input=1)
        interval = step(6, fact(GE, 6, [(1, 2)]), [0, 1], [1, 1],
                        pivot=2, definition=0, bounds=[(0, 0, NONE), (1, 1, NONE)])
        cert = Certificate(variables, monomials, [lower_x, lower_y, interval], 2)
        cert.check()
        interval.fact = replace(interval.fact, rhs=Q(7))
        with self.assertRaises(InvalidProof):
            cert.check()

    def test_discharge_and_forward_reference(self):
        x = z3.Real("x")
        bound = step(0, fact(GE, 3, [(1, 0)]), input=0)
        assumption = step(0, fact(LT, 3, [(1, 0)]), input=1)
        body = step(1, fact(contradiction=True), [0, 1], [1, 1])
        discharge = step(7, fact(GE, 3, [(1, 0)]), [2], [1], assumption=1)
        cert = Certificate([(x, False, [])], [], [bound, assumption, body, discharge], 3)
        cert.check()
        discharge.assumption = 0
        with self.assertRaises(InvalidProof):
            cert.check()
        discharge.assumption = 1
        body.premises[0] = 3
        with self.assertRaises(InvalidProof):
            cert.check()


if __name__ == "__main__":
    unittest.main()
