############################################
# Copyright (c) 2026 Microsoft Corporation
############################################
"""Open assumptions and first-order answer literals."""

from z3 import (
    BoolSort, Consts, DeclareSort, ForAll, Function, Implies, Not, Or,
    SimpleSolver, Var, unsat,
)


def ground_instances():
    item = DeclareSort("Item")
    a, b = Consts("a b", item)
    p = Function("p", item, item, BoolSort())
    solver = SimpleSolver()
    solver.add(Or(Not(p(a, b)), Not(p(b, a))))
    assert solver.check(p(Var(1, item), Var(0, item))) == unsat
    print("Ground-instance core:", solver.unsat_core())


def first_order_answers():
    person = DeclareSort("Person")
    alice, bob, x = Consts("alice bob x", person)
    researcher = Function("researcher", person, BoolSort())
    reject_answer = Function("reject-answer", person, BoolSort())
    solver = SimpleSolver()
    solver.add(researcher(alice), researcher(bob))
    solver.add(
        ForAll(
            [x],
            Implies(researcher(x), Not(reject_answer(x))),
            patterns=[researcher(x)],
        )
    )
    assert solver.check(reject_answer(Var(0, person))) == unsat
    answers = [lit.arg(0) for lit in solver.unsat_core()]
    print("First-order answers:", answers)


if __name__ == "__main__":
    ground_instances()
    first_order_answers()
