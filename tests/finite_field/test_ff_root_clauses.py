#!/usr/bin/env python3
"""Root clauses: exhaustiveness, conditional premises, models and backtracking."""
import itertools
import random
from z3 import *


def solve(constraints, expected, split=True):
    s = SimpleSolver()
    s.set(timeout=10000)
    s.set('ff.root_split', split)
    s.add(*constraints)
    assert s.check() == expected, (constraints, s.reason_unknown())
    if expected == sat:
        assert all(is_true(s.model().eval(c, model_completion=True)) for c in constraints), s.model()
    return s


def examples():
    for p in [2, 3, 5, 7, 17, 257]:
        F = FiniteFieldSort(p)
        x, y = Consts('root_x root_y', F)
        f = Function('root_f', F, IntSort())
        one, minus = FiniteFieldVal(1, F), FiniteFieldVal(p-1, F)
        cases = [
            [x*x == 1, f(x) != f(one), f(x) != f(minus)],
            [y == x*x, x*x*x*x == 1, f(y) != f(one), f(y) != f(minus)],
            [x*y == 0, x != 0, y != 0],
            [x*x == y*y, x != y, x != -y],
            [(x+1)*(x+1) == y*y, x+1 != y, x+1 != -y],
            [(x*y)*(x*y) == 1, x*y != 1, x*y != minus],
        ]
        for cs in cases:
            s = solve(cs, unsat)
            # F_2 rewriting can settle some equalities before the theory runs.
            if p > 2:
                assert s.statistics().get_key_value('ff root clauses') > 0, (cs, s.statistics())
        # Square recognition must not cancel an unknown factor, discard the
        # negative root, or confuse integer nonsquares with field nonresidues.
        solve([x*y == 0, x == 0, y == 1], sat)
        solve([x*x == 1, x == minus], sat)
        for phase in [0, 1]:
            s = SimpleSolver()
            s.set(phase_selection=phase, timeout=10000)
            s.add(Or(x*x == 1, x == 0), f(x) != f(one), f(x) != f(minus))
            assert s.check() == sat
            assert is_true(s.model().eval(x == 0))
        if p == 7:
            solve([x*x == 2, x == 3], sat)
            solve([x*x == 3], unsat)
        # A derived split is valid only under its equality premise. Negating
        # that premise on a later check must not retain unconditional roots.
        s = SimpleSolver()
        s.set(timeout=10000, unsat_core=True)
        tags = Bools('root_guard root_left root_right')
        for c, tag in zip(cases[0], tags):
            s.assert_and_track(c, tag)
        assert s.check() == unsat
        core = list(s.unsat_core())
        core_constraints = [c for c, tag in zip(cases[0], tags) if any(eq(tag, t) for t in core)]
        solve(core_constraints, unsat, split=False)
        s = SimpleSolver()
        for _ in range(4):
            s.push()
            s.add(*cases[0])
            assert s.check() == unsat
            s.pop()
            assert s.check(x == 0, f(x) != f(one)) == sat
            assert s.check(*cases[0]) == unsat
        s.reset()
        s.add(x == 0, f(x) != f(one))
        assert s.check() == sat


def exhaustive():
    rng = random.Random(94172)
    count = 0
    for p in [2, 3, 5, 7, 11, 17]:
        F = FiniteFieldSort(p)
        x, y = Consts('ex_root_x ex_root_y', F)
        for i in range(40):
            a, b, c, d = [rng.randrange(p) for _ in range(4)]
            mode = i % 4
            if mode == 0:
                guard = (x+a)*(x+a) == b*b
                holds = lambda xv, yv: ((xv+a)**2-b*b) % p == 0
            elif mode == 1:
                guard = x*x*x*x == (y+b)*(y+b)
                holds = lambda xv, yv: (xv**4-(yv+b)**2) % p == 0
            elif mode == 2:
                guard = (x+a)*(y+b)*(x+y) == 0
                holds = lambda xv, yv: ((xv+a)*(yv+b)*(xv+yv)) % p == 0
            else:
                guard = (x+a)*(x+a) == b
                holds = lambda xv, yv: ((xv+a)**2-b) % p == 0
            cs = [guard, x != c, y != d, Or(x+y == a, x*y == b)]
            expected = sat if any(holds(xv, yv) and xv != c and yv != d and
                                  ((xv+yv) % p == a or xv*yv % p == b)
                                  for xv, yv in itertools.product(range(p), repeat=2)) else unsat
            solve(cs, expected)
            count += 1
    print(count, 'root/factor formulas checked against exhaustive enumeration', flush=True)


def algebra_roots():
    count = 0
    for p in [2, 3, 5, 7, 11, 17]:
        F = FiniteFieldSort(p)
        x = Const('algebra_root_x', F)
        for a in range(1, p):
            for b in range(p):
                roots = [v for v in range(p) if a*v*v % p == b]
                for exclude in [False, True]:
                    cs = [a*x*x == b]
                    if exclude:
                        cs += [x != v for v in roots]
                    s = Tactic('ff-solve').solver()
                    s.add(*cs)
                    expected = sat if roots and not exclude else unsat
                    assert s.check() == expected, (p, a, b, exclude)
                    if expected == sat:
                        assert all(is_true(s.model().eval(c, model_completion=True)) for c in cs)
                    count += 1
    print(count, 'pure algebra quadratic/root-exclusion checks passed', flush=True)


if __name__ == '__main__':
    examples()
    exhaustive()
    algebra_roots()
    print('Root clauses: characteristic two, modular-only roots, cores, assumptions and lifecycle passed', flush=True)
