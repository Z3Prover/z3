"""Exact basis reuse: changing constraints, premise indices, scopes and fields."""
import itertools
from z3 import *


def main():
    checked = 0
    for enabled in [False, True]:
        for p in [5, 7, 97]:
            field = FiniteFieldSort(p)
            x, y = Consts('cache_x cache_y', field)
            observer = Function('cache_observer', field, IntSort())
            solver = SimpleSolver()
            solver.set(**{'ff.basis_cache': enabled, 'unsat_core': True, 'timeout': 10000})
            base = [x*x+y*y == 5, x*y == 2]
            solver.add(base)
            for i, total in enumerate([None, None, 3, 0, None, 4, None]):
                solver.push()
                constraints = base + [observer(x) == i]
                solver.add(constraints[-1])
                if total is not None:
                    constraint = x+y == total
                    solver.assert_and_track(constraint, Bool('cache_tag_'+str(i)))
                    constraints.append(constraint)
                expected = any((a*a+b*b-5) % p == 0 and (a*b-2) % p == 0 and
                               (total is None or (a+b-total) % p == 0)
                               for a, b in itertools.product(range(p), repeat=2))
                result = solver.check()
                assert result == (sat if expected else unsat), (p, i, result)
                if result == sat:
                    assert all(is_true(solver.model().eval(q, model_completion=True)) for q in constraints)
                else:
                    assert {str(t) for t in solver.unsat_core()} == {'cache_tag_'+str(i)}
                solver.pop()
                checked += 1
            if enabled and p == 97:
                assert solver.statistics().get_key_value('ff basis cache hits') > 0
            solver.reset()
            # Same variable indices can be reused after reset in another field.
            other = FiniteFieldSort(11)
            u, v = Consts('cache_u cache_v', other)
            solver.add(u*u+v*v == 5, u*v == 2)
            assert solver.check() == sat
            assert all(is_true(solver.model().eval(q, model_completion=True)) for q in solver.assertions())
            checked += 1
        solver = SimpleSolver()
        solver.set(**{'ff.basis_cache': enabled, 'timeout': 10000})
        # Identical positive coefficients, different prime: the first system
        # has no F5 point but the second has F7 points. Keep the solver alive
        # across pop so cache identity must distinguish the fields.
        for p, expected in [(5, unsat), (7, sat), (5, unsat), (7, sat)]:
            field = FiniteFieldSort(p)
            u, v = Consts('prime_u_'+str(p)+' prime_v_'+str(p), field)
            constraints = [u*u+v*v+1 == 0, u*v+1 == 0]
            solver.push()
            solver.add(constraints)
            assert solver.check() == expected
            if expected == sat:
                assert all(is_true(solver.model().eval(q, model_completion=True)) for q in constraints)
            solver.pop()
            checked += 1
    print('basis cache:', checked, 'checks with independent finite enumeration, models, cores and reset')


if __name__ == '__main__':
    main()
