#!/usr/bin/env python3
"""Independent circuit fixtures and guarded R1CS bit-decomposition regression tests."""
import itertools
import random
from z3 import Bool, FiniteFieldSort, FiniteFieldElems, SolverFor, Tactic, Sum, sat, unsat
from zk_circuits import self_test


def decomposition_tests():
    rng = random.Random(8271)
    checked = 0
    for prime in [2, 3, 5, 7, 17]:
        for _ in range(35):
            f = FiniteFieldSort(prime)
            a, b, c, out = FiniteFieldElems('a b c out', f)
            variables = [a, b, c]
            guarded = [rng.choice([True, True, False]) for _ in variables]
            coefficients = [rng.choice([1, -1, 2, -2, 4, -4, 3]) for _ in variables]
            target = rng.randrange(prime)
            assertions = [v*v == v for v, guard in zip(variables, guarded) if guard]
            assertions += [Sum([coef*v for coef, v in zip(coefficients, variables)]) == out, out == target]
            solver = SolverFor('QF_FF'); solver.set(unsat_core=True)
            for i, assertion in enumerate(assertions):
                solver.assert_and_track(assertion, Bool(f'constraint_{i}'))
            witnesses = list(itertools.product(*(range(2) if guard else range(prime) for guard in guarded)))
            exists = any(sum(v*k for v,k in zip(row, coefficients)) % prime == target for row in witnesses)
            result = solver.check()
            assert result == (sat if exists else unsat), (prime, guarded, coefficients, target, result)
            if exists:
                model = solver.model()
                values = [model.eval(v, model_completion=True).as_long() for v in variables]
                assert all(not guard or value in [0, 1] for value, guard in zip(values, guarded))
                assert sum(v*k for v,k in zip(values, coefficients)) % prime == target
            else:
                # Every returned core must imply inconsistency on its own.
                core = {int(str(x).split('_')[-1]) for x in solver.unsat_core()}
                guards = [i for i, guard in enumerate(guarded) if guard]
                for row in itertools.product(range(prime), repeat=3):
                    if any(i in core and row[var] not in [0, 1] for i, var in enumerate(guards)): continue
                    # Omitting either the definition or pin always admits an out.
                    assert len(guards) in core and len(guards)+1 in core, (prime, guarded, coefficients, target, core, assertions, row)
                    assert sum(v*k for v,k in zip(row, coefficients)) % prime != target
            checked += 1
    # Exercise the newly recognized ordinary linear sum plus a pinned output.
    f = FiniteFieldSort(17); a,b,c,out = FiniteFieldElems('a b c out',f)
    solver = Tactic('ff-solve').solver(); solver.add(a*a==a,b*b==b,c*c==c,out==5,a+2*b+4*c==out)
    assert solver.check() == sat
    assert solver.statistics().get_key_value('ff bit facts') >= 3
    print(f'{checked} guarded, unguarded, signed and wrapping decompositions checked, including cores')


if __name__ == '__main__':
    self_test()
    decomposition_tests()
