"""Independent field-point, core, lifecycle and resource checks for root completion.

Run against the built Python bindings. Algebra-only checks admit unknown when a
budget is exhausted, but every definite result/model/core is checked against
integer enumeration; solver-level checks additionally exercise exact fallback.
"""
import itertools
from collections import Counter
import random
from z3 import *

OPTIONS = ['root_completion', 'quotient_field']


def statistic(s, name):
    return next((v for k, v in s.statistics() if k == name), 0)


def solver(kind, options):
    if kind in ['ff-solve', 'ff-sat']:
        s = Tactic(kind).solver()
    elif kind == 'native':
        s = SimpleSolver()
    else:
        s = SolverFor('QF_FF')
    s.set(**{'ff.' + k: True for k in options})
    s.set(**{'ff.model_search': False, 'ff.sparse_witness': False})
    if kind in ['ff-solve', 'ff-sat']:
        s.set(**{'ff.enum_bits': 0})
    return s


def cyclic(prime):
    field = FiniteFieldSort(prime)
    xs = Consts('cycle0 cycle1 cycle2 cycle3 cycle4', field)
    qs = []
    for length in range(1, 5):
        terms = []
        for start in range(5):
            product = FiniteFieldVal(1, field)
            for offset in range(length):
                product *= xs[(start + offset) % 5]
            terms.append(product)
        qs.append(Sum(terms) == 0)
    product = FiniteFieldVal(1, field)
    for x in xs:
        product *= x
    return xs, qs + [product == 1]


def isolated_completion():
    # The cyclic example has extension-field solutions but none over F_394357.
    # Require the algebra-only path and its completion statistic, so BV fallback
    # or a sampled model cannot accidentally make this regression test pass.
    _, qs = cyclic(394357)
    s = solver('ff-solve', ['root_completion'])
    s.add(qs)
    assert s.check() == unsat, s.reason_unknown()
    assert statistic(s, 'ff minimal polynomials') > 0
    assert statistic(s, 'ff model probes') == 0
    assert statistic(s, 'ff quotient probes') == 0
    # Legacy model_search still includes the same completion operation.
    legacy = solver('ff-solve', [])
    legacy.set(**{'ff.model_search': True})
    legacy.add(qs)
    assert legacy.check() == unsat
    print('isolated cyclic completion and legacy option', flush=True)


def enumerated_systems():
    rng = random.Random(823417)
    facts = 0
    checks = 0
    definite = Counter()
    for p in [2, 3, 5, 7]:
        field = FiniteFieldSort(p)
        xs = Consts('quot_x quot_y quot_z', field)
        points = list(itertools.product(range(p), repeat=3))
        for trial in range(12):
            # Quadratic systems without linear definitions exercise quotient
            # completion. Repeated roots, extension-only roots and singular
            # systems arise naturally, with no dependence on solver output.
            coeffs = [(rng.randrange(p), rng.randrange(p)) for _ in xs]
            qs = [xs[i]*xs[i] + a*xs[(i+1)%3]*xs[(i+2)%3] + b == 0
                  for i, (a, b) in enumerate(coeffs)]
            def holds(point, indices):
                return all((point[i]**2 + coeffs[i][0]*point[(i+1)%3]*point[(i+2)%3]
                            + coeffs[i][1]) % p == 0 for i in indices)
            expected = sat if any(holds(pt, range(3)) for pt in points) else unsat
            for flags in [[], ['root_completion'], ['quotient_field'], OPTIONS]:
                s = solver('ff-solve', flags)
                s.set(unsat_core=True)
                # Raw ff-solve accepts field literals, not Boolean implications.
                # tactic2solver attaches each check assumption directly as a
                # dependency; assert_and_track would introduce an implication.
                result = s.check(*qs)
                assert result in [expected, unknown], (p, coeffs, flags, result, expected)
                if result == sat:
                    assert all(is_true(s.model().eval(q, model_completion=True)) for q in qs)
                elif result == unsat:
                    indices = {q.get_id(): i for i, q in enumerate(qs)}
                    selected = [indices[q.get_id()] for q in s.unsat_core()]
                    assert not any(holds(pt, selected) for pt in points), (p, coeffs, flags, selected)
                if result != unknown:
                    definite[tuple(flags)] += 1
                facts += statistic(s, 'ff quotient facts')
                checks += 1
    assert facts > 0, 'No completed Frobenius consequence was exercised'
    assert all(definite[tuple(flags)] >= 24 for flags in
               [[], ['root_completion'], ['quotient_field'], OPTIONS]), definite
    print(checks, 'enumerated systems and independently checked cores;', facts, 'field facts', flush=True)


def field_root_families():
    checks = facts = 0
    for p in [2, 3, 5, 7]:
        field = FiniteFieldSort(p)
        for a, b in [(0, 1), (2, 1), (1, 0)]:
            points = [(u, v) for u, v in itertools.product(range(p), repeat=2)
                      if (u*u + v*v - a) % p == 0 and (u*v - b) % p == 0]
            expected = sat if points else unsat
            for names in [('family_x', 'family_y'), ('renamed_z', 'renamed_a')]:
                # Reverse both symbol names and equation order. The mathematical
                # family and integer oracle are independent of AST variable IDs
                # and which basis polynomial happens to be first.
                x, y = Consts(' '.join(names), field)
                qs = [x*x + y*y == a, x*y == b]
                for reverse in [False, True]:
                    for flags in [['root_completion'], ['quotient_field'], OPTIONS]:
                        s = solver('ff-solve', flags)
                        s.add(list(reversed(qs)) if reverse else qs)
                        answer = s.check()
                        assert answer == expected, (p, a, b, names, reverse, flags, answer, s.reason_unknown())
                        if answer == sat:
                            m = s.model()
                            assert all(is_true(m.eval(q, model_completion=True)) for q in qs)
                        facts += statistic(s, 'ff quotient facts')
                        checks += 1
    assert facts > 0
    print(checks, 'exact quadratic field-root families with renaming/order invariance;', facts, 'field facts', flush=True)


def missing_premise_core():
    # In F3, nonzero squares are 1. xy=1 makes both coordinates nonzero,
    # contradicting x^2+y^2=0. Each premise alone has an explicit field model;
    # over the algebraic closure their conjunction is consistent. A conflict
    # missing either reducer premise is therefore unsound.
    field = FiniteFieldSort(3)
    x, y = Consts('coretrap_x coretrap_y', field)
    qs = [x*x + y*y == 0, x*y == 1]
    points = list(itertools.product(range(3), repeat=2))
    def holds(point, indices):
        u, v = point
        return all([(u*u+v*v) % 3 == 0, u*v % 3 == 1][i] for i in indices)
    assert not any(holds(pt, [0, 1]) for pt in points)
    assert all(any(holds(pt, [i]) for pt in points) for i in [0, 1])
    for kind in ['ff-solve', 'ff-sat', 'native', 'qfff']:
        s = solver(kind, ['quotient_field'])
        s.set(unsat_core=True)
        if kind == 'ff-solve':
            assert s.check(*qs) == unsat
            ids = {q.get_id(): i for i, q in enumerate(qs)}
            core = {ids[q.get_id()] for q in s.unsat_core()}
        else:
            for i, q in enumerate(qs):
                s.assert_and_track(q, Bool('essential' + str(i)))
            assert s.check() == unsat
            core = {int(str(q).removeprefix('essential')) for q in s.unsat_core()}
        assert core == {0, 1}, (kind, core)
        # The raw tactic has no independent Boolean/BV fallback: require this
        # path to have actually committed field consequences.
        if kind == 'ff-solve':
            assert statistic(s, 'ff quotient facts') > 0
        assert not any(holds(pt, core) for pt in points)
        for q in qs:
            single = solver(kind, ['quotient_field'])
            single.add(q)
            assert single.check() == sat
    print('base-field-only conflict retains both indispensable premises', flush=True)


def interfaces_and_guards():
    for p in [3, 5, 7, 394357, 4294967311,
              21888242871839275222246405745257275088548364400416034343698204186575808495617]:
        field = FiniteFieldSort(p)
        x, y = Consts('guard_x guard_y', field)
        for kind in ['ff-solve', 'ff-sat', 'native', 'qfff']:
            for flags in [['root_completion'], ['quotient_field'], OPTIONS]:
                s = solver(kind, flags)
                # A positive-dimensional variety must not be rejected by a
                # failed zero-dimensional guard. Nonzero witness is explicit.
                s.add(x*y == 1)
                assert s.check() == sat, (p, kind, flags, s.reason_unknown())
                assert is_true(s.model().eval(x*y == 1))
                s.push()
                s.add(x == 0)
                assert s.check() == unsat
                s.pop()
                assert s.check() == sat
                s.reset()
                # Nonradical equation: Frobenius closure may remove nilpotents
                # algebraically but must preserve its unique field point.
                s.add((x-1)*(x-1) == 0)
                assert s.check() == sat
                assert is_true(s.model().eval(x == 1))
    print('all interfaces, large primes, positive dimension, nonradical roots and push/pop/reset', flush=True)


def resource_recovery():
    _, qs = cyclic(394357)
    s = solver('qfff', OPTIONS)
    s.add(qs)
    s.set(rlimit=1)
    assert s.check() == unknown
    s.set(rlimit=10000000)
    assert s.check() == unsat, s.reason_unknown()
    # Local algebra exhaustion must not become an UNSAT claim or poison reuse.
    s = solver('ff-solve', OPTIONS)
    s.add(qs)
    s.set(**{'ff.max_steps': 1})
    assert s.check() == unknown
    s.set(**{'ff.max_steps': 2000000})
    assert s.check() == unsat, s.reason_unknown()
    print('shared resource cancellation and local budget recovery', flush=True)


def default_model_search_policy():
    # x*y*z=1 needs witness construction. The probe counter distinguishes the
    # retained policy from the legacy recursive guesses, which also find SAT.
    # Check local precedence over global settings and all public interfaces;
    # raw child-engine defaults remain false to avoid recursive probe expansion.
    field = FiniteFieldSort(101)
    x, y, z = Consts('policy_x policy_y policy_z', field)
    q = x*y*z == 1
    try:
        for global_value in [None, False, True]:
            for local_value in [None, False, True]:
                reset_params()
                if global_value is not None:
                    set_param('smt.ff.model_search', global_value)
                expected = local_value if local_value is not None else (global_value if global_value is not None else True)
                for kind in ['ff-solve', 'ff-sat', 'native', 'QF_FF']:
                    s = Tactic(kind).solver() if kind in ['ff-solve', 'ff-sat'] else (SimpleSolver() if kind == 'native' else SolverFor('QF_FF'))
                    s.set(**{'ff.sparse_witness': False})
                    if kind in ['ff-solve', 'ff-sat']:
                        s.set(**{'ff.enum_bits': 0})
                    if local_value is not None:
                        s.set(**{'ff.model_search': local_value})
                    s.add(q)
                    assert s.check() == sat, (kind, global_value, local_value, s.reason_unknown())
                    assert is_true(s.model().eval(q, model_completion=True))
                    if kind == 'native':
                        # The native theory publishes its own check/fallback
                        # counters, not per-engine algebra probe statistics.
                        assert statistic(s, 'ff native checks') > 0
                    else:
                        assert (statistic(s, 'ff model probes') > 0) == expected, (kind, global_value, local_value, s.statistics())
    finally:
        reset_params()
    print('default witness policy and local/global overrides across all interfaces', flush=True)


if __name__ == '__main__':
    isolated_completion()
    enumerated_systems()
    field_root_families()
    missing_premise_core()
    interfaces_and_guards()
    resource_recovery()
    default_model_search_policy()
