#!/usr/bin/env python3
"""Native large-field combination, DAG models, and forced fallback lifecycle.

Use the Python bindings/library from the build being tested. No timing threshold
is asserted: native counters ensure these cases do not pass via bit-blasting.
"""
from z3 import *
from test_ff_combination import check, examples, finite_domains, incremental, exhaustive_uf
from zk_circuits import FIELDS, poseidon_case


def native(s):
    stats = s.statistics()
    assert sum(stats.get_key_value(k) for k in ['ff native checks', 'ff root clauses'] if k in stats.keys()) > 0, stats
    assert 'ff bv fallbacks' not in stats.keys() or stats.get_key_value('ff bv fallbacks') == 0, stats


def large_field(factory, p):
    F = FiniteFieldSort(p)
    x, y = Consts('large_x large_y', F)
    one, minus_one = FiniteFieldVal(1, F), FiniteFieldVal(p-1, F)
    h = Function('large_h', F, IntSort())
    constraints = [x*x == 1, h(x) != h(one), h(x) != h(minus_one)]
    native(check(factory, constraints, unsat, 'large nonlinear UF'))
    native(check(factory, [x*x == 1, h(x) == 11, h(-x) == 12], sat, 'large UF model'))
    f = Function('large_from_int', IntSort(), F)
    i = Int('large_i')
    native(check(factory, [i == 2, f(i)*f(i) == 1, f(2) != one, f(2) != minus_one],
                 unsat, 'large field-valued UF'))
    a = Array('large_array', F, F)
    native(check(factory, [x*x == 1, Select(a, x) != Select(a, one),
                          Select(a, x) != Select(a, minus_one)], unsat, 'large array indices'))
    native(check(factory, [x*x == 1, Select(a, x)*Select(a, x) == 4,
                          Select(a, -x) == 0], sat, 'large array model'))
    # Nonlinear equality crossing a UF boundary, rather than a numeral-only pin.
    native(check(factory, [y == x*x, x*x*x*x == 1, h(y) != h(one), h(y) != h(minus_one)],
                 unsat, 'large symbolic determinism'))
    s = factory()
    s.set(timeout=10000, unsat_core=True)
    tags = Bools('large_root large_pos large_neg')
    for c, tag in zip(constraints, tags):
        s.assert_and_track(c, tag)
    assert s.check() == unsat
    assert {str(x) for x in s.unsat_core()} == {str(x) for x in tags}
    native(s)
    s = factory()
    s.set(timeout=10000)
    base = [x*x == 1, h(one) == 11, h(minus_one) == 12]
    s.add(*base)
    for _ in range(3):
        assert s.check() == sat
        assert all(is_true(s.model().eval(c, model_completion=True)) for c in base)
        assert s.check(h(x) != 11, h(x) != 12) == unsat
        s.push()
        s.add(h(x) == 12)
        assert s.check() == sat
        assert is_true(s.model().eval(x == minus_one))
        s.pop()
    native(s)


def poseidon_constraints(field, count, equality):
    # Two complete permutations with different x^5 multiplication schedules.
    # The residual condition observes their outputs through an opaque UF.
    circuit, _ = poseidon_case(field, count, 'equivalence')
    (a, b), = circuit.different
    circuit.different = []
    F = FiniteFieldSort(circuit.p)
    lhs = Const('w' + str(next(iter(a))), F)
    rhs = Const('w' + str(next(iter(b))), F)
    h = Function('poseidon_observer', F, IntSort())
    constraints = list(parse_smt2_string(circuit.smt().replace('QF_FF', 'ALL')))
    constraints.append(h(lhs) == h(rhs) if equality else h(lhs) != h(rhs))
    return constraints


def poseidon_models(factory):
    for field in FIELDS:
        for equality in [True, False]:
            constraints = poseidon_constraints(field, 1, equality)
            s = check(factory, constraints, sat if equality else unsat, (field, 'Poseidon UF', equality))
            native(s)


def forced_fallback():
    def factory():
        s = SimpleSolver()
        s.set('ff.max_steps', 0)
        s.set('ff.root_split', False)
        return s
    # Re-exercise UF congruence, finite cardinality, cores and scoped bridge
    # axioms independently from the native implementation.
    examples(factory)
    finite_domains(factory)
    incremental(factory)
    exhaustive_uf(factory)
    F = FiniteFieldSort(7)
    x = Const('fallback_x', F)
    s = factory()
    for _ in range(3):
        s.push()
        s.add(x*x == 1)
        assert s.check() == sat
        assert s.statistics().get_key_value('ff bv fallbacks') > 0
        s.pop()
        s.push()
        s.add(x*x == 3)
        assert s.check() == unsat
        s.pop()
    s.reset()
    s.add(x*x == 2)
    assert s.check() == sat
    assert is_true(s.model().eval(x*x == 2))


def resource_recovery():
    F = FiniteFieldSort(257)
    x = Const('limited_x', F)
    f = Function('limited_f', F, IntSort())
    constraints = [x*x == 4, f(x) == 10, f(-x) == 20]
    for algebra_steps in [0, 2000000]:
        for limit in [1, 1000]:
            s = SimpleSolver()
            s.set('ff.max_steps', algebra_steps)
            s.set(rlimit=limit)
            s.add(*constraints)
            result = s.check()
            assert result in [sat, unknown]
            if limit == 1:
                assert result == unknown
            s.set(rlimit=0, timeout=10000)
            assert s.check() == sat, s.reason_unknown()
            assert all(is_true(s.model().eval(c, model_completion=True)) for c in constraints)


if __name__ == '__main__':
    for name, factory in [('incremental SMT', SimpleSolver), ('SMT tactic', lambda: Tactic('smt').solver())]:
        for p in FIELDS.values():
            large_field(factory, p)
        poseidon_models(factory)
        print(name + ': large-field UFs, arrays, cores, incremental checks and Poseidon DAGs passed', flush=True)
    forced_fallback()
    resource_recovery()
    print('Forced exact fallback: mixed theories, finite domains, exhaustive UF cases and lifecycle passed', flush=True)
