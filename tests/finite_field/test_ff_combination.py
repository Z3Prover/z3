#!/usr/bin/env python3
"""Ground field/theory combination, including finite-domain and model checks.

Run with PYTHONPATH=build-ff-cmake/python Z3_LIBRARY_PATH=build-ff-cmake.
Both the public Solver pipeline and the raw SMT context must be sound.
"""
import itertools
import random
from z3 import *


def check(factory, constraints, expected, label):
    s = factory()
    s.set(timeout=10000)
    s.add(*constraints)
    actual = s.check()
    assert actual == expected, (label, actual, s.reason_unknown(), s.sexpr())
    if actual == sat:
        model = s.model()
        for c in constraints:
            value = model.eval(c, model_completion=True)
            assert is_true(value), (label, c, value, model)
        assert not any(str(d).startswith(('ff.encode!', 'ff.decode!')) for d in model.decls()), model
    return s


def examples(factory):
    F = FiniteFieldSort(7)
    x, y = FiniteFieldElems('x y', F)
    one, six = FiniteFieldVal(1, F), FiniteFieldVal(6, F)
    f = Function('f', F, F)
    for result_sort, a, b in [(F, one, six), (IntSort(), 3, 4), (RealSort(), RealVal('1/2'), RealVal('3/2')),
                               (BitVecSort(8), 3, 4), (BoolSort(), True, False)]:
        h = Function('h_' + str(result_sort), F, result_sort)
        check(factory, [x*x == 1, h(x) != h(one), h(x) != h(six)], unsat, 'UF congruence')
        check(factory, [x*x == 1, h(x) == a, h(-x) == b], sat, 'UF model')
    check(factory, [f(x)*f(x) == 3], unsat, 'field-valued UF')
    check(factory, [f(x)*f(x) == 2, f(f(x)) == x + 1], sat, 'nested UF model')
    i = Int('i')
    g = Function('from_int', IntSort(), F)
    check(factory, [i > 1, i < 3, g(i)*g(i) == 1, g(2) != one, g(2) != six], unsat, 'Int to field')
    check(factory, [i > 1, i < 4, g(i)*g(i) == 2], sat, 'Int model')
    r = Real('r')
    gr = Function('from_real', RealSort(), F)
    check(factory, [r == RealVal('3/2'), gr(r)*gr(r) == 3], unsat, 'Real to field')
    check(factory, [r > 0, r < 1, gr(r)*gr(r) == 2], sat, 'Real model')
    v = BitVec('v', 8)
    h = Function('from_bv', v.sort(), F)
    check(factory, [v + 1 == 3, h(v)*h(v) == 3], unsat, 'BV to field')
    check(factory, [v + 1 == 3, h(v)*h(v) == 2], sat, 'BV model')
    A = Array('A', F, F)
    check(factory, [x*x == 1, Select(A, x) != Select(A, one),
                    Select(A, x) != Select(A, six)], unsat, 'field array index')
    check(factory, [Select(A, x)*Select(A, x) == 2, Select(A, -x) == 0], sat, 'field array model')
    B = Array('B', IntSort(), F)
    check(factory, [i == 2, Select(B, i)*Select(B, i) == 3], unsat, 'field array range')
    check(factory, [Select(Store(B, i, x), i) == x, x*x == 2], sat, 'store model')
    Box = Datatype('FFBox')
    Box.declare('box', ('value', F))
    Box = Box.create()
    box = Const('box_instance', Box)
    check(factory, [Box.value(box)*Box.value(box) == 3], unsat, 'datatype selector')
    check(factory, [Box.value(box)*Box.value(box) == 2], sat, 'datatype model')
    G = FiniteFieldSort(5)
    cross = Function('cross', F, G)
    check(factory, [x*x == 1, cross(x)*cross(x) == 2], unsat, 'two fields')
    check(factory, [x*x == 1, cross(x)*cross(x) == 4], sat, 'two fields model')
    check(factory, [x*x == 2, If(i > 0, f(x), f(y)) == 3, i > 0], sat, 'mixed ITE')


def finite_domains(factory):
    # Pigeonholes must remain sound across the theory boundary: F_p is not
    # stably infinite. Test field cardinality and extensional array indices.
    for p in [2, 3, 5, 7]:
        F = FiniteFieldSort(p)
        h = Function('pigeon_' + str(p), IntSort(), F)
        check(factory, [Distinct(*[h(i) for i in range(p+1)])], unsat, 'finite UF range')
        check(factory, [Distinct(*[h(i) for i in range(p)])], sat, 'full UF range model')
        a, b = Consts('a b', ArraySort(F, BoolSort()))
        same = [Select(a, FiniteFieldVal(i, F)) == Select(b, FiniteFieldVal(i, F)) for i in range(p)]
        check(factory, same + [a != b], unsat, 'extensionality over all field indices')
        check(factory, same[:-1] + [a != b], sat, 'extensionality witness model')
    F = FiniteFieldSort(2)
    arrays = [Const('binary_array_' + str(i), ArraySort(F, BoolSort())) for i in range(5)]
    check(factory, [Distinct(*arrays)], unsat, 'nested finite sorts without field terms')


def incremental(factory):
    F = FiniteFieldSort(7)
    x = FiniteFieldElem('inc_x', F)
    f = Function('inc_f', F, IntSort())
    base = [x*x == 1, f(FiniteFieldVal(1, F)) == 10, f(FiniteFieldVal(6, F)) == 20]
    s = check(factory, base, sat, 'incremental base')
    for _ in range(8):
        s.push()
        s.add(f(x) != 10, f(x) != 20)
        assert s.check() == unsat
        s.pop()
        assert s.check() == sat
        assert all(is_true(s.model().eval(c, model_completion=True)) for c in base)
        assert s.check(f(x) != 10, f(x) != 20) == unsat
        assert s.check(f(x) == 20) == sat
    s = factory()
    s.set(unsat_core=True)
    constraints = [x*x == 1, f(x) != f(FiniteFieldVal(1, F)), f(x) != f(FiniteFieldVal(6, F))]
    labels = Bools('root positive negative')
    for c, label in zip(constraints, labels):
        s.assert_and_track(c, label)
    assert s.check() == unsat
    core = {str(c) for c in s.unsat_core()}
    assert core == {str(c) for c in labels}, core
    for removed in range(3):
        check(factory, [c for i, c in enumerate(constraints) if i != removed], sat, 'core premise necessity')
    # Translate a live mixed context; private representation functions belong
    # to the receiving SMT context, not the source context's AST manager.
    # Use plain assertions here: tactic2solver's generic translate does not
    # preserve tracking assumptions (independent of finite fields).
    s = check(factory, constraints, unsat, 'translation source')
    target = Context()
    translated = s.translate(target)
    assert translated.check() == unsat


def lifecycle():
    # SimpleSolver retains the SMT context across calls; tactic-backed solvers
    # can replay goals and would not expose all stale-axiom/backtracking bugs.
    s = SimpleSolver()
    assert s.check() == sat
    F = FiniteFieldSort(13)
    x = FiniteFieldElem('late_x', F)
    h = Function('late_h', F, IntSort())
    for _ in range(4):
        s.push()
        s.add(x*x == 1, h(x) != h(FiniteFieldVal(1, F)), h(x) != h(FiniteFieldVal(12, F)))
        assert s.check() == unsat
        s.pop()
        assert s.check() == sat
    s.reset()
    s.add(h(x) == 9, x*x == 4)
    assert s.check() == sat
    assert is_true(s.model().eval(h(x) == 9))
    for relevance in [0, 1, 2]:
        s = SimpleSolver()
        s.set(relevancy=relevance)
        for _ in range(3):
            s.push()
            s.add(x*x == 1, h(x) != h(FiniteFieldVal(1, F)), h(x) != h(FiniteFieldVal(12, F)))
            assert s.check() == unsat
            s.pop()
            assert s.check() == sat
    # Certificates remain explicitly unsupported, including the new raw path.
    ctx = Context(proof=True)
    F = FiniteFieldSort(7, ctx)
    x = FiniteFieldElem('proof_x', F)
    s = SimpleSolver(ctx=ctx)
    s.add(x*x == 3)
    try:
        assert s.check() == unknown
    except Z3Exception as ex:
        assert 'certificates are not supported' in str(ex), ex


def exhaustive_uf(factory):
    # Independent semantics: enumerate both x and the entire unary function
    # table. Random query answers must match, and every returned model is checked.
    rng = random.Random(72341)
    for p in [2, 3, 5]:
        F = FiniteFieldSort(p)
        x = FiniteFieldElem('random_x', F)
        h = Function('random_h', F, F)
        vals = [FiniteFieldVal(i, F) for i in range(p)]
        for case in range(35):
            a, b, c, d = [rng.randrange(p) for _ in range(4)]
            constraints = [x*x + a*x == b, h(x)*h(x) == c,
                           Or(h(x + 1) == d, h(h(x)) == x)]
            if case % 2:
                constraints.append(h(x) != h(vals[a]))
            expected = unsat
            for xv in range(p):
                if (xv*xv+a*xv) % p != b:
                    continue
                for table in itertools.product(range(p), repeat=p):
                    hx = table[xv]
                    if hx*hx % p == c and (table[(xv+1) % p] == d or table[hx] == xv) and (
                            case % 2 == 0 or hx != table[a]):
                        expected = sat
                        break
                if expected == sat:
                    break
            check(factory, constraints, expected, ('exhaustive UF', p, case))


def conditional_model(factory):
    # A relevant equality-class root may inherit its field theory variable
    # from another member. The native model must assign the root as well.
    field = FiniteFieldSort(3)
    x, y = Consts('conditional_x conditional_y', field)
    query = Implies(If(x == y, -x, -y) == x*x*y,
                    -y == If(x == y, FiniteFieldVal(-4, field), y)*(2+FiniteFieldVal(-1, field)))
    check(factory, [query], sat, 'conditional equality-class model')


if __name__ == '__main__':
    for name, factory in [('default', Solver), ('SMT tactic', lambda: Tactic('smt').solver()),
                          ('incremental SMT', SimpleSolver)]:
        examples(factory)
        finite_domains(factory)
        incremental(factory)
        exhaustive_uf(factory)
        conditional_model(factory)
        print(name + ': mixed theories, models, finite domains, incrementality, cores and 105 exhaustive UF queries passed', flush=True)
    lifecycle()
    print('Late field introduction, reset and proof rejection passed', flush=True)
