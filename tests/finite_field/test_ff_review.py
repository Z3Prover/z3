#!/usr/bin/env python3
"""Regressions for opaque field terms versus independently assignable variables."""
from z3 import *


def checked(factory, constraints, expected):
    solver = factory()
    solver.set(timeout=5000)
    solver.add(*constraints)
    result = solver.check()
    assert result == expected, (result, solver.reason_unknown(), constraints)
    if result == sat:
        model = solver.model()
        assert all(is_true(model.eval(c, model_completion=True)) for c in constraints), model


def conditional_arithmetic(factory):
    # Term ITEs do not necessarily own theory variables. Their selected-branch
    # equalities must still constrain the opaque leaves in field polynomials.
    for p in [7, 101]:
        field = FiniteFieldSort(p)
        zero, one = FiniteFieldVal(0, field), FiniteFieldVal(1, field)
        c, d = Bools('review_ite_c review_ite_d')
        a, b = If(c, zero, one), If(d, zero, one)
        # The sum ranges over {0, 1, 2}, without modular wrap. Check SAT models
        # as well as UNSAT: dropping the ITE equalities can break both.
        for total in range(4):
            checked(factory, [a + b == total], sat if total < 3 else unsat)
        checked(factory, [a + b == 2, a != b], unsat)
        checked(factory, [c, d, a + b != zero], unsat)

        # The selected branches change across assumptions and popped scopes;
        # neither missing equalities nor stale ones may survive the next check.
        solver = factory()
        solver.set(timeout=5000)
        base = a + b == 2
        solver.add(base)
        for _ in range(2):
            assert solver.check(c) == unsat
            assert solver.check(Not(c), Not(d)) == sat
            model = solver.model()
            assert all(is_true(model.eval(f, model_completion=True))
                       for f in [base, Not(c), Not(d)]), model
            solver.push()
            solver.add(c)
            assert solver.check() == unsat
            solver.pop()
            assert solver.check() == sat
            assert is_true(solver.model().eval(base, model_completion=True))
        solver.reset()
        solver.add(c, d, a + b == zero)
        assert solver.check() == sat
        assert all(is_true(solver.model().eval(f, model_completion=True))
                   for f in [c, d, a + b == zero])


def shared_tactic():
    # Force the common algebra path rather than the small-bit shortcut. Compare
    # both compact modes with an exhaustive oracle, including exported models.
    for p in [2, 3, 7]:
        field = FiniteFieldSort(p)
        x, y, z = Consts('shared_x shared_y shared_z', field)
        for compact in [False, True]:
            factory = lambda: With(Tactic('ff-solve'), **{
                'ff.enum_bits': 0, 'ff.compact_encoding': compact}).solver()
            for a in range(p):
                for b in range(p):
                    constraints = [x*y == a, x+y == b, x != b, z == x*x + y]
                    expected = any(u*v % p == a and (u+v) % p == b and u != b
                                   for u in range(p) for v in range(p))
                    checked(factory, constraints, sat if expected else unsat)

    # Reconstruction must include variables removed before polynomial encoding,
    # across independent fields and pairwise expansion of a distinct constraint.
    f7, f11 = FiniteFieldSort(7), FiniteFieldSort(11)
    x, y, z = Consts('shared_core_x shared_core_y shared_core_z', f7)
    u, v = Consts('shared_other_u shared_other_v', f11)
    factory = lambda: With(Tactic('ff-solve'), **{'ff.enum_bits': 0}).solver()
    checked(factory, [x == 2, y == x*x, z == y+1, Distinct(x, y, z),
                      u == 8, v == u*u], sat)
    checked(factory, [x == 2, y == x*x, Distinct(x, y, y)], unsat)

    # Opaque leaves are legal only when a frontend supplies theory semantics.
    # The standalone tactic must keep rejecting UF, arrays and term ITEs.
    c = Bool('shared_condition')
    fun = Function('shared_fun', f7, f7)
    array = Array('shared_array', IntSort(), f7)
    for term in [fun(x), Select(array, 0), If(c, x, y)]:
        goal = Goal()
        goal.add(term == 0)
        try:
            With(Tactic('ff-solve'), **{'ff.enum_bits': 0})(goal)
        except Z3Exception:
            assert len(goal) == 1  # failure must leave the input goal intact
        else:
            raise AssertionError(('accepted foreign term', term))

    ctx = Context(proof=True)
    pf = FiniteFieldSort(7, ctx=ctx)
    px = Const('shared_proof_x', pf)
    goal = Goal(proofs=True, ctx=ctx)
    goal.add(px == 0, px != 0)
    try:
        Tactic('ff-solve', ctx=ctx)(goal)
    except Z3Exception as ex:
        assert 'certificates' in str(ex)
    else:
        raise AssertionError('proof mode silently accepted')


def main():
    shared_tactic()
    factories = [Solver, SimpleSolver, lambda: Tactic('smt').solver()]
    for factory in factories:
        conditional_arithmetic(factory)
    for p in [2, 3, 7, 101]:
        field = FiniteFieldSort(p)
        x, y = Consts('review_x review_y', field)
        c = Bool('review_c')
        zero, one = FiniteFieldVal(0, field), FiniteFieldVal(1, field)
        h = Function('review_h', field, field)
        for factory in factories:
            # Opaque field terms need congruence and pointwise function models.
            checked(factory, [h(x) == 0, h(y) == 1], sat)
            checked(factory, [x == y, h(x) == 0, h(y) == 1], unsat)
            checked(factory, [x*x == 1, h(x) == 1, h(-x) == p-1], sat)
        bv = lambda: Then('ff2bv', 'smt').solver()
        # This is UNSAT in every field: the ITE cannot take a third value.
        checked(bv, [Distinct(If(c, zero, one), zero, one)], unsat)
        checked(bv, [If(c, zero, one) == one], sat)
        # A direct standalone encoding cannot silently abstract f(x), f(y).
        for tactic in ['ff2bv', 'ff-solve']:
            goal = Goal()
            goal.add(h(x) == 0, h(y) == 1, x == y)
            try:
                result = Tactic(tactic)(goal)
            except Z3Exception:
                pass  # unsupported combinations must fall back to SMT
            else:
                assert len(result) == 1 and result[0].is_decided_unsat(), result
    # An independent exhaustive oracle for a Boolean/field expression involving
    # a nested ITE and bitsums; this caught an invalid model in the review branch.
    field = FiniteFieldSort(2)
    x, y = Consts('review_bit_x review_bit_y', field)
    formula = Or(FiniteFieldBitsum(If(x == y, x, FiniteFieldVal(-3, field)), -y) !=
                 FiniteFieldBitsum(FiniteFieldBitsum(y, x), FiniteFieldBitsum(x, x)), y == -y + 3*y)
    for factory in factories:
        checked(factory, [formula], sat)
    # Generic mixed BV/field subtraction encoding: a packed Boolean result
    # equals a-b+2^width, hence its low bits must agree with modular BV subtraction.
    # The prime exceeds every possible packed value, so there is no field wrap.
    for width in [1, 2, 3]:
        field = FiniteFieldSort(101)
        a, b = BitVecs('review_bv_a review_bv_b', width)
        digits = [FiniteFieldElem('review_digit_' + str(i), field)
                  for i in range(width + 1)]
        zero, one = FiniteFieldVal(0, field), FiniteFieldVal(1, field)
        def bit(value, i):
            return If(Extract(i, i, value) == 1, one, zero)
        def packed(value):
            return Sum([2**i * bit(value, i) for i in range(width)])
        premises = [d*d == d for d in digits]
        premises += [Sum([2**i*d for i, d in enumerate(digits)]) ==
                     packed(a) - packed(b) + 2**width]
        mismatch = Or([digits[i] != bit(a-b, i) for i in range(width)])
        for factory in factories:
            checked(factory, premises + [mismatch], unsat)
    print('Opaque field terms, function models, congruence and ITE encodings passed')


if __name__ == '__main__':
    main()
