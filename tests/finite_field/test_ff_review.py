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


def main():
    factories = [Solver, SimpleSolver, lambda: Tactic('smt').solver()]
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
