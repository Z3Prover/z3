"""Exercise fused scalar reduction through real solver interfaces.

The general-algebra suite supplies independently enumerated answers and cores;
C++ tests separately compare exact remainders, sugar, premises and work.
"""
from z3 import *
import test_ff_general_algebra as general


def count(solver, key):
    return next((v for k, v in solver.statistics() if k == key), 0)


def interfaces():
    f = FiniteFieldSort(17)
    x, y = Consts('matrix_x matrix_y', f)
    seen = 0
    for name in ['ff-solve', 'ff-sat', 'QF_FF', 'native']:
        for enabled in [False, True]:
            s = Tactic(name).solver() if name.startswith('ff-') else SimpleSolver() if name == 'native' else SolverFor(name)
            s.set(**{'ff.fused_reduction': enabled,
                     'ff.model_search': False, 'ff.sparse_witness': False})
            s.push()
            # Squaring xy=2 conflicts with x^2=y^2=1 already over the
            # algebraic closure, so this checks matrix algebra without relying
            # on the separate finite-field root-completion route.
            # Invertible row mixing hides the three equations so symbolic
            # preprocessing and matrix reducers are exercised as well. The
            # mixing matrix has determinant 1 modulo 17.
            s.add(14*x*x + 6*x*y + 14*y*y + 11 == 0,
                  3*x*x + 4*x*y + 16*y*y + 7 == 0,
                  10*x*x + 6*y*y + 1 == 0)
            assert s.check() == unsat, (name, enabled, s.reason_unknown())
            uses = count(s, 'ff fused reductions')
            assert enabled or uses == 0
            seen += uses
            s.pop()
            s.add(x == 1, y == 1)
            assert s.check() == sat
            assert s.model().eval(y).as_long() == 1
    assert seen > 0, 'interface checks never exercised fused reductions'
    print('local options, all interfaces, exact UNSAT and push/pop model recovery')


def main():
    interfaces()
    try:
        for packed in [False, True]:
            set_param('smt.ff.fused_reduction', True)
            set_param('smt.ff.compact_matrix', packed)
            general.random_systems()
            general.mixed_domains()
            general.word_boundary()
    finally:
        reset_params()
    print('global fused reductions: exhaustive models/cores, mixed theories and word boundaries')


if __name__ == '__main__':
    main()
