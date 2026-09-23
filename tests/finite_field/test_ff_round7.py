"""Semantic, model and core checks for independently implemented algebra optimizations."""
from z3 import *
import test_ff_round6 as previous

FLAGS = ['bounded_elimination', 'adaptive_reduction', 'sugar_pairs', 'gm_pairs', 'div_masks', 'geobucket', 'small_coefficients', 'compact_encoding']


def compact_definitions():
    for p in [7, 4294967291, 4294967311, 21888242871839275222246405745257275088548364400416034343698204186575808495617]:
        f = FiniteFieldSort(p)
        x, y = Consts('compact_x compact_y', f)
        expr = x + y + 1
        for _ in range(7):
            expr = expr * expr + x
        value = 4
        for _ in range(7):
            value = (value * value + 1) % p
        for theory in [False, True]:
            s = SimpleSolver() if theory else Tactic('ff-solve').solver()
            s.set(**{'ff.' + k: True for k in FLAGS},
                  **{'ff.sparse_witness': False, 'ff.model_search': False})
            if not theory: s.set(**{'ff.enum_bits': 0})
            s.add(x == 1, y == 2, expr == value)
            assert s.check() == sat, (p, theory, s.reason_unknown())
            assert s.model().eval(expr).as_long() == value
            s.push(); s.add(expr != value)
            assert s.check() == unsat
            s.pop(); assert s.check() == sat
        # Named assertions exercise dependency accounting across fresh definitions.
        s = SolverFor('QF_FF'); s.set(unsat_core=True, **{'ff.' + k: True for k in FLAGS})
        s.set(**{'ff.model_search': False})
        for tag, q in [('xpin', x == 1), ('ypin', y == 2), ('wrong', expr != value)]:
            s.assert_and_track(q, Bool(tag))
        assert s.check() == unsat
        core = {str(v) for v in s.unsat_core()}
        check = SolverFor('QF_FF'); check.add([q for tag, q in [('xpin', x == 1), ('ypin', y == 2), ('wrong', expr != value)] if tag in core])
        assert check.check() == unsat
    print('compact definitions: original models, incrementality and tracked conflicts across field sizes', flush=True)


def compact_retry():
    p = 21888242871839275222246405745257275088548364400416034343698204186575808495617
    f = FiniteFieldSort(p); x, y = Consts('retry_x retry_y', f)
    expr = x + y + 1
    value = 4
    for _ in range(7):
        expr = expr * expr + x
        value = (value * value + 1) % p
    for route in ['local', 'global']:
        for enabled in [False, True]:
            if route == 'global': set_param('smt.ff.compact_retry', enabled)
            s = Tactic('ff-solve').solver()
            s.set(**{'ff.enum_bits': 0, 'ff.compact_encoding': False,
                     'ff.max_steps': 2000000, 'ff.model_search': False})
            if route == 'local': s.set(**{'ff.compact_retry': enabled})
            s.add(x == 1, y == 2, expr == value)
            status = s.check()
            assert status == (sat if enabled else unknown), (route, enabled, status)
            st = {k:v for k,v in s.statistics()}
            assert bool(st.get('ff compact retries', 0)) == enabled
            if enabled: assert s.model().eval(expr).as_long() == value
    set_param('smt.ff.compact_retry', False)
    print('compact retry: local/global enable-disable controls, original model checked', flush=True)


if __name__ == '__main__':
    previous.FLAGS = FLAGS
    previous.random_systems()
    compact_definitions()
    compact_retry()
