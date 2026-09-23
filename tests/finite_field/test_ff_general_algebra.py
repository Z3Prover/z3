"""Independent semantic checks for sparse batches and precise conflict support.

Seeds, coefficients and shapes are independent of the paper artifact inputs.
All small-field answers and returned cores are checked by finite enumeration.
"""
import itertools
import random
from z3 import *


def random_systems():
    rng = random.Random(729143)
    checked = batches = 0
    for p in [2, 3, 5, 7, 11]:
        field = FiniteFieldSort(p)
        xs = Consts('general_x general_y general_z', field)
        points = list(itertools.product(range(p), repeat=3))
        for trial in range(45):
            specs = []
            constraints = []
            for _ in range(rng.randrange(2, 6)):
                terms = [(rng.randrange(1, p), tuple(rng.randrange(3) for _ in range(rng.randrange(4))))
                         for _ in range(rng.randrange(2, 7))]
                different = rng.randrange(5) == 0
                specs.append((terms, different))
                expr = FiniteFieldVal(0, field)
                for coeff, mon in terms:
                    term = FiniteFieldVal(coeff, field)
                    for v in mon: term *= xs[v]
                    expr += term
                constraints.append(expr != 0 if different else expr == 0)
            def satisfies(values, indices):
                for index in indices:
                    terms, different = specs[index]
                    total = 0
                    for coeff, mon in terms:
                        for var in mon: coeff *= values[var]
                        total += coeff
                    if (total % p != 0) != different: return False
                return True
            expected = any(satisfies(point, range(len(specs))) for point in points)
            solver = SolverFor('QF_FF')
            solver.set(timeout=3000, unsat_core=True)
            for i, q in enumerate(constraints): solver.assert_and_track(q, Bool('general_tag_'+str(i)))
            answer = solver.check()
            assert answer == (sat if expected else unsat), (p, trial, answer, solver.reason_unknown())
            if answer == sat:
                assert all(is_true(solver.model().eval(q, model_completion=True)) for q in constraints)
            else:
                chosen = [int(str(tag).rsplit('_', 1)[1]) for tag in solver.unsat_core()]
                assert not any(satisfies(point, chosen) for point in points), (p, trial, chosen)
            st = solver.statistics()
            batches += st.get_key_value('ff matrix batches') if 'ff matrix batches' in st.keys() else 0
            checked += 1
    assert batches > 0, 'generated systems did not exercise batched reduction'
    print(checked, 'random three-variable systems and cores exhaustively verified;', batches, 'matrix batches')


def mixed_domains():
    checked = 0
    for p in [2, 3, 7, 97, 4294967291,
              21888242871839275222246405745257275088548364400416034343698204186575808495617]:
        field = FiniteFieldSort(p)
        x, y, z = Consts('domain_x domain_y domain_z', field)
        observer = Function('domain_observer', field, IntSort())
        guard = Bool('domain_guard')
        # The finite-domain lemma must apply to compound/foreign field terms,
        # and must remain conditional under disjunctions and scope changes.
        for term in [x, x+y, z*x+y]:
            domain = term*term == term
            for expected, conditions in [
                (unsat, [domain, term != 0, term != 1]),
                (sat, [domain, observer(term) == 3]),
                (sat if p > 2 else unsat, [Or(domain, guard), guard, term != 0, term != 1])]:
                solver = SimpleSolver()
                solver.set(timeout=3000, **{'ff.boolean_split': True})
                solver.add(conditions)
                assert solver.check() == expected, (p, term, conditions)
                if expected == sat:
                    assert all(is_true(solver.model().eval(q, model_completion=True)) for q in conditions)
                checked += 1
    print(checked, 'guarded field-domain checks across small, machine-boundary and cryptographic primes')


def word_boundary():
    # Invertible row mixing hides a known quadratic system. Coefficients near
    # 2^32 exercise full-width products in matrix elimination; larger primes
    # must stay on the arbitrary-precision path. Scalar and batched algorithms
    # have to agree with the independently known roots, not just each other.
    rng = random.Random(188531)
    checked = batches = 0
    for p in [65537, 4294967291, 4294967311,
              21888242871839275222246405745257275088548364400416034343698204186575808495617]:
        field = FiniteFieldSort(p)
        x, y = Consts('boundary_x boundary_y', field)
        for trial in range(6):
            for consistent in [False, True]:
                rows = [x*x-13**2, y*y-29**2, x*y-(13*29+(not consistent))]
                for _ in range(8):
                    i, j = rng.sample(range(3), 2)
                    rows[i] += rng.randrange(1, p)*rows[j]
                for enabled in [False, True]:
                    solver = Tactic('ff-solve').solver()
                    solver.set(**{'ff.batch': enabled, 'ff.sparse_witness': False,
                                  'ff.model_search': False})
                    solver.add([row == 0 for row in rows])
                    answer = solver.check()
                    assert answer == (sat if consistent else unsat), (p, trial, enabled, answer)
                    if answer == sat:
                        assert all(is_true(solver.model().eval(row == 0, model_completion=True)) for row in rows)
                    st = solver.statistics()
                    count = st.get_key_value('ff matrix batches') if 'ff matrix batches' in st.keys() else 0
                    assert not count or (enabled and p < 2**32)
                    batches += count
                    checked += 1
    assert batches > 0
    print(checked, 'scalar/batched boundary-prime checks;', batches, 'matrix batches')


def mixed_bitvectors():
    # Use an arbitrary BV operation as the argument of a field-valued UF.
    # Equality of its argument must reach the field solver through congruence;
    # the guarded Boolean-domain consequence must then return to BV reasoning.
    # Both branch choices, assumptions and restored scopes are exercised.
    checked = 0
    for width in [1, 2, 3, 5, 8]:
        a, b = BitVecs('mix_a mix_b', width)
        operations = [a+b, a*b, a >> b, UDiv(a, b), URem(a, b), a ^ b]
        for p in [3, 17, 4294967291,
                  21888242871839275222246405745257275088548364400416034343698204186575808495617]:
            field = FiniteFieldSort(p)
            f = Function('mix_to_field', a.sort(), field)
            h = Function('mix_from_field', field, a.sort())
            zero, one = FiniteFieldVal(0, field), FiniteFieldVal(1, field)
            for operation in operations:
                x, alias = Consts('mix_x mix_alias', field)
                guard = Bool('mix_guard')
                solver = SimpleSolver()
                solver.set(timeout=3000)
                base = [alias == f(operation), x == alias, Or(Not(guard), x*x == x),
                        h(zero) == 0, h(one) == 1]
                solver.add(base)
                solver.push()
                solver.add(h(f(operation)) != 0, h(f(operation)) != 1)
                assert solver.check(guard) == unsat
                # In width one, the BV range itself excludes a third value.
                assert solver.check(Not(guard)) == (sat if width > 1 else unsat)
                solver.pop()
                solver.add(guard, h(f(operation)) == 1)
                assert solver.check() == sat
                assert all(is_true(solver.model().eval(q, model_completion=True)) for q in base)
                checked += 3
    print(checked, 'mixed BV/field checks across operations, widths, primes and scopes')


def sparse_witnesses():
    checked = witnesses = 0
    for p in [5, 17, 65537, 4294967291,
              21888242871839275222246405745257275088548364400416034343698204186575808495617]:
        field = FiniteFieldSort(p)
        x, y, z = Consts('slice_x slice_y slice_z', field)
        # The first admits sparse solutions. The second requires all three
        # coordinates to be nonzero, so every proposed sparse slice fails:
        # failure must fall through to the complete solver, never imply UNSAT.
        for query in [[x*x+y*y+z*z == 1], [x*y*z == 1],
                      [(x-2)*(y-3)*(z-4) == 1]]:
            for enabled in [False, True]:
                solver = Tactic('ff-solve').solver()
                # model_search independently enables sparse slices. Disable it
                # explicitly so the off arm really excludes that algorithm,
                # regardless of the interface defaults adopted later.
                solver.set(**{'ff.sparse_witness': enabled, 'ff.model_search': False})
                solver.add(query)
                assert solver.check() == sat, (p, enabled, query)
                assert all(is_true(solver.model().eval(q, model_completion=True)) for q in query)
                st = solver.statistics()
                count = st.get_key_value('ff sparse witnesses') if 'ff sparse witnesses' in st.keys() else 0
                assert not count or enabled
                witnesses += count
                checked += 1
    assert witnesses > 0
    print(checked, 'sparse-witness and failed-slice fallthrough checks;', witnesses, 'validated witnesses')


def global_parameters():
    # SMT-LIB/global options and per-solver options must reach the same backend.
    field = FiniteFieldSort(17)
    x, y = Consts('parameter_x parameter_y', field)
    try:
        for enabled in [False, True]:
            set_param('smt.ff.batch', enabled)
            solver = SolverFor('QF_FF')
            solver.set(**{'ff.model_search': False})
            solver.add(x*x+y*y == 3, x*y == 1)
            assert solver.check() == unsat
            st = solver.statistics()
            batches = st.get_key_value('ff matrix batches') if 'ff matrix batches' in st.keys() else 0
            assert bool(batches) == enabled
    finally:
        reset_params()
    for enabled in [False, True]:
        solver = SimpleSolver()
        solver.set(**{'ff.boolean_split': enabled})
        solver.add(x*x == x, x != 0, x != 1)
        assert solver.check() == unsat
        st = solver.statistics()
        clauses = st.get_key_value('ff root clauses') if 'ff root clauses' in st.keys() else 0
        assert bool(clauses) == enabled
    print('global batch option and opt-in Boolean splitting checked in both modes')


if __name__ == '__main__':
    random_systems()
    mixed_domains()
    word_boundary()
    mixed_bitvectors()
    sparse_witnesses()
    global_parameters()
