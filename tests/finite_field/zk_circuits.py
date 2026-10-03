"""R1CS-shaped ZK gadgets with independent integer witnesses and SMT-LIB export.

These are full-round reference-parameter permutations and curve gadgets, not
compiler-exported production applications. Wire 0 is the constant one.
"""
import json
from pathlib import Path

FIXTURE = Path(__file__).with_name('fixtures') / 'poseidon_t3.json'
PARAMETERS = json.loads(FIXTURE.read_text())['fields']
FIELDS = {name: int(q['prime']) for name, q in PARAMETERS.items()}


def lc(*items):
    result = {}
    for terms in items:
        for wire, coeff in terms.items():
            result[wire] = result.get(wire, 0) + coeff
    return {wire: coeff for wire, coeff in result.items() if coeff}


def scaled(terms, coeff):
    return {wire: value * coeff for wire, value in terms.items()}


class Circuit:
    def __init__(self, prime):
        self.p = prime
        self.witness = [1]
        self.constraints = []
        self.pins = {}
        self.different = []

    def value(self, terms, assignment=None):
        assignment = self.witness if assignment is None else assignment
        return sum(assignment[i] * c for i, c in terms.items()) % self.p

    def wire(self, value):
        self.witness.append(value % self.p)
        return {len(self.witness)-1: 1}

    def mul(self, a, b):
        out = self.wire(self.value(a) * self.value(b))
        self.constraints.append((a, b, out))
        return out

    def linear(self, a):
        out = self.wire(self.value(a))
        self.constraints.append((a, {0: 1}, out))
        return out

    def inverse(self, a):
        out = self.wire(pow(self.value(a), -1, self.p))
        self.constraints.append((a, out, {0: 1}))
        return out

    def bit(self, value):
        out = self.wire(value)
        self.constraints.append((out, out, out))
        return out

    def pin(self, terms, value=None):
        assert len(terms) == 1 and next(iter(terms.values())) == 1
        self.pins[next(iter(terms))] = self.value(terms) if value is None else value % self.p

    def valid(self, assignment):
        if len(assignment) != len(self.witness) or assignment[0] != 1:
            return False
        if any(not 0 <= x < self.p for x in assignment):
            return False
        ev = lambda terms: self.value(terms, assignment)
        return (all(ev(a)*ev(b) % self.p == ev(c) for a, b, c in self.constraints)
                and all(assignment[i] == v for i, v in self.pins.items())
                and all(ev(a) != ev(b) for a, b in self.different))

    def smt(self):
        def val(n): return f'(as ff{n % self.p} F)'
        def expression(terms):
            args = []
            for i, coeff in sorted(terms.items()):
                coeff %= self.p
                if not coeff: continue
                if i == 0: args.append(val(coeff))
                elif coeff == 1: args.append(f'w{i}')
                else: args.append(f'(ff.mul {val(coeff)} w{i})')
            return val(0) if not args else args[0] if len(args) == 1 else '(ff.add ' + ' '.join(args) + ')'
        lines = ['(set-logic QF_FF)', f'(define-sort F () (_ FiniteField {self.p}))']
        lines += [f'(declare-const w{i} F)' for i in range(1, len(self.witness))]
        lines += [f'(assert (= w{i} {val(v)}))' for i, v in self.pins.items()]
        for a, b, c in self.constraints:
            left = expression(a) if b == {0: 1} else f'(ff.mul {expression(a)} {expression(b)})'
            lines.append(f'(assert (= {left} {expression(c)}))')
        lines += [f'(assert (distinct {expression(a)} {expression(b)}))' for a, b in self.different]
        return '\n'.join(lines) + '\n'


def permutation_reference(field, state):
    q = PARAMETERS[field]; p = FIELDS[field]
    matrix = [[int(v, 16) for v in row] for row in q['mds']]
    for r, constants in enumerate(q['constants']):
        state = [(v + int(c, 16)) % p for v, c in zip(state, constants)]
        for i in range(3 if r < 4 or r >= 60 else 1):
            state[i] = pow(state[i], 5, p)
        state = [sum(c*v for c, v in zip(row, state)) % p for row in matrix]
    return state


def poseidon(circuit, field, state, alternate=False):
    q = PARAMETERS[field]
    for r, constants in enumerate(q['constants']):
        state = [lc(v, {0: int(c, 16)}) for v, c in zip(state, constants)]
        for i in range(3 if r < 4 or r >= 60 else 1):
            x = state[i]; square = circuit.mul(x, x)
            # Independent multiplication schedules for symbolic equivalence.
            if alternate:
                cube = circuit.mul(square, x)
                state[i] = circuit.mul(cube, square)
            else:
                fourth = circuit.mul(square, square)
                state[i] = circuit.mul(fourth, x)
        state = [circuit.linear(lc(*(scaled(v, int(c, 16)) for c, v in zip(row, state)))) for row in q['mds']]
    return state


def poseidon_case(field, count, mode):
    c = Circuit(FIELDS[field]); inputs = [c.wire(v) for v in [0, 1, 2]]
    if mode in ['fixed_sat', 'fixed_unsat']:
        for v in inputs: c.pin(v)
    elif mode == 'partial':
        c.pin(inputs[0]); c.pin(inputs[1])
        b0, b1 = c.bit(0), c.bit(1)
        c.constraints.append((lc(b0, scaled(b1, 2)), {0: 1}, inputs[2]))
    state = inputs
    expected = [0, 1, 2]
    for _ in range(count):
        state = poseidon(c, field, state)
        expected = permutation_reference(field, expected)
    assert [c.value(v) for v in state] == expected
    if mode == 'equivalence':
        other = inputs
        for _ in range(count): other = poseidon(c, field, other, alternate=True)
        c.different.append((state[0], other[0]))
    elif mode != 'free':
        c.pin(state[0], expected[0] + (mode == 'fixed_unsat'))
    return c, 'unsat' if mode in ['fixed_unsat', 'equivalence'] else 'sat'


def range_case(field, width, mode):
    c = Circuit(FIELDS[field]); value = 37
    bits = [c.bit((value >> i) & 1) for i in range(width)]
    total = lc(*(scaled(b, 1 << i) for i, b in enumerate(bits)))
    if mode == 'value':
        # Deliberately plain R1CS linear combinations, not the ff.bitsum extension.
        out = c.linear(total); c.pin(out, value)
    else:
        other = [c.bit((value >> i) & 1) for i in range(width)]
        right = lc(*(scaled(b, 1 << i) for i, b in enumerate(other)))
        c.constraints.append((total, {0: 1}, right))
        c.different.append((bits[0], other[0]))
    assert 2**width <= c.p
    return c, 'sat' if mode == 'value' else 'unsat'


def sqrt_mod(n, p):
    n %= p
    if n == 0: return 0
    if pow(n, (p-1)//2, p) != 1: return None
    q, s = p-1, 0
    while q % 2 == 0: q //= 2; s += 1
    z = 2
    while pow(z, (p-1)//2, p) != p-1: z += 1
    root, t, b = pow(n, (q+1)//2, p), pow(n, q, p), pow(z, q, p)
    while t != 1:
        i, u = 0, t
        while u != 1: u = u*u % p; i += 1
        v = pow(b, 1 << (s-i-1), p)
        root = root*v % p; b = v*v % p; t = t*b % p; s = i
    return root


def curve_parameters(field):
    p = FIELDS[field]
    return (168700, 168696) if field == 'bn254' else (-1, -10240*pow(10241, -1, p) % p)


def curve_point(field):
    p = FIELDS[field]; a, d = curve_parameters(field)
    for x in range(2, 100):
        y = sqrt_mod((1-a*x*x)*pow(1-d*x*x, -1, p), p)
        if y not in [None, 0, 1]: return x, y
    raise AssertionError('no point')


def edwards_add(c, left, right, a, d):
    x, y = left; u, v = right
    xx, yy = c.mul(x, u), c.mul(y, v)
    cross = c.mul(xx, yy)
    nx = lc(c.mul(x, v), c.mul(y, u)); ny = lc(yy, scaled(xx, -a))
    ix = c.inverse(lc({0: 1}, scaled(cross, d)))
    iy = c.inverse(lc({0: 1}, scaled(cross, -d)))
    return c.mul(nx, ix), c.mul(ny, iy)


def on_curve(c, point, a, d):
    x, y = point; xx, yy = c.mul(x, x), c.mul(y, y)
    c.constraints.append((xx, scaled(yy, d), lc(scaled(xx, a), yy, {0: -1})))


def curve_case(field, count, mode):
    c = Circuit(FIELDS[field]); a, d = curve_parameters(field)
    point = tuple(c.wire(v) for v in curve_point(field))
    on_curve(c, point, a, d)
    if mode.startswith('fixed'):
        for v in point: c.pin(v)
    if mode == 'partial':
        c.pin(point[0])  # Recover y from the curve equation; there are two roots.
    state = point
    for _ in range(count): state = edwards_add(c, state, point, a, d)
    if mode == 'oncurve':
        x, y = state; xx, yy = c.mul(x, x), c.mul(y, y)
        product = c.mul(xx, yy)
        c.different.append((lc(scaled(xx, a), yy), lc({0: 1}, scaled(product, d))))
    else:
        c.pin(state[0], c.value(state[0]) + (mode == 'fixed_unsat'))
    return c, 'unsat' if mode in ['fixed_unsat', 'oncurve'] else 'sat'


def cases(large=False):
    for field in FIELDS:
        for count in ([1, 4, 16] if large else [1, 4]):
            for mode in ['fixed_sat', 'fixed_unsat']:
                yield f'{field}_poseidon_{count}_{mode}', *poseidon_case(field, count, mode)
        for mode in ['partial', 'free', 'equivalence']:
            yield f'{field}_poseidon_1_{mode}', *poseidon_case(field, 1, mode)
        for width in ([8, 32, 128, 253] if large else [8, 32, 128]):
            for mode in ['value', 'injectivity']:
                yield f'{field}_range_{width}_{mode}', *range_case(field, width, mode)
        for count in ([1, 8, 64] if large else [1, 8]):
            for mode in ['fixed_sat', 'fixed_unsat']:
                yield f'{field}_edwards_{count}_{mode}', *curve_case(field, count, mode)
        for mode in ['partial', 'oncurve']:
            yield f'{field}_edwards_1_{mode}', *curve_case(field, 1, mode)


def self_test():
    for field, q in PARAMETERS.items():
        assert permutation_reference(field, q['vector_input']) == [int(v, 16) for v in q['vector_output']]
    for name, c, expected in cases(large=True):
        assert c.valid(c.witness) == (expected == 'sat'), name
    print('Reference Poseidon vectors and all generated witnesses checked')


if __name__ == '__main__': self_test()
