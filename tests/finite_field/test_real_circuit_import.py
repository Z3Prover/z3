"""Checks for the benchmark translation boundary, independent of solver code."""
import itertools
import unittest

from benchmark_real_circuits import encode, parse
from benchmark_public_ff import sexprs
from import_real_circuits import convert
from validate_artifact_models import evaluate


class CircuitImportTests(unittest.TestCase):
    def test_two_copy_property(self):
        source = '''(prime-number 5)
        (in 1) (out 2)
        (constraint [(1 1)] [(1 1)] [(1 2)])'''
        smt, _, _ = encode(source)
        assertions = [x[1] for x in sexprs(smt) if x[0] == 'assert']
        for a, b, c, d in itertools.product(range(5), repeat=4):
            env = dict(a_1=a, a_2=b, b_1=c, b_2=d)
            actual = all(evaluate(x, env, 5) for x in assertions)
            expected = a*a % 5 == b and c*c % 5 == d and a == c and b != d
            self.assertEqual(actual, expected)

    def test_exact_range_encoding(self):
        for bound in (1, 2, 3, 15, 16, 100, 255, 256):
            source = f'''(prime-number 257)
            (in 1) (out 2)
            (extra-constraint (< (var 2) (int {bound})))'''
            smt, names, _ = encode(source)
            # Inspect one copy's constraints; the property itself is checked
            # separately above. Enumerate all possible bit reconstructions.
            assertions = [x[1] for x in sexprs(smt) if x[0] == 'assert'
                          and 'b_' not in str(x) and 'distinct' not in str(x)]
            width = (bound - 1).bit_length()
            for value in range(1 << width):
                env = {'a_1': 0, 'a_2': value}
                env.update({f'a_range0_{i}': (value >> i) & 1 for i in range(width)})
                self.assertEqual(all(evaluate(x, env, 257) for x in assertions), value < bound)
            # A non-binary auxiliary assignment must fail its field equation.
            if width:
                env['a_range0_0'] = 2
                self.assertFalse(all(evaluate(x, env, 257) for x in assertions))

    def test_r1cs_ordering_and_constant_wire(self):
        def u(x, n=4): return x.to_bytes(n, 'little')
        # Public output is wire 1, public input wire 2, private input wire 3.
        # (2*x + 1)*y = output, over F17, with a genuinely empty LC in row 2.
        header = u(1) + u(17, 1) + u(4) + u(1) + u(1) + u(1) + u(4, 8) + u(2)
        rows = [[[(1, 0), (2, 2)], [(1, 3)], [(1, 1)]], [[], [], []]]
        constraints = b''.join(u(len(side)) + b''.join(u(w) + u(c, 1) for c, w in side)
                               for row in rows for side in row)
        sections = {2: constraints, 3: b''.join(u(i, 8) for i in range(4)), 1: header}
        raw = b'r1cs' + u(1) + u(3) + b''.join(u(k) + u(len(v), 8) + v for k, v in sections.items())
        text, info = convert(raw)
        p, inputs, outputs, parsed, bounds, wires = parse(text)
        self.assertEqual((p, inputs, outputs, parsed), (17, [2, 3], [1], rows))
        self.assertEqual(info['constraints'], 2)
        with self.assertRaises(AssertionError): convert(raw[:-1])

    def test_reject_unrecognized_constraint(self):
        with self.assertRaises(AssertionError):
            encode('(prime-number 17) (in 1) (out 2) (unknown-constraint 1 2)')


if __name__ == '__main__': unittest.main()
