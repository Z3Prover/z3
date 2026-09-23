#!/usr/bin/env python3
"""Import Circom --O0 R1CS v1 exports without changing their constraints.

Format: https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md
Run the documented pinned compiler first; this importer does not download code.
"""
import argparse
import hashlib
import io
import json
from pathlib import Path


def read_uint(stream, n=4):
    data = stream.read(n)
    assert len(data) == n, 'truncated R1CS'
    return int.from_bytes(data, 'little')


def convert(raw):
    f = io.BytesIO(raw)
    assert f.read(4) == b'r1cs' and read_uint(f) == 1
    sections = {}
    for _ in range(read_uint(f)):
        kind, size = read_uint(f), read_uint(f, 8)
        assert kind not in sections
        sections[kind] = f.read(size)
        assert len(sections[kind]) == size
    assert not f.read() and set(sections) == {1, 2, 3}, 'only plain R1CS supported'
    h = io.BytesIO(sections[1])
    width = read_uint(h); prime = read_uint(h, width)
    wires, outputs, public, private = [read_uint(h) for _ in range(4)]
    labels, count = read_uint(h, 8), read_uint(h)
    assert not h.read() and len(sections[3]) == wires * 8
    assert outputs and 1 + outputs + public + private <= wires
    # Circom orders constant wire 0, public outputs, public inputs, private
    # inputs, then intermediates. Fix ALL inputs for functional determinism.
    lines = [f'(prime-number {prime})', f'(num-wires {wires})']
    lines += [f'(in {i})' for i in range(1 + outputs, 1 + outputs + public + private)]
    lines += [f'(out {i})' for i in range(1, outputs + 1)]
    c = io.BytesIO(sections[2])
    for _ in range(count):
        sides = []
        for _ in range(3):
            terms = []
            for _ in range(read_uint(c)):
                wire, coefficient = read_uint(c), read_uint(c, width)
                assert wire < wires and coefficient < prime
                terms.append(f'({coefficient} {wire})')
            sides.append('[' + ' '.join(terms) + ']')
        lines.append('(constraint ' + ' '.join(sides) + ')')
    assert not c.read(), 'unparsed constraints'
    return '\n'.join(lines) + '\n', dict(prime=str(prime), wires=wires, public_inputs=public,
        private_inputs=private, outputs=outputs, constraints=count, labels=labels)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('input', type=Path)
    ap.add_argument('output', type=Path)
    args = ap.parse_args()
    raw = args.input.read_bytes()
    text, info = convert(raw)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(text)
    info.update(r1cs_sha256=hashlib.sha256(raw).hexdigest(), sr1cs_sha256=hashlib.sha256(text.encode()).hexdigest())
    args.output.with_suffix('.json').write_text(json.dumps(info, indent=2)+'\n')
    print(args.output.name, info)


if __name__ == '__main__': main()
