#!/usr/bin/env python3
"""Verify a Circom witness directly against every imported R1CS equation.

This establishes that the single-copy circuit is satisfiable. It is a check
against vacuous determinism results, not an UNSAT proof certificate.
"""
import argparse
import hashlib
import io
import json
from pathlib import Path

from benchmark_real_circuits import parse
from import_real_circuits import read_uint


def validate(source, witness):
    stream = io.BytesIO(witness)
    assert stream.read(4) == b'wtns' and read_uint(stream) == 2
    sections = {}
    for _ in range(read_uint(stream)):
        kind, size = read_uint(stream), read_uint(stream, 8)
        assert kind not in sections
        sections[kind] = stream.read(size)
        assert len(sections[kind]) == size
    assert not stream.read() and set(sections) == {1, 2}
    header = io.BytesIO(sections[1])
    width = read_uint(header); prime = read_uint(header, width); count = read_uint(header)
    assert not header.read() and len(sections[2]) == count * width
    data = io.BytesIO(sections[2])
    values = [read_uint(data, width) for _ in range(count)]
    p, inputs, outputs, rows, bounds, wires = parse(source)
    assert p == prime and values[0] == 1 and max(wires) < count
    assert all(0 <= v < p for v in values)
    for i, row in enumerate(rows):
        a, b, c = [sum(coefficient * values[wire] for coefficient, wire in side) % p for side in row]
        assert (a*b-c) % p == 0, f'violated R1CS equation {i}'
    for wire, bound in bounds: assert values[wire] < bound
    return dict(valid=True, equations_checked=len(rows), witness_wires=count,
                witness_sha256=hashlib.sha256(witness).hexdigest(),
                source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                inputs={str(i): values[i] for i in inputs}, outputs={str(i): values[i] for i in outputs})


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('sr1cs', type=Path)
    ap.add_argument('witness', type=Path)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    result = validate(args.sr1cs.read_text(), args.witness.read_bytes())
    args.out.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result))


if __name__ == '__main__': main()
