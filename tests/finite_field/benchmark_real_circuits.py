#!/usr/bin/env python3
"""Compare solver backends on pinned Picus gnark/Plonky2 circuit exports.

This is a monolithic output-determinism check, not an end-to-end Picus run.
Each circuit is copied twice, its inputs are equated, and at least one output
must differ. SAT is an ambiguity witness; UNSAT proves output determinism.
"""
import argparse
import hashlib
import json
import platform
import subprocess
from pathlib import Path

from benchmark_artifacts import run
from benchmark_public_ff import sexprs
from validate_artifact_models import validate, evaluate

COMMIT = '138b151d3a388e5b6c040c163e0a1db04f2ceda6'
FIXTURES = Path(__file__).parent / 'fixtures/real-circuits/picus'


def parse(source):
    data = sexprs(source.replace('[', '(').replace(']', ')'))
    prime = int(next(x[1] for x in data if x[0] == 'prime-number'))
    inputs = [int(x[1]) for x in data if x[0] == 'in']
    outputs = [int(x[1]) for x in data if x[0] == 'out']
    constraints, bounds = [], []
    wires = set(inputs + outputs + [0])
    for x in data:
        if x[0] == 'constraint':
            assert len(x) == 4
            row = [[(int(c), int(v)) for c, v in side] for side in x[1:]]
            constraints.append(row)
            wires.update(v for side in row for _, v in side)
        elif x[0] == 'extra-constraint':
            _, (op, (var, wire), (integer, bound)) = x
            assert (op, var, integer) == ('<', 'var', 'int')
            bounds.append((int(wire), int(bound)))
            wires.add(int(wire))
        else:
            assert x[0] in ('prime-number', 'in', 'out', 'label', 'num-wires'), x
    assert outputs and 0 not in inputs + outputs
    return prime, inputs, outputs, constraints, bounds, sorted(wires - {0})


def encode(source):
    p, inputs, outputs, constraints, bounds, wires = parse(source)
    lines = ['(set-logic QF_FF)', f'(define-sort F () (_ FiniteField {p}))']
    names = []
    def constant(c): return f'(as ff{c % p} F)'
    def var(copy, v): return constant(1) if v == 0 else f'{copy}_{v}'
    def decl(n):
        names.append(n)
        lines.append(f'(declare-const {n} F)')
    def assertion(s): lines.append(f'(assert {s})')
    def add(xs): return constant(0) if not xs else xs[0] if len(xs) == 1 else '(ff.add ' + ' '.join(xs) + ')'
    def lc(copy, side):
        return add([f'(ff.mul {constant(c)} {var(copy, v)})' for c, v in side])
    for copy in ('a', 'b'):
        for v in wires: decl(var(copy, v))
        for a, b, c in constraints:
            assertion(f'(= (ff.mul {lc(copy, a)} {lc(copy, b)}) {lc(copy, c)})')
        for j, (wire, bound) in enumerate(bounds):
            # Canonical field ordering is encoded exactly, never dropped.
            # For width w with 2^w <= p, binary reconstruction cannot wrap p.
            # Lexicographic comparison then enforces the strict integer bound.
            width = (bound - 1).bit_length()
            assert 0 < bound and (1 << width) <= p
            bits = [f'{copy}_range{j}_{i}' for i in range(width)]
            for bit in bits:
                decl(bit)
                assertion(f'(= (ff.mul {bit} (ff.add {bit} {constant(-1)})) {constant(0)})')
            assertion(f'(= {var(copy, wire)} ' + add([f'(ff.mul {constant(1 << i)} {bit})' for i, bit in enumerate(bits)]) + ')')
            if bound != 1 << width:
                # x <= bound-1: scanning from low to high builds a comparison
                # whose most significant unequal bit decides the result.
                le = 'true'
                for i, bit in enumerate(bits):
                    zero = f'(= {bit} {constant(0)})'
                    le = f'(or {zero} {le})' if ((bound - 1) >> i) & 1 else f'(and {zero} {le})'
                assertion(le)
    for v in inputs: assertion(f'(= {var("a", v)} {var("b", v)})')
    diffs = [f'(distinct {var("a", v)} {var("b", v)})' for v in outputs]
    assertion(diffs[0] if len(diffs) == 1 else '(or ' + ' '.join(diffs) + ')')
    lines.append('(check-sat)')
    return '\n'.join(lines) + '\n', names, dict(prime=str(p), field_bits=p.bit_length(),
        original_wires=len(wires)+1, original_constraints=len(constraints), inputs=inputs,
        outputs=outputs, range_constraints=len(bounds), smt_variables=len(names))


def validate_source(source, model, names):
    """Check witnesses directly against SR1CS as well as generated SMT."""
    p, inputs, outputs, rows, bounds, wires = parse(source)
    pairs = next(x for x in sexprs(model) if isinstance(x, list) and len(x) == len(names)
                 and all(isinstance(a, list) and len(a) == 2 and a[0] in names for a in x))
    env = {n: evaluate(v, {}, p) for n, v in pairs}
    def val(copy, v): return 1 if v == 0 else env[f'{copy}_{v}']
    for copy in ('a', 'b'):
        for a, b, c in rows:
            av, bv, cv = [sum(k * val(copy, v) for k, v in side) % p for side in (a, b, c)]
            assert (av*bv-cv) % p == 0
        for v, bound in bounds: assert 0 <= val(copy, v) < bound
    assert all(val('a', v) == val('b', v) for v in inputs)
    assert any(val('a', v) != val('b', v) for v in outputs)
    return {f'{copy}_{v}': val(copy, v) for copy in ('a', 'b') for v in inputs + outputs}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--z3', type=Path, required=True)
    ap.add_argument('--cvc5', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--group', choices=['pure', 'ranged', 'circom', 'all'], default='pure')
    ap.add_argument('--timeout', type=float, default=10)
    ap.add_argument('--repetitions', type=int, default=1)
    ap.add_argument('--case', action='append', help='include only these filename substrings')
    ap.add_argument('--solvers', nargs='+', choices=['z3', 'cvc5', 'cvc5_split'])
    args = ap.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    commands = {'z3': [str(args.z3.resolve()), '-in'],
                'cvc5': [str(args.cvc5.resolve()), '--lang=smt2'],
                'cvc5_split': [str(args.cvc5.resolve()), '--lang=smt2', '--ff-solver=split']}
    if args.solvers: commands = {k: c for k, c in commands.items() if k in args.solvers}
    files = sorted(FIXTURES.rglob('*.sr1cs'))
    files = [f for f in files if args.group == 'all' or
             (f.parent.name in ('int', 'fixed-int') if args.group == 'ranged' else f.parent.name == args.group)]
    if args.case: files = [f for f in files if any(c in f.name for c in args.case)]
    assert files, 'empty selection'
    source_dir = '/gnark-plonky2-verifier' if args.group == 'pure' else ''
    metadata = dict(source=f'https://github.com/Veridise/Picus/tree/{COMMIT}/benchmarks{source_dir}',
        platform=platform.platform(), timeout=args.timeout, memory_mib=4096, jobs=1,
        repetitions=args.repetitions, property='same inputs, differing outputs, all constraints in both copies',
        timing='isolated fresh solver process including parsing; model validation is a separate untimed run',
        binaries={k: dict(sha256=hashlib.sha256(Path(c[0]).read_bytes()).hexdigest(), command=c,
            version=subprocess.check_output([c[0], '--version'], text=True).splitlines()[0]) for k, c in commands.items()})
    if args.case: metadata['case_filters'] = args.case
    meta = args.out/'metadata.json'
    if meta.exists(): assert json.loads(meta.read_text()) == metadata, 'incompatible resume'
    else: meta.write_text(json.dumps(metadata, indent=2)+'\n')
    log = args.out/'runs.jsonl'
    old = [json.loads(x) for x in log.read_text().splitlines()] if log.exists() else []
    done = {(r['case'], r['solver'], r['repetition']) for r in old}
    manifest = []
    with log.open('a', buffering=1) as out:
        for i, f in enumerate(files):
            source = f.read_text()
            case = f.relative_to(FIXTURES).as_posix()
            smt, names, details = encode(source)
            dest = args.out/'inputs'/f.relative_to(FIXTURES).with_suffix('.smt2')
            dest.parent.mkdir(parents=True, exist_ok=True); dest.write_text(smt)
            entry = dict(case=case, source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                         input_sha256=hashlib.sha256(smt.encode()).hexdigest(), **details)
            manifest.append(entry)
            for rep in range(args.repetitions):
                labels = list(commands); off = (i+rep) % len(labels); labels = labels[off:] + labels[:off]
                for solver in labels:
                    if (case, solver, rep) in done: continue
                    cfg = dict(command=commands[solver], smt=smt, timeout=args.timeout, checks=1, memory_mib=4096)
                    row = dict(case=case, solver=solver, repetition=rep, **run(cfg))
                    if row['result'] == 'sat':
                        model_smt = '(set-option :produce-models true)\n' + smt + '(get-value (' + ' '.join(names) + '))\n'
                        model = run(dict(cfg, smt=model_smt, timeout=max(30, args.timeout)))
                        try:
                            assert model['result'] == 'sat', 'model retrieval failed'
                            row['validated_assertions'] = validate(smt, model['stdout'])
                            row['witness_io'] = validate_source(source, model['stdout'], names)
                            row['model_validated'] = True
                        except Exception as exc:
                            row['model_validated'] = False; row['validation_error'] = str(exc)
                        row['model_run'] = model
                    out.write(json.dumps(row)+'\n')
                    print(case, solver, row['result'], round(row['seconds'], 3), row.get('model_validated', ''), flush=True)
    (args.out/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')


if __name__ == '__main__': main()
