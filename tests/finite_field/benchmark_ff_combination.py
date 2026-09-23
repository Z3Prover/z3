#!/usr/bin/env python3
"""Reproducible mixed large-field benchmarks, including direct SMT invocation.

Solver wall time includes parsing and modulus validation. SAT Z3 models are
checked separately against every original assertion, outside the timed process.
"""
import argparse
import hashlib
import json
import platform
import subprocess
from pathlib import Path
from z3 import *
from benchmark_zk import run_once
from test_ff_large_combination import poseidon_constraints
from zk_circuits import FIELDS


def cases():
    for field, p in FIELDS.items():
        F = FiniteFieldSort(p)
        x, y = Consts('x y', F)
        f = Function('observe', F, IntSort())
        one, minus_one = FiniteFieldVal(1, F), FiniteFieldVal(p-1, F)
        yield field + '_nonlinear_uf', [x*x == 1, f(x) != f(one), f(x) != f(minus_one)], unsat
        yield field + '_nonlinear_uf_model', [x*x == 1, f(x) == 11, f(-x) == 12], sat
        a = Array('a', F, F)
        yield field + '_array_index', [x*x == 1, Select(a, x) != Select(a, one),
                                       Select(a, x) != Select(a, minus_one)], unsat
        yield field + '_symbolic_determinism', [y == x*x, x*x*x*x == 1,
                                               f(y) != f(one), f(y) != f(minus_one)], unsat
        for count in [1, 4]:
            for equality in [True, False]:
                yield (f'{field}_poseidon_{count}_uf_' + ('model' if equality else 'equivalence'),
                       poseidon_constraints(field, count, equality), sat if equality else unsat)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--z3', default='build-ff-cmake/z3')
    ap.add_argument('--cvc5', required=True)
    ap.add_argument('--baseline', help='previous BV-only Z3; run on non-Poseidon cases')
    ap.add_argument('--timeout', type=float, default=3)
    ap.add_argument('--repeat', type=int, default=3)
    ap.add_argument('--out', type=Path, default=Path('tests/finite_field/results/large-combination.json'))
    ap.add_argument('--inputs', type=Path, default=Path('/private/tmp/ff-large-combination-inputs'))
    args = ap.parse_args()
    commands = {'native_smt': [args.z3, '-in', f'-t:{int(args.timeout*1000)}'],
                'default': [args.z3, '-in', f'-t:{int(args.timeout*1000)}'],
                'cvc5': [args.cvc5, '--lang=smt2', f'--tlimit-per={int(args.timeout*1000)}'],
                'cvc5_split': [args.cvc5, '--lang=smt2', '--ff-solver=split', f'--tlimit-per={int(args.timeout*1000)}']}
    if args.baseline:
        commands['bv_baseline'] = [args.baseline, '-in', f'-t:{int(args.timeout*1000)}']
    report = dict(platform=platform.platform(), timeout_seconds=args.timeout,
                  external_deadline_seconds=args.timeout + 2, repeat=args.repeat,
                  timing='fresh solver process wall time, including parsing and field validation',
                  versions={label: {'command': cmd, 'sha256': hashlib.sha256(Path(cmd[0]).read_bytes()).hexdigest(),
                                    'version': subprocess.check_output([cmd[0], '--version'], text=True).splitlines()[0]}
                            for label, cmd in commands.items()}, cases=[])
    args.inputs.mkdir(parents=True, exist_ok=True)
    for name, constraints, expected in cases():
        s = SimpleSolver()
        s.add(*constraints)
        text = '(set-logic ALL)\n' + s.sexpr()
        path = args.inputs / (name + '.smt2')
        path.write_text(text + '(check-sat)\n')
        row = dict(case=name, expected=str(expected), input=str(path),
                   sha256=hashlib.sha256(path.read_bytes()).hexdigest(), results={})
        for label, cmd in commands.items():
            if label == 'bv_baseline' and 'poseidon' in name:
                continue
            check = '(check-sat-using smt)' if label in ['native_smt', 'bv_baseline'] else '(check-sat)'
            smt = text + check + '\n'
            if not label.startswith('cvc5'):
                smt += '(get-info :all-statistics)\n'
            runs = [run_once(cmd, smt, args.timeout + 2) for _ in range(args.repeat)]
            for r in runs:
                assert r['result'] in [str(expected), 'unknown', 'timeout'], (name, label, r)
                r.pop('stdout')
                r['stderr'] = r['stderr'][:1000]
            row['results'][label] = runs
        if expected == sat:
            s.set(timeout=int(args.timeout*1000))
            assert s.check() == sat, (name, s.reason_unknown())
            model = s.model()
            assert all(is_true(model.eval(c, model_completion=True)) for c in constraints), name
            row['native_model_validated'] = True
        report['cases'].append(row)
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(report, indent=2) + '\n')
        print(json.dumps({name: {label: [(r['result'], round(r['seconds'], 4)) for r in runs]
                                      for label, runs in row['results'].items()}}), flush=True)


if __name__ == '__main__':
    main()
