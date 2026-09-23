#!/usr/bin/env python3
"""Before/after root clauses; separate solver-only timing from process startup."""
import argparse
import hashlib
import json
import platform
import statistics
from pathlib import Path
from time import perf_counter
from z3 import *
from benchmark_zk import run_once
from benchmark_ff_combination import cases
from zk_circuits import FIELDS


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline', required=True)
    ap.add_argument('--z3', default='build-ff-cmake/z3')
    ap.add_argument('--cvc5', required=True)
    ap.add_argument('--repeat', type=int, default=5)
    ap.add_argument('--out', type=Path, default=Path('tests/finite_field/results/root-clauses.json'))
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    commands = {'before_smt': [args.baseline, '-in'], 'after_smt': [args.z3, '-in'],
                'before_default': [args.baseline, '-in'], 'after_default': [args.z3, '-in'],
                'cvc5': [args.cvc5, '--lang=smt2'],
                'cvc5_split': [args.cvc5, '--lang=smt2', '--ff-solver=split']}
    report = dict(platform=platform.platform(), repeat=args.repeat,
                  versions={k: dict(command=v, sha256=hashlib.sha256(Path(v[0]).read_bytes()).hexdigest())
                            for k, v in commands.items()}, cases=[], solver_only=[])
    for name, constraints, expected in cases():
        s = SimpleSolver()
        s.add(*constraints)
        text = '(set-logic ALL)\n' + s.sexpr()
        row = dict(case=name, expected=str(expected), input=text, results={})
        for label, cmd in commands.items():
            # Poseidon sentinels compare the same Z3 paths before/after; the
            # earlier combination report already records cvc5's timeouts there.
            if 'poseidon' in name and label.startswith('cvc5'):
                continue
            check = '(check-sat-using smt)' if label.endswith('_smt') else '(check-sat)'
            suffix = '' if label.startswith('cvc5') else '\n(get-info :all-statistics)'
            runs = [run_once(cmd, text + check + suffix, 10) for _ in range(args.repeat)]
            for r in runs:
                assert r['result'] == str(expected), (name, label, r)
                r.pop('stdout')
            row['results'][label] = runs
        if expected == sat:
            assert s.check() == sat
            assert all(is_true(s.model().eval(c, model_completion=True)) for c in constraints)
            row['model_validated'] = True
        # Retain a digest instead of duplicating large circuit inputs in JSON;
        # their generator and parameters are checked into this directory.
        row['input_sha256'] = hashlib.sha256(row.pop('input').encode()).hexdigest()
        report['cases'].append(row)
        args.out.write_text(json.dumps(report, indent=2)+'\n')
        print(name, {k: round(statistics.median(x['seconds'] for x in v)*1000, 3)
                     for k, v in row['results'].items()}, flush=True)
    for field, p in FIELDS.items():
        F = FiniteFieldSort(p)
        x, y = Consts('profile_x profile_y', F)
        f = Function('profile_f', F, IntSort())
        one, minus = FiniteFieldVal(1, F), FiniteFieldVal(p-1, F)
        queries = [('quadratic_pure', [x*x == 1], sat),
                   ('quadratic_mixed', [x*x == 1, f(x) != f(one), f(x) != f(minus)], unsat),
                   ('quartic_mixed', [y == x*x, x*x*x*x == 1, f(y) != f(one), f(y) != f(minus)], unsat)]
        for name, cs, expected in queries:
            for split in [False, True]:
                times = []
                for _ in range(11):
                    s = Tactic('ff-solve').solver() if name.endswith('pure') else SimpleSolver()
                    if not name.endswith('pure'):
                        s.set('ff.root_split', split)
                    s.add(*cs)
                    start = perf_counter()
                    assert s.check() == expected
                    times.append(perf_counter()-start)
                report['solver_only'].append(dict(field=field, case=name, root_split=split,
                                                   seconds=times, median_seconds=statistics.median(times)))
                if name.endswith('pure'):
                    break
    args.out.write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
