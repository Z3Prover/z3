#!/usr/bin/env python3
"""Run circuit scaling cases in isolated workers; retain failures and validate SAT models.

RSS is measured per solver process, never the cumulative maximum of the suite.
Model validation is a separate, untimed solver invocation. Generated inputs and
binary hashes make before/after comparisons reproducible.
"""
import argparse
import hashlib
import json
import platform
import re
import resource
import statistics
import subprocess
import sys
import time
from pathlib import Path
from zk_circuits import cases, poseidon_case, PARAMETERS, permutation_reference


def worker(config):
    cmd = config['command']
    start = time.perf_counter()
    result, stdout, stderr = 'error', '', ''
    try:
        run = subprocess.run(cmd, input=config['smt'], text=True, capture_output=True, timeout=config['timeout'])
        stdout, stderr = run.stdout, run.stderr
        answers = re.findall(r'^(sat|unsat|unknown)$', stdout, re.M)
        if run.returncode == 0 and '(error' not in stdout and answers:
            result = answers[0]
    except subprocess.TimeoutExpired as e:
        result = 'timeout'
        stdout = e.stdout or b''; stderr = e.stderr or b''
        if isinstance(stdout, bytes): stdout = stdout.decode(errors='replace')
        if isinstance(stderr, bytes): stderr = stderr.decode(errors='replace')
    elapsed = time.perf_counter() - start
    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
    # Darwin reports bytes; Linux reports KiB.
    peak = usage.ru_maxrss / (1024**2 if sys.platform == 'darwin' else 1024)
    counters = {k: float(v) for k, v in re.findall(r':(ff-[a-z-]+)\s+([0-9.]+)', stdout)}
    return dict(result=result, seconds=elapsed, peak_rss_mib=peak,
                cpu_seconds=usage.ru_utime+usage.ru_stime, statistics=counters,
                stdout=stdout, stderr=stderr)


def run_once(command, smt, timeout):
    config = dict(command=command, smt=smt, timeout=timeout)
    output = subprocess.check_output([sys.executable, __file__, '--worker'], input=json.dumps(config), text=True)
    return json.loads(output)


def returned_assignment(output, circuit):
    values = {int(i): int(a or b) % circuit.p for i, a, b in re.findall(
        r'\(w(\d+)\s+(?:\(as\s+ff(-?\d+)\b|#f(-?\d+)m\d+)', output)}
    if set(values) != set(range(1, len(circuit.witness))):
        raise AssertionError(f'model has {len(values)} of {len(circuit.witness)-1} wires')
    return [1] + [values[i] for i in range(1, len(circuit.witness))]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--z3', default='build-ff-cmake/z3')
    ap.add_argument('--baseline')
    ap.add_argument('--simplify', action='store_true', help='also measure explicit ff-simplify preprocessing')
    ap.add_argument('--raw', action='store_true', help='also measure the field strategy without preprocessing')
    ap.add_argument('--cvc5', required=True)
    ap.add_argument('--only', default='', help='comma-separated solver labels')
    ap.add_argument('--filter', default='')
    ap.add_argument('--large', action='store_true')
    ap.add_argument('--symbolic-scaling', action='store_true', help='holdout: two/four chained symbolic Poseidon permutations')
    ap.add_argument('--repeat', type=int, default=3)
    ap.add_argument('--timeout', type=float, default=5)
    ap.add_argument('--out', type=Path, default=Path('tests/finite_field/results/zk.json'))
    ap.add_argument('--inputs', type=Path, default=Path('/private/tmp/ff-zk-inputs'))
    args = ap.parse_args()
    if args.repeat < 1 or args.timeout <= 0: ap.error('positive repeat and timeout required')
    commands = {'z3': [args.z3, '-in'],
                'cvc5': [args.cvc5, '--lang=smt2', f'--tlimit-per={int(args.timeout*1000)}'],
                'cvc5_split': [args.cvc5, '--lang=smt2', '--ff-solver=split', f'--tlimit-per={int(args.timeout*1000)}']}
    if args.baseline: commands['baseline'] = [args.baseline, '-in']
    if args.simplify: commands['z3_simplify'] = [args.z3, '-in']
    if args.raw: commands['z3_raw'] = [args.z3, '-in']
    if args.only: commands = {k:v for k,v in commands.items() if k in args.only.split(',')}
    assert commands, 'no selected solvers'
    for field, q in PARAMETERS.items():
        assert permutation_reference(field, q['vector_input']) == [int(v, 16) for v in q['vector_output']]
    versions = {label: dict(command=cmd, sha256=hashlib.sha256(Path(cmd[0]).read_bytes()).hexdigest(),
                           version=subprocess.check_output([cmd[0], '--version'], text=True).splitlines()[0])
                for label, cmd in commands.items()}
    report = dict(platform=platform.platform(), timeout_seconds=args.timeout, repeat=args.repeat,
                  reference_revision='055bde3f4782731ba5f5ce5888a440a94327eaf3',
                  model_validation='separate untimed run; every R1CS equation, pin and disequality',
                  versions=versions, cases=[])
    failed = False
    args.inputs.mkdir(parents=True, exist_ok=True); args.out.parent.mkdir(parents=True, exist_ok=True)
    suite = cases(args.large)
    if args.symbolic_scaling:
        suite = ((f'{field}_poseidon_{count}_{mode}', *poseidon_case(field, count, mode))
                 for field in PARAMETERS for count in [2,4] for mode in ['free','partial','equivalence'])
    report['suite'] = 'symbolic scaling holdout' if args.symbolic_scaling else 'reference circuit suite'
    for name, circuit, expected in suite:
        if args.filter and args.filter not in name: continue
        assert circuit.valid(circuit.witness) == (expected == 'sat'), name
        smt = circuit.smt(); (args.inputs / f'{name}.smt2').write_text(smt+'(check-sat)\n')
        row = dict(case=name, expected=expected, wires=len(circuit.witness)-1,
                   constraints=len(circuit.constraints), input_sha256=hashlib.sha256(smt.encode()).hexdigest(), solvers={})
        for label, command in commands.items():
            z3 = label.startswith('z3') or label == 'baseline'
            header = f'(set-option :timeout {int(args.timeout*1000)})\n' if z3 else ''
            check = ('(check-sat-using (then ff-simplify (or-else ff-solve ff-sat (then ff2bv qfbv))))\n'
                     if label == 'z3_simplify' else '(check-sat)\n')
            if label == 'z3_raw': check = '(check-sat-using (or-else ff-solve ff-sat (then ff2bv qfbv)))\n'
            suffix = check + ('(get-info :all-statistics)\n' if z3 else '')
            runs = []
            for _ in range(args.repeat):
                record = run_once(command, header+smt+suffix, args.timeout+2)
                if record['result'] != 'error':
                    record.pop('stdout'); record.pop('stderr')
                runs.append(record)
                if record['result'] != expected: break
            summary = dict(result=runs[-1]['result'], seconds=statistics.median(r['seconds'] for r in runs),
                           peak_rss_mib=max(r['peak_rss_mib'] for r in runs), runs=runs)
            if summary['result'] == 'sat':
                queries = '(get-value ('+' '.join(f'w{i}' for i in range(1,len(circuit.witness)))+'))\n'
                model = run_once(command, header+'(set-option :produce-models true)\n'+smt+check+queries, args.timeout+2)
                if model['result'] == 'sat':
                    assignment = returned_assignment(model['stdout'], circuit)
                    assert circuit.valid(assignment), (name, label, 'invalid model')
                    summary['model_validated'] = True
                else:
                    summary['model_validated'] = False
                    summary['model_run_result'] = model['result']
                    failed = True
            if summary['result'] in ['sat','unsat'] and summary['result'] != expected:
                raise AssertionError((name, label, summary))
            failed |= summary['result'] == 'error'
            row['solvers'][label] = summary
        report['cases'].append(row)
        args.out.write_text(json.dumps(report, indent=2)+'\n')
        print(name, json.dumps({k:{q:v[q] for q in ['result','seconds','peak_rss_mib']} for k,v in row['solvers'].items()}), flush=True)
    print(f"{len(report['cases'])} cases recorded; errors or missing SAT validation: {failed}")
    return int(failed)


if __name__ == '__main__':
    if '--worker' in sys.argv: print(json.dumps(worker(json.load(sys.stdin))))
    else: sys.exit(main())
