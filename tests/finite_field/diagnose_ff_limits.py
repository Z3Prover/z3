#!/usr/bin/env python3
"""Attribute bounded algebra failures without running the default fallback.

This is a diagnostic, not a competitive solver score. Configurations name
explicit ff-solve parameters, and all input assertions are preserved.
"""
import argparse
import concurrent.futures
import hashlib
import json
import re
from pathlib import Path
from benchmark_artifacts import infrastructure_error, prepare, run


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--manifest', type=Path, required=True)
    ap.add_argument('--binary', type=Path, required=True)
    ap.add_argument('--configs', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--timeout', type=float, default=3)
    ap.add_argument('--jobs', type=int, default=4)
    args = ap.parse_args()
    entries = json.loads(args.manifest.read_text())
    configs = json.loads(args.configs.read_text())
    args.out.mkdir(parents=True, exist_ok=True)
    journal = args.out / 'runs.jsonl'
    if journal.exists():
        raise SystemExit('Use a fresh output directory; diagnostic logs are never overwritten.')
    metadata = dict(binary=str(args.binary.resolve()), sha256=hashlib.sha256(args.binary.read_bytes()).hexdigest(),
                    configs=configs, timeout=args.timeout, jobs=args.jobs, route='ff-simplify then ff-solve',
                    peak_semantics='Per-engine storage estimates; wrappers can sum peaks across separate attempts.')
    (args.out / 'metadata.json').write_text(json.dumps(metadata, indent=2) + '\n')
    (args.out / 'selection.json').write_text(json.dumps(entries, indent=2) + '\n')

    def task(pair):
        entry, label = pair
        source = Path(entry['path']).read_text()
        smt = prepare(source, solver='z3')
        if len(re.findall(r'\(check-sat\s*\)', smt)) != 1:
            raise ValueError('diagnostic requires exactly one check-sat')
        opts = ' '.join(':' + k + ' ' + str(v).lower() for k, v in configs[label].items())
        tactic = '(using-params ff-solve ' + opts + ')' if opts else 'ff-solve'
        smt = re.sub(r'\(check-sat\s*\)', '(check-sat-using (then ff-simplify ' + tactic + '))', smt)
        smt = f'(set-option :timeout {max(1, int(args.timeout * 1000) - 200)})\n' + smt
        smt += '\n(get-info :reason-unknown)\n(get-info :all-statistics)\n'
        result = run(dict(command=[str(args.binary.resolve()), '-in'], smt=smt, timeout=args.timeout,
                          checks=1, memory_mib=4096, output_limit=None))
        result.update(entry, variant=label, source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                      input_sha256=hashlib.sha256(smt.encode()).hexdigest(),
                      stats={k: float(v) for k, v in re.findall(r':(ff-[a-z-]+)\s+([0-9.]+)', result['stdout'])})
        return result

    def supervised_task(pair):
        try:
            return task(pair)
        except Exception as error:
            entry, label = pair
            result = infrastructure_error('case_setup', f'{type(error).__name__}: {error}')
            result.update(entry, variant=label, stats={})
            return result

    failures = 0
    with journal.open('x', buffering=1) as output, concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        for result in pool.map(supervised_task, [(e, label) for e in entries for label in configs]):
            output.write(json.dumps(result) + '\n')
            failures += result['result'] == 'infrastructure_error'
            print(result['family'], result['variant'], result['result'], flush=True)
    if failures:
        raise SystemExit(f'{failures} infrastructure failures: not a clean diagnostic run')


if __name__ == '__main__':
    main()
