#!/usr/bin/env python3
"""Retrieve models separately and evaluate every original assertion in Python."""
import argparse
import concurrent.futures
import json
from pathlib import Path
from benchmark_artifacts import run
from benchmark_ff_optimizations import configure
from benchmark_public_ff import sexprs
from validate_artifact_models import validate


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('results', type=Path)
    ap.add_argument('--jobs', type=int, default=4)
    args = ap.parse_args()
    configs = json.loads((args.results/'metadata.json').read_text())['configs']
    rows = [json.loads(line) for line in (args.results/'runs.jsonl').read_text().splitlines()]
    targets = [r for r in rows if r['result'] == 'sat']
    def check(row):
        original = Path(row['path']).read_text()
        cfg = configs[row['variant']]
        commands = sexprs(original)
        names = [c[1] for c in commands if c[0] == 'declare-const' or
                 (c[0] == 'declare-fun' and c[2] == [])]
        smt = '(set-option :produce-models true)\n'+configure(original, cfg)
        if names: smt += '\n(get-value ('+' '.join(names)+'))\n'
        result = run(dict(command=[cfg['binary'], '-in'], smt=smt, checks=1,
                          timeout=30, output_limit=None, memory_mib=4096))
        out = dict(case=row['case'], variant=row['variant'], result=result['result'])
        try:
            assert result['result'] == 'sat', result
            out['assertions'] = validate(original, result['stdout'])
            out['validation'] = 'valid'
        except Exception as error:
            out.update(validation='failed', detail=repr(error), model=result['stdout'])
        return out
    with (args.results/'models.jsonl').open('w') as output, concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        results = list(pool.map(check, targets))
        for row in results: output.write(json.dumps(row)+'\n')
    failures = [r for r in results if r['validation'] != 'valid']
    print(len(results), 'SAT models checked;', len(failures), 'failures')
    for row in failures: print(row)
    assert not failures


if __name__ == '__main__':
    main()
