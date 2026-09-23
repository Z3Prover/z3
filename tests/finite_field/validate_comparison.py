#!/usr/bin/env python3
"""Parallel, untimed original-assertion model checks for a frozen comparison.

Validation is separate from benchmark timing. Reuse only identical Z3 binary
and input witnesses; retrieve and independently evaluate every new cvc5 SAT
model. Incremental multi-answer inputs are checked separately in smoke tests.
"""
import argparse
import collections
import concurrent.futures
import hashlib
import json
from pathlib import Path
from benchmark_artifacts import prepare, run
from benchmark_public_ff import sexprs
from validate_artifact_models import validate


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--results', type=Path, required=True)
    ap.add_argument('--corpus', type=Path, required=True)
    ap.add_argument('--jobs', type=int, default=4)
    args = ap.parse_args()
    root = Path(__file__).resolve().parents[2]
    path = args.results / 'models.jsonl'
    rows = [json.loads(l) for l in (args.results / 'runs.jsonl').read_text().splitlines()]
    targets = {(r['sha256'], r['solver']): r for r in rows if r['result'] == 'sat'}
    if not path.exists():
        old = root / 'tests/finite_field/results/cav-overview'
        metadata = json.loads((args.results / 'metadata.json').read_text())
        same = metadata['binaries']['z3']['sha256'] == json.loads((old / 'metadata.json').read_text())['binary_sha256']
        with path.open('w') as f:
            if same:
                for line in (old / 'models.jsonl').read_text().splitlines():
                    r = json.loads(line)
                    if (r['sha256'], 'z3') in targets and r['validation'] == 'valid':
                        r.update(source='same-binary original-assertion witness from cav-overview')
                        f.write(json.dumps(r)+'\n')
    done = {(r['sha256'], r['solver']) for r in map(json.loads, path.read_text().splitlines())}
    commands = {'z3': [str((args.results/'binaries/z3').resolve()), '-in'],
                'cvc5': [str((args.results/'binaries/cvc5').resolve()), '--lang=smt2'],
                'cvc5_split': [str((args.results/'binaries/cvc5').resolve()), '--lang=smt2', '--ff-solver=split']}

    def check(key):
        h, label = key
        original = (args.corpus / 'inputs' / (h+'.smt2')).read_text()
        assert hashlib.sha256(original.encode()).hexdigest() == h
        normalized = prepare(original, solver=label)
        assert hashlib.sha256(normalized.encode()).hexdigest() == targets[key]['input_sha256']
        names = [c[1] for c in sexprs(original) if c[0] == 'declare-const' or (c[0] == 'declare-fun' and c[2] == [])]
        smt = '(set-option :produce-models true)\n' + normalized
        if names:
            smt += '\n(get-value ('+' '.join(names)+'))\n'
        result = run(dict(command=commands[label], smt=smt, timeout=30, checks=1, memory_mib=4096, output_limit=None))
        row = dict(sha256=h, solver=label, model_result=result['result'])
        try:
            assert result['result'] == 'sat', result['result']
            row.update(validation='valid', assertions=validate(original, result['stdout']))
        except Exception as error:
            row.update(validation='failed', detail=repr(error), replay=result)
        return row

    todo = sorted(set(targets)-done)
    print(len(done), 'reused;', len(todo), 'new SAT model checks', flush=True)
    with path.open('a', buffering=1) as f, concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        for i, row in enumerate(pool.map(check, todo), 1):
            f.write(json.dumps(row)+'\n')
            if i % 100 == 0 or row['validation'] != 'valid':
                print(i, '/', len(todo), row['validation'], flush=True)
    checked = [json.loads(l) for l in path.read_text().splitlines()]
    assert len(checked) == len(targets)
    counts = collections.Counter(r['validation'] for r in checked)
    print(dict(counts), flush=True)
    assert counts.get('failed', 0) == 0


if __name__ == '__main__':
    main()
