#!/usr/bin/env python3
"""Summarize paired runs without interpreting timeouts as satisfiability answers."""
import argparse
import collections
import json
from pathlib import Path


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('results', type=Path)
    args = ap.parse_args()
    rows = [json.loads(line) for line in (args.results/'runs.jsonl').read_text().splitlines()]
    variants = list(json.loads((args.results/'metadata.json').read_text())['configs'])
    by_case = collections.defaultdict(dict)
    counts = collections.defaultdict(collections.Counter)
    for row in rows:
        by_case[row['case']][row['variant']] = row
        counts[row['family'], row['variant']][row['result']] += 1
    solved = lambda row: row['result'] in ('sat', 'unsat', 'multi')
    contradictions = []
    gains = {v: [] for v in variants if v != 'baseline'}
    losses = {v: [] for v in gains}
    for case, group in by_case.items():
        if len({tuple(r['answers']) for r in group.values() if solved(r)}) > 1:
            contradictions.append(case)
        baseline = group.get('baseline')
        if not baseline:
            continue
        for variant in gains:
            if variant not in group:
                continue
            row = group[variant]
            record = dict(case=case, family=row['family'], name=row['name'],
                          baseline=baseline['result'], result=row['result'],
                          baseline_seconds=baseline['seconds'], seconds=row['seconds'])
            if solved(row) and not solved(baseline): gains[variant].append(record)
            if solved(baseline) and not solved(row): losses[variant].append(record)
    summary = dict(runs=len(rows), cases=len(by_case), variants=variants,
                   complete_pairs=sum(len(g) == len(variants) for g in by_case.values()),
                   counts=[dict(family=f, variant=v, **c) for (f,v),c in sorted(counts.items())],
                   gains=gains, losses=losses, contradictions=contradictions)
    (args.results/'summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    print('runs', len(rows), 'complete cases', summary['complete_pairs'])
    for family in sorted({f for f, v in counts}):
        print(family, {v: sum(counts[family,v][s] for s in ('sat','unsat','multi')) for v in variants})
    print('gains', {v: len(g) for v,g in gains.items()})
    print('losses', {v: len(g) for v,g in losses.items()})
    print('contradictions', contradictions)


if __name__ == '__main__':
    main()
