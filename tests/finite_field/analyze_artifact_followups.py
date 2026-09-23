#!/usr/bin/env python3
"""Audit separate hard-case and isolated replays without changing primary scores."""
import argparse
import collections
import json
import math
import statistics
from pathlib import Path
from artifact_analysis import LABELS, SOLVED, family, load


def analyze(path):
    _, members, primary = load(path)
    decisions = json.loads((path/'adjudications.json').read_text()) if (path/'adjudications.json').exists() else {}
    out = {'contradictions': [], 'hard': {}, 'isolated': {}}
    for mode in ('hard', 'isolated'):
        selection = json.loads((path/(mode+'-selection.json')).read_text())
        rows = [json.loads(l) for l in (path/(mode+'.jsonl')).read_text().splitlines()]
        keys = {(r['sha256'], r['solver'], r['repetition']) for r in rows}
        expected = {(c['sha256'], label, rep) for c in selection['cases']
                    for label in LABELS for rep in range(selection['repeats'])}
        assert len(rows) == len(keys) and keys == expected, 'incomplete/duplicate follow-up runs'
        grouped = collections.defaultdict(lambda: collections.defaultdict(list))
        for row in rows:
            h, label = row['sha256'], row['solver']
            if h in decisions and label in decisions[h]['wrong_solvers'] and row['result'] in SOLVED:
                if row['result'] != decisions[h]['expected']:
                    row['reported_result'], row['result'] = row['result'], 'wrong'
            grouped[h][label].append(row)
            previous = {tuple(r['answers']) for r in primary[h].values() if r['result'] in SOLVED}
            if row['result'] in SOLVED and previous and tuple(row['answers']) not in previous:
                out['contradictions'].append(dict(mode=mode, sha256=h, solver=label,
                                                  answers=row['answers'], primary=list(previous)))
        for h, a in grouped.items():
            definite = {tuple(r['answers']) for rs in a.values() for r in rs if r['result'] in SOLVED}
            if len(definite) > 1:
                out['contradictions'].append(dict(mode=mode, sha256=h, answers=list(definite)))
        data = out[mode]
        data['inputs'], data['runs'] = len(grouped), len(rows)
        data['families'] = dict(collections.Counter(family(members[h]) for h in grouped))
        data['counts'] = {label: dict(collections.Counter(r['result'] for r in rows if r['solver']==label)) for label in LABELS}
        if mode == 'hard':
            data['changes'] = {}
            for label in LABELS:
                data['changes'][label] = dict(
                    newly_solved=[h for h, a in grouped.items() if a[label][0]['result'] in SOLVED and primary[h][label]['result'] not in SOLVED],
                    no_longer_solved=[h for h, a in grouped.items() if a[label][0]['result'] not in SOLVED and primary[h][label]['result'] in SOLVED])
            data['cases'] = [dict(sha256=h, family=family(members[h]),
                member=members[h][0]['member'],
                primary={k: {s: primary[h][k][s] for s in ('result','seconds','peak_rss_mib')} for k in LABELS},
                replay={k: {s: a[k][0][s] for s in ('result','seconds','peak_rss_mib')} for k in LABELS}) for h,a in grouped.items()]
        else:
            medians = {h: {k: statistics.median(r['seconds'] for r in rs) for k,rs in a.items()
                           if all(r['result'] in SOLVED for r in rs)} for h,a in grouped.items()}
            data['pairwise'] = {}
            for ref in LABELS[1:]:
                pairs = [a for a in medians.values() if 'z3' in a and ref in a]
                data['pairwise'][ref] = dict(mutually_solved_all_repetitions=len(pairs),
                    geomean_reference_over_z3=math.exp(statistics.mean(math.log(a[ref]/a['z3']) for a in pairs)),
                    z3_faster=sum(a['z3'] < a[ref] for a in pairs))
            data['repetition_spread'] = {}
            for label in LABELS:
                spreads = sorted(max(r['seconds'] for r in a[label])/min(r['seconds'] for r in a[label])
                                 for a in grouped.values() if all(r['result'] in SOLVED for r in a[label]))
                data['repetition_spread'][label] = dict(median_max_over_min=statistics.median(spreads),
                    p90_max_over_min=spreads[math.ceil(.9*len(spreads))-1], max_max_over_min=max(spreads))
    for log in ('models.jsonl','models-hard.jsonl'):
        checks = [json.loads(l) for l in (path/log).read_text().splitlines()]
        source_log = 'runs.jsonl' if log == 'models.jsonl' else 'hard.jsonl'
        expected = {(r['sha256'],r['solver']) for r in map(json.loads,(path/source_log).read_text().splitlines()) if r['result']=='sat'}
        actual = {(r['sha256'],r['solver']) for r in checks}
        assert len(checks) == len(actual) and expected == actual, 'incomplete/duplicate SAT-model checks'
        out[log] = dict(counts=dict(collections.Counter(r['validation'] for r in checks)),
                        per_solver={k: dict(collections.Counter(r['validation'] for r in checks if r['solver']==k)) for k in LABELS},
                        failed=[r for r in checks if r['validation'] != 'valid'])
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('results', type=Path)
    args = ap.parse_args()
    result = analyze(args.results)
    (args.results/'followup-summary.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))
    assert not result['contradictions'], 'follow-up answers need investigation'


if __name__ == '__main__': main()
