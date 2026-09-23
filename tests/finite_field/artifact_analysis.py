#!/usr/bin/env python3
"""Coverage, family and correctness summaries for the full artifact comparison."""
import argparse
import collections
import csv
import json
import math
import statistics
from pathlib import Path

LABELS = ['z3', 'cvc5', 'cvc5_split']
SOLVED = {'sat', 'unsat', 'multi'}


def family(entries):
    experiment = [e for e in entries if e['family'] != 'Examples' and e['paper'] != 'FMCAD26']
    if not experiment: return 'Examples'
    c24 = [e for e in experiment if e['paper'] == 'CAV24']
    if c24: return c24[0]['family']
    return 'TV-pureFF' if '-pureff' in experiment[0]['family'] else 'TV'


def load(path):
    manifest = json.loads((path/'manifest.json').read_text())
    members = collections.defaultdict(list)
    for e in manifest['entries']: members[e['sha256']].append(e)
    runs = collections.defaultdict(dict)
    for line in (path/'runs.jsonl').read_text().splitlines():
        row = json.loads(line)
        assert row['solver'] not in runs[row['sha256']], 'duplicate measured run'
        runs[row['sha256']][row['solver']] = row
    adjudications=path/'adjudications.json'
    if adjudications.exists():
        for h, decision in json.loads(adjudications.read_text()).items():
            for label in decision['wrong_solvers']:
                row=runs[h][label]
                row['reported_result']=row['result'];row['result']='wrong'
    return manifest, members, runs


def summarize(path, allow_partial=False):
    manifest, members, runs = load(path)
    expected = len(members)*len(LABELS)
    completed = sum(map(len, runs.values()))
    if not allow_partial: assert completed == expected, (completed, expected)
    timeout = json.loads((path/'metadata.json').read_text())['timeout']
    disagreements, status_mismatches, proof_subset_mismatches, wrong_answers = [], [], [], []
    for h, answers in runs.items():
        wrong_answers.extend(dict(sha256=h,solver=label,reported_result=r['reported_result']) for label,r in answers.items() if r['result']=='wrong')
        definite = {tuple(r['answers']) for r in answers.values() if r['result'] in SOLVED}
        if len(definite) > 1: disagreements.append(h)
        expected_status = {e['declared_status'] for e in members[h]} & {'sat','unsat'}
        if expected_status and any(r['result'] in {'sat','unsat'} and r['result'] not in expected_status for r in answers.values()): status_mismatches.append(h)
        if any('benchmark_set_FF_UNSAT_SMT' in e['paper_sets'] for e in members[h]) and any(r['result']=='sat' for r in answers.values()):
            proof_subset_mismatches.append(h)

    def table(hashes):
        result = {'n': len(hashes)}
        for label in LABELS:
            rows = [runs[h][label] for h in hashes if label in runs[h]]
            counts = collections.Counter(r['result'] for r in rows)
            result[label] = dict(counts=counts, solved=sum(counts[s] for s in SOLVED),
                par2_mean=statistics.mean(r['seconds'] if r['result'] in SOLVED else 2*timeout for r in rows) if rows else None,
                peak_rss_mib=max((r['peak_rss_mib'] for r in rows), default=0))
        return result

    groups = collections.defaultdict(set)
    for h, entries in members.items(): groups[family(entries)].add(h)
    paper_groups = {p: {h for h, es in members.items() if any(e['paper'] == p for e in es)} for p in manifest['sources']}
    paper_groups['CAV23-main'] = {h for h, es in members.items() if any('CAV23-full-runs' in e['paper_sets'] for e in es)}
    main_sets = {'benchmark_set_general','benchmark_set_circ_deterministic'}
    paper_groups['CAV24-main'] = {h for h, es in members.items() if any(e['paper']=='CAV24' and main_sets.intersection(e['paper_sets']) for e in es)}
    paper_groups['FMCAD26-UNSAT'] = {h for h, es in members.items() if any(e['paper']=='FMCAD26' and 'benchmark_set_FF_UNSAT_SMT' in e['paper_sets'] for e in es)}
    field_groups = {'small (<=16 bits)':set(), 'medium (17-127 bits)':set(), 'large (>=128 bits)':set()}
    for h, es in members.items():
        bits=max(es[0]['field_bits'])
        field_groups['small (<=16 bits)' if bits<=16 else 'medium (17-127 bits)' if bits<128 else 'large (>=128 bits)'].add(h)
    pairwise = {}
    for ref in LABELS[1:]:
        complete = [a for a in runs.values() if 'z3' in a and ref in a]
        both = [a for a in complete if a['z3']['result'] in SOLVED and a[ref]['result'] in SOLVED]
        pairwise[ref] = dict(both=len(both),
            z3_only=sum(a['z3']['result'] in SOLVED and a[ref]['result'] not in SOLVED for a in complete),
            reference_only=sum(a['z3']['result'] not in SOLVED and a[ref]['result'] in SOLVED for a in complete),
            neither=sum(a['z3']['result'] not in SOLVED and a[ref]['result'] not in SOLVED for a in complete),
            geomean_reference_over_z3=math.exp(statistics.mean(math.log(a[ref]['seconds']/a['z3']['seconds']) for a in both)) if both else None)
    result = dict(expected_runs=expected, completed_runs=completed, unique_inputs=len(members),
                  artifact_members=len(manifest['entries']),
                  excluded_alternate_encodings=len(manifest['excluded_non_field']),
                  total=table(set(members)), families={k: table(v) for k,v in sorted(groups.items())},
                  papers={k:table(v) for k,v in paper_groups.items()}, pairwise=pairwise,
                  field_sizes={k:table(v) for k,v in field_groups.items()},
                  disagreements=disagreements, declared_status_mismatches=status_mismatches,
                  proof_paper_unsat_subset_mismatches=proof_subset_mismatches)
    result['confirmed_wrong_answers']=wrong_answers
    models = path/'models.jsonl'
    if models.exists():
        m = [json.loads(l) for l in models.read_text().splitlines()]
        result['models'] = collections.Counter(r['validation'] for r in m)
        result['sat_runs'] = sum(r['result']=='sat' for a in runs.values() for r in a.values())
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('results', type=Path)
    ap.add_argument('--partial', action='store_true')
    args = ap.parse_args()
    result = summarize(args.results, args.partial)
    (args.results/'summary.json').write_text(json.dumps(result, indent=2)+'\n')
    _, members, runs = load(args.results)
    with (args.results/'cases.csv').open('w') as f:
        writer = csv.writer(f)
        writer.writerow(['sha256','family','papers','representative_member','solver','result','reported_result','seconds','cpu_seconds','peak_rss_mib'])
        for h in sorted(runs):
            for label, r in runs[h].items():
                writer.writerow([h, family(members[h]), ';'.join(sorted({e['paper'] for e in members[h]})),
                                 members[h][0]['member'],label,r['result'],r.get('reported_result',r['result']),r['seconds'],r['cpu_seconds'],r['peak_rss_mib']])
    print(json.dumps(result, indent=2))


if __name__ == '__main__': main()
