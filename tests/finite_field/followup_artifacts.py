#!/usr/bin/env python3
"""Deterministic, stratified isolated repetitions and longer-budget hard-case replays.

This never overwrites primary measurements. Selections and all follow-up runs
are recorded, including unsuccessful reruns. A sample does not stand in for the
complete corpus; it diagnoses timing stability and timeout sensitivity.
"""
import argparse
import collections
import concurrent.futures
import json
import statistics
from pathlib import Path
from artifact_analysis import LABELS, SOLVED, family, load
from benchmark_artifacts import prepare, run


def select(members, results, mode, limit):
    groups = collections.defaultdict(list)
    named = sorted(h for h, es in members.items() if mode=='hard' and any('/SMTHash' in e['member'] for e in es))
    for h, es in members.items():
        if h in named: continue
        a = results[h]
        assert len(a) == 3, 'complete the primary comparison first'
        ok = {k for k in LABELS if a[k]['result'] in SOLVED}
        if mode == 'isolated':
            if len(ok) != 3: continue
            slow = max(r['seconds'] for r in a.values())
            bucket = 0 if slow < .05 else 1 if slow < .5 else 2 if slow < 5 else 3
        else:
            if ok == set(LABELS): continue
            if ok == {'z3'}: bucket = 'Z3-only'
            elif 'z3' not in ok and ok: bucket = 'Z3-loses'
            elif not ok: bucket = 'none-solved'
            else: bucket = 'mixed-outcome'
        groups[(family(es), str(bucket))].append(h)
    # Hash order is stable and independent of manually inspected outcomes.
    groups = {g: sorted(hs) for g,hs in sorted(groups.items())}
    chosen=[dict(sha256=h, stratum=['QED2','Named Poseidon/MiMC hash circuit']) for h in named[:limit]]
    while len(chosen) < limit and any(groups.values()):
        for group, hashes in groups.items():
            if hashes and len(chosen) < limit: chosen.append(dict(sha256=hashes.pop(0), stratum=list(group)))
    return chosen


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--results', type=Path, required=True)
    ap.add_argument('--corpus', type=Path, required=True)
    ap.add_argument('--mode', choices=['isolated','hard'], required=True)
    ap.add_argument('--limit', type=int)
    ap.add_argument('--jobs', type=int)
    args = ap.parse_args()
    _, members, primary = load(args.results)
    limit = args.limit or (64 if args.mode=='isolated' else 24)
    jobs = args.jobs or (1 if args.mode=='isolated' else 4)
    assert args.mode != 'isolated' or jobs == 1
    timeout = 10 if args.mode=='isolated' else 60
    repeats = 3 if args.mode=='isolated' else 1
    chosen = select(members, primary, args.mode, limit)
    selection = dict(mode=args.mode, timeout=timeout, jobs=jobs, repeats=repeats, memory_mib=4096,
                     selection='hard mode first includes all four named SMTHash circuits; remaining slots use round-robin family/outcome or family/runtime strata, then ascending input hash', cases=chosen)
    (args.results/(args.mode+'-selection.json')).write_text(json.dumps(selection,indent=2)+'\n')
    output = args.results/(args.mode+'.jsonl')
    done = {(r['sha256'],r['solver'],r['repetition']) for r in map(json.loads,output.read_text().splitlines())} if output.exists() else set()
    commands = {'z3': [str((args.results/'binaries/z3').resolve()), '-in'],
                'cvc5': [str((args.results/'binaries/cvc5').resolve()), '--lang=smt2'],
                'cvc5_split': [str((args.results/'binaries/cvc5').resolve()), '--lang=smt2','--ff-solver=split']}
    tasks=[]
    for i,c in enumerate(chosen):
        for rep in range(repeats):
            labels=LABELS[(i+rep)%3:]+LABELS[:(i+rep)%3]
            tasks.extend((c['sha256'], label, rep) for label in labels if (c['sha256'],label,rep) not in done)

    def task(t):
        h,label,rep=t
        original=(args.corpus/'inputs'/(h+'.smt2')).read_text()
        cmd=list(commands[label]);checks=members[h][0]['checks']
        if checks>1 and label!='z3':cmd.append('--incremental')
        row=run(dict(command=cmd,smt=prepare(original),timeout=timeout,checks=checks,memory_mib=4096))
        row.update(sha256=h,solver=label,repetition=rep)
        if row['result'] in SOLVED:row.pop('stdout')
        return row

    print(args.mode,len(chosen),'inputs',len(tasks),'runs',flush=True)
    with output.open('a',buffering=1) as f, concurrent.futures.ThreadPoolExecutor(jobs) as pool:
        for i,row in enumerate(pool.map(task,tasks)):
            f.write(json.dumps(row)+'\n')
            if i%30==0:print(i+1,'/',len(tasks),row['solver'],row['result'],flush=True)
    print('completed',flush=True)


if __name__=='__main__':main()
