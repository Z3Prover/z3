#!/usr/bin/env python3
"""Paired finite-field optimization experiments on a preselected manifest.

Keep short exploratory screens separate from the final 10-second comparison.
The configurations file specifies binaries, parameters and optional tactic
routing; all original assertions are preserved in every experiment.
Infrastructure failures remain in the journal, invalidate the timing run, and
require a fresh output directory instead of silently appending duplicate retries.
"""
import argparse
import concurrent.futures
import hashlib
import json
import platform
import random
import re
from pathlib import Path
from benchmark_artifacts import run, prepare, infrastructure_error


def configure(smt, cfg):
    smt = prepare(smt, solver='z3' if cfg.get('normalize_incremental') else None)
    # Preserve the default portfolio for parameter-only ablations. The older
    # params/route interface deliberately builds an explicit tactic pipeline.
    smt = ''.join(f'(set-option :{key} {str(value).lower()})\n'
                  for key, value in cfg.get('global_params', {}).items()) + smt
    if not cfg.get('params') and not cfg.get('route'):
        return smt
    opts = ' '.join(':'+k+' '+str(v).lower() for k, v in cfg.get('params', {}).items())
    def tactic(name): return f'(using-params {name} {opts})' if opts else name
    strategies = [tactic('ff-solve'), tactic('ff-sat')]
    route = cfg.get('route', 'default')
    if route == 'native': strategies += ['smt']
    elif route == 'direct-native': strategies = ['smt']
    elif route == 'default': strategies += ['(then ff2bv qfbv)', 'smt']
    elif route != 'algebra': raise ValueError(route)
    strategy = '(then ff-simplify (or-else '+' '.join(strategies)+'))' if len(strategies)>1 else '(then ff-simplify '+strategies[0]+')'
    assert len(re.findall(r'\(check-sat\s*\)', smt)) == 1
    return re.sub(r'\(check-sat\s*\)', '(check-sat-using '+strategy+')', smt)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--manifest', type=Path, required=True)
    ap.add_argument('--configs', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--timeout', type=float, default=10)
    ap.add_argument('--jobs', type=int, default=4)
    args = ap.parse_args()
    entries = json.loads(args.manifest.read_text());configs=json.loads(args.configs.read_text())
    args.out.mkdir(parents=True,exist_ok=True)
    metadata = dict(timeout=args.timeout, jobs=args.jobs, memory_mib=4096, platform=platform.platform(),
                    configs={k: dict(v, binary_sha256=hashlib.sha256(Path(v['binary']).read_bytes()).hexdigest()) for k,v in configs.items()})
    meta=args.out/'metadata.json'
    if meta.exists(): assert json.loads(meta.read_text())==metadata
    else: meta.write_text(json.dumps(metadata,indent=2)+'\n')
    (args.out/'selection.json').write_text(json.dumps(entries,indent=2)+'\n')
    output=args.out/'runs.jsonl'
    previous=list(map(json.loads,output.read_text().splitlines())) if output.exists() else []
    if any(r['result']=='infrastructure_error' for r in previous):
        raise SystemExit('Infrastructure errors are preserved in runs.jsonl. Use a new output directory for a clean rerun; automatic retry would double-count rows.')
    done={(r['case'],r['variant']) for r in previous}
    tasks=[]
    for i,e in enumerate(entries):
        labels=list(configs);off=i%len(labels);labels=labels[off:]+labels[:off]
        tasks += [(e,k) for k in labels if (e['case'],k) not in done]
    def task(pair):
        e,label=pair;cfg=configs[label]
        try:
            source=Path(e['path']).read_text();smt=configure(source,cfg)
            checks=e.get('checks', len(re.findall(r'\(check-sat(?:-using)?(?:\s|\))', smt)))
            row=run(dict(command=[cfg['binary'],'-in'],smt=smt,timeout=args.timeout,checks=checks,memory_mib=4096))
            row.update(source_sha256=hashlib.sha256(source.encode()).hexdigest(),input_sha256=hashlib.sha256(smt.encode()).hexdigest())
        except Exception as exc:
            # Record per-case infrastructure failures and keep draining futures;
            # one bad worker must not abort journaling while queued work runs.
            row=infrastructure_error('case_setup', f'{type(exc).__name__}: {exc}')
        row.update(e,variant=label)
        return row
    failed=0
    with output.open('a',buffering=1) as f,concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        futures=[pool.submit(task,t) for t in tasks]
        for i,future in enumerate(concurrent.futures.as_completed(futures)):
            row=future.result();f.write(json.dumps(row)+'\n')
            failed += row['result']=='infrastructure_error'
            if i%20==0: print(i+1,'/',len(tasks),row['family'],row['variant'],row['result'],flush=True)
    if failed:
        raise SystemExit(f'{failed} infrastructure errors recorded; this is not a clean timing run. Use a new output directory to rerun.')


if __name__=='__main__': main()
