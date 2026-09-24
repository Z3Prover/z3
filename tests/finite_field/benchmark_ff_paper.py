#!/usr/bin/env python3
"""Same-input, versioned FMCAD solver/proof comparison (no Lean dependency).

Requires psutil. One fresh worker and process group per configuration/input.
The outer wall deadline covers production AND checking, including Python startup.
Outputs and per-stage receipts are retained; interrupted campaigns can resume.
"""
import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import random
import re
import signal
import subprocess
import sys
import time
import zipfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def stage(command, directory, name, receipt):
    out, err = directory / (name + '.stdout'), directory / (name + '.stderr')
    start = time.monotonic()
    receipt['active_stage'] = name
    (directory/'progress.json').write_text(json.dumps(receipt))
    with out.open('wb') as stdout, err.open('wb') as stderr:
        p = subprocess.Popen(command, stdout=stdout, stderr=stderr)
        code = p.wait()
    info = dict(command=command, seconds=time.monotonic()-start, returncode=code,
                stdout_bytes=out.stat().st_size, stderr_bytes=err.stat().st_size)
    receipt.setdefault('stages', {})[name] = info
    (directory/'progress.json').write_text(json.dumps(receipt))
    return code, out, err


def worker(job):
    import ff_proof_pipeline as pp
    directory = Path(job['directory']); config = job['configuration']
    source = Path(job['input']); receipt = dict(status='error', stages={})
    if config['kind'] == 'z3-proof':
        receipt['active_stage'] = 'produce'; (directory/'progress.json').write_text(json.dumps(receipt))
        text = source.read_text(); (directory/'problem.smt2').write_text(text)
        start = time.monotonic()
        pp.produce_bundle(text, directory, config['command'][0], job['timeout'])
        receipt['stages']['produce'] = dict(seconds=time.monotonic()-start)
        receipt['produced'] = True; receipt['generation_seconds'] = time.monotonic()-job['started_at']; receipt['active_stage'] = 'check'
        (directory/'progress.json').write_text(json.dumps(receipt))
        start = time.monotonic()
        pp.check_bundle(directory, job['carcara'], job['ffpacheck'], job['timeout'])
        receipt['stages']['check'] = dict(seconds=time.monotonic()-start)
        receipt.update(status='checked', check_contract='input-bound-independent+carcara+ffpacheck')
        return receipt
    code, stdout, stderr = stage(config['command']+[str(source)], directory, 'produce', receipt)
    if code:
        receipt.update(status='error', reason=stderr.read_text(errors='replace')[:2000]); return receipt
    text = stdout.read_text(errors='replace')
    answers = re.findall(r'^(sat|unsat|unknown)\s*$', text, re.M)
    if answers != ['unsat']:
        receipt.update(status=answers[0] if len(answers)==1 else 'error', reason=text[:2000]); return receipt
    if config['kind'] == 'solve':
        receipt['status'] = 'unsat'; return receipt
    receipt['produced'] = True
    receipt['generation_seconds'] = time.monotonic()-job['started_at']
    # cvc5 --dump-proofs emits its answer, followed by the Alethe proof.
    proof = text[text.index('unsat')+len('unsat'):].strip()
    if proof.startswith('(') and proof.endswith(')'):
        # Dumping wraps all proof commands in a single list. Only unwrap when
        # the next non-whitespace token is another opening parenthesis.
        if proof[1:].lstrip().startswith('('): proof = proof[1:-1].strip()
    (directory/'proof.alethe').write_text(proof+'\n')
    # Never count admitted/undefined rules as checked evidence.
    if re.search(r':rule\s+(hole|undefined)\b', proof):
        receipt.update(status='checker_rejected',reason='proof contains admitted/undefined rule'); return receipt
    command = [job['carcara'], 'check', str(directory/'proof.alethe'), str(source),
               '--expand-let-bindings', '--apply-function-defs', '--ff-pac-solver', job['ffpacheck']] + config.get('checker_args', [])
    code, stdout, stderr = stage(command, directory, 'check', receipt)
    receipt['status'] = 'checked' if code == 0 and stdout.read_text().strip() == 'valid' else 'checker_rejected'
    receipt['check_contract'] = 'carcara+ffpacheck (upstream PAC-premise binding limitation)'
    if receipt['status'] != 'checked': receipt['reason'] = (stdout.read_text()+stderr.read_text())[:2000]
    return receipt


def supervise(job):
    import psutil
    directory = Path(job['directory']); directory.mkdir(parents=True, exist_ok=True)
    for name in ['result.json', 'progress.json']:
        (directory/name).unlink(missing_ok=True)
    start = time.monotonic(); job = dict(job, started_at=start); peak = 0; limit = job['memory_mib'] * 1024**2
    with (directory/'worker.stdout').open('wb') as out, (directory/'worker.stderr').open('wb') as err:
        p = subprocess.Popen([sys.executable, str(Path(__file__).resolve()), '--worker'],
                             stdin=subprocess.PIPE, stdout=out, stderr=err, start_new_session=True)
        p.stdin.write(json.dumps(job).encode()); p.stdin.close()
        proc = psutil.Process(p.pid); stop = None; tracked = {}
        try:
            while p.poll() is None:
                elapsed = time.monotonic()-start
                members = [proc] + proc.children(recursive=True)
                for q in members[1:]: tracked[(q.pid, q.create_time())] = q
                rss = 0
                for q in members:
                    try: rss += q.memory_info().rss
                    except psutil.NoSuchProcess: pass
                peak = max(peak, rss)
                output_bytes = sum(f.stat().st_size for f in directory.glob('*.stdout'))
                if elapsed >= job['timeout']: stop = 'timeout'
                elif rss > limit: stop = 'memout'
                elif output_bytes > 256*1024**2: stop = 'output_limit'
                if stop: break
                try: p.wait(timeout=min(.05, max(.001, job['timeout']-elapsed)))
                except subprocess.TimeoutExpired: pass
        except psutil.NoSuchProcess: pass
        finally:
            # The Z3 pipeline gives external stages their own sessions. Track
            # and stop descendants as well as the worker's process group.
            try:
                for q in proc.children(recursive=True): tracked[(q.pid, q.create_time())] = q
            except psutil.NoSuchProcess: pass
            for q in reversed(list(tracked.values())):
                try: q.kill()
                except psutil.NoSuchProcess: pass
            if p.poll() is None:
                try: os.killpg(p.pid, signal.SIGKILL)
                except ProcessLookupError: pass
                except PermissionError:
                    # macOS can deny killpg after the group exits between poll
                    # and kill. Descendants were stopped above; reap the child.
                    if p.poll() is None: p.kill()
            p.wait()
    elapsed = time.monotonic()-start
    if elapsed >= job['timeout'] and stop is None: stop = 'timeout'
    final = directory/'result.json'; progress = directory/'progress.json'
    if final.exists(): result = json.loads(final.read_text())
    elif progress.exists(): result = json.loads(progress.read_text())
    else: result = dict(status='infrastructure_error')
    if stop: result.update(status=stop)
    elif not final.exists(): result.update(status='infrastructure_error',reason=(directory/'worker.stderr').read_text()[:2000])
    result.update(sha256=job['sha256'],configuration=job['configuration']['id'],member=job['member'],
                  seconds=elapsed, peak_tree_rss_mib=peak/1024**2)
    (directory/'measurement.json').write_text(json.dumps(result,indent=2)+'\n')
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for name in ['manifest','corpus','config','out','carcara','ffpacheck']:ap.add_argument('--'+name,type=Path,required=True)
    ap.add_argument('--timeout',type=float,default=10);ap.add_argument('--jobs',type=int,default=4)
    ap.add_argument('--memory-mib',type=int,default=16384);ap.add_argument('--limit',type=int)
    args=ap.parse_args();args.out.mkdir(parents=True,exist_ok=True)
    configs=json.loads(args.config.read_text())
    members=[r for r in json.loads(args.manifest.read_text())['entries'] if r['paper']=='FMCAD26' and 'benchmark_set_FF_UNSAT_SMT' in r['paper_sets']]
    selected={r['sha256']:r for r in members}; keys=sorted(selected)
    if args.limit: keys=keys[:args.limit]
    meta=dict(timeout=args.timeout,jobs=args.jobs,memory_mib=args.memory_mib,
              memory='worker plus descendant RSS sampled every 50 ms; overshoot possible',
              timing='whole worker wall time including process startup, production and checking',
              members=len(members),distinct=len(keys),configurations=configs,
              binaries={c['id']:dict(path=c['command'][0],sha256=digest(c['command'][0])) for c in configs},
              checkers={k:dict(path=str(getattr(args,k).resolve()),sha256=digest(getattr(args,k))) for k in ['carcara','ffpacheck']},
              python=sys.version,runner_sha256=digest(__file__),
              pipeline_sha256={n:digest(ROOT/'scripts'/n) for n in ['ff_certificate.py','ff_boolean_proof.py','ff_proof_pipeline.py']})
    metapath=args.out/'metadata.json'
    if metapath.exists(): assert json.loads(metapath.read_text())==meta,'resume metadata differs'
    else: metapath.write_text(json.dumps(meta,indent=2)+'\n')
    (args.out/'selection.json').write_text(json.dumps([r for r in members if r['sha256'] in keys],indent=2)+'\n')
    done=set();journal=args.out/'runs.jsonl'
    if journal.exists():done={(r['configuration'],r['sha256']) for r in map(json.loads,journal.read_text().splitlines())}
    inputs=args.out/'inputs';inputs.mkdir(exist_ok=True);jobs=[]
    with zipfile.ZipFile(args.corpus) as z:
        for h in keys:
            content=z.read('inputs/'+h+'.smt2');assert hashlib.sha256(content).hexdigest()==h
            source=inputs/(h+'.smt2');source.write_bytes(content)
            for c in configs:
                if (c['id'],h) in done:continue
                jobs.append(dict(sha256=h,member=selected[h]['member'],input=str(source.resolve()),
                                 directory=str((args.out/c['id']/h).resolve()),configuration=c,
                                 timeout=args.timeout,memory_mib=args.memory_mib,
                                 carcara=str(args.carcara.resolve()),ffpacheck=str(args.ffpacheck.resolve())))
    random.Random(20260924).shuffle(jobs)
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool,journal.open('a') as f:
        for i,r in enumerate(pool.map(supervise,jobs),1):
            f.write(json.dumps(r)+'\n');f.flush()
            if i%50==0:print(i,'/',len(jobs),flush=True)
    print('complete',flush=True)


if __name__=='__main__':
    if '--worker' in sys.argv:
        job=json.load(sys.stdin)
        try: result=worker(job)
        except Exception as e:
            p=Path(job['directory'])/'progress.json'
            result=json.loads(p.read_text()) if p.exists() else {}
            result.update(status='unavailable' if type(e).__name__=='Invalid' else 'error',reason=f'{type(e).__name__}: {e}')
        (Path(job['directory'])/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    else:main()
