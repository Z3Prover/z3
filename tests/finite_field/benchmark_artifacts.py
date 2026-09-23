#!/usr/bin/env python3
"""Resumable whole-corpus comparison; one durable JSONL row per solver/input.

Four workers by default; each worker runs one fresh solver at a time. Byte-
identical inputs shared by artifacts are run once. QF_BVFF is an artifact-specific
logic name: replace only that declaration with ALL for BOTH solvers, preserving
every assertion. Solver parsing, initialization and shutdown are timed.
Infrastructure failures are recorded separately and require a fresh output
directory for a clean rerun; they are never counted as solver timeouts.
"""
import argparse
import concurrent.futures
import ctypes
import hashlib
import json
import os
import platform
import random
import re
import resource
import shutil
import signal
import subprocess
import struct
import sys
import time
from pathlib import Path


def worker(c):
    start = time.perf_counter()
    result, stdout, stderr, code = 'error', '', '', None
    p = None
    try:
        p = subprocess.Popen(c['command'], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE, text=True)
        memory_limit = c.get('memory_mib', 4096) * 1024**2
        proc = ctypes.CDLL('/usr/lib/libproc.dylib', use_errno=True) if sys.platform == 'darwin' else None
        first = True
        while True:
            remaining = c['timeout']-(time.perf_counter()-start)
            try:
                stdout, stderr = p.communicate(input=c['smt'] if first else None, timeout=max(.001, min(.05, remaining)))
                code = p.returncode
                break
            except subprocess.TimeoutExpired:
                first = False
                if proc:
                    buf = ctypes.create_string_buffer(512)
                    ret = proc.proc_pid_rusage(p.pid, 2, buf)
                    if ret and p.poll() is None: raise RuntimeError('cannot sample solver RSS')
                    rss = struct.unpack_from('Q', buf.raw, 64)[0] if not ret else 0
                else:
                    try:
                        rss = int(re.search(r'^VmRSS:\s+(\d+)', Path(f'/proc/{p.pid}/status').read_text(), re.M)[1])*1024
                    except (FileNotFoundError, TypeError): rss = 0
                if rss > memory_limit or time.perf_counter()-start >= c['timeout']:
                    result = 'memout' if rss > memory_limit else 'timeout'
                    p.kill(); stdout, stderr = p.communicate(); code = p.returncode
                    break
        answers = re.findall(r'^(sat|unsat|unknown)\s*$', stdout, re.M)
        if result not in ('memout','timeout') and code == 0 and '(error' not in stdout and len(answers) == c['checks']:
            result = answers[0] if len(answers) == 1 else ('multi' if all(a in ('sat','unsat') for a in answers) else 'unknown')
    except subprocess.TimeoutExpired as e:
        result = 'timeout'
        stdout, stderr = e.stdout or b'', e.stderr or b''
        stdout = stdout.decode(errors='replace') if isinstance(stdout, bytes) else stdout
        stderr = stderr.decode(errors='replace') if isinstance(stderr, bytes) else stderr
    finally:
        # A supervisor SIGTERM or an RSS-sampling exception must not leave the
        # solver alive. Reap our direct child before the worker exits; the outer
        # process-group guard also covers descendants retaining pipe handles.
        if p is not None:
            if p.poll() is None:
                p.kill()
                p.communicate(timeout=1)
    u = resource.getrusage(resource.RUSAGE_CHILDREN)
    limit = c.get('output_limit', 65536)
    return dict(result=result, answers=re.findall(r'^(sat|unsat|unknown)\s*$', stdout, re.M),
                seconds=time.perf_counter()-start, cpu_seconds=u.ru_utime+u.ru_stime,
                peak_rss_mib=u.ru_maxrss/(1024**2 if sys.platform == 'darwin' else 1024),
                returncode=code, stdout=stdout[:limit], stderr=stderr[:limit])


def infrastructure_error(kind, message, *, seconds=0, stdout='', stderr='', returncode=None):
    return dict(result='infrastructure_error', answers=[], seconds=seconds,
                cpu_seconds=None, peak_rss_mib=None, returncode=returncode,
                stdout=stdout, stderr=stderr, infrastructure_kind=kind,
                infrastructure_message=message)


def _signal_group(p, sig):
    try:
        os.killpg(p.pid, sig)
    except ProcessLookupError:
        pass


def _stop_group(p):
    # TERM lets the Python worker reap its solver in finally. KILL bounds cleanup
    # if either process hangs or ignores TERM. The worker and all ordinary solver
    # descendants inherit one new session/process group owned by this run.
    _signal_group(p, signal.SIGTERM)
    try:
        p.communicate(timeout=1)
    except subprocess.TimeoutExpired:
        pass
    finally:
        _signal_group(p, signal.SIGKILL)
        p.communicate()


def _run_supervised(c, supervisor_timeout):
    start = time.perf_counter()
    p = None
    output_limit = c.get('output_limit', 65536)
    stdout = stderr = ''
    try:
        p = subprocess.Popen([sys.executable, __file__, '--worker'], stdin=subprocess.PIPE,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                             start_new_session=True)
        try:
            stdout, stderr = p.communicate(json.dumps(c), timeout=supervisor_timeout)
        except subprocess.TimeoutExpired:
            _stop_group(p)
            stdout, stderr = p.communicate()
            return infrastructure_error('supervisor_timeout',
                f'Benchmark worker exceeded {supervisor_timeout:g}s outer deadline; '
                f'worker/solver process group {p.pid} stopped. This is not a solver timeout.',
                seconds=time.perf_counter()-start, stdout=stdout[:output_limit],
                stderr=stderr[:output_limit], returncode=p.returncode)
        if p.returncode:
            return infrastructure_error('worker_exit', f'Benchmark worker exited with code {p.returncode}',
                seconds=time.perf_counter()-start, stdout=stdout[:output_limit],
                stderr=stderr[:output_limit], returncode=p.returncode)
        result = json.loads(stdout)
        if not isinstance(result, dict) or 'result' not in result:
            raise ValueError('Worker did not return a benchmark result object')
        return result
    except Exception as exc:
        return infrastructure_error('supervisor_error', f'{type(exc).__name__}: {exc}',
            seconds=time.perf_counter()-start, stdout=stdout[:output_limit],
            stderr=stderr[:output_limit], returncode=p.returncode if p else None)
    finally:
        if p is not None:
            # Also stop any descendants left behind after a worker failure or
            # an otherwise normal result. BaseException (including Ctrl-C) is
            # deliberately not converted into a logical measurement.
            _stop_group(p)


def run(c):
    # Python 3.9's repeated communicate(input=None) can stop feeding a large
    # input after the first sampling timeout. Use the tested runtime: otherwise
    # a solver waiting for the rest of stdin can be misclassified as a timeout.
    if sys.version_info < (3, 14):
        raise RuntimeError('This sampled benchmark harness requires Python 3.14 or later')
    return _run_supervised(c, c['timeout']+20)


def prepare(text, solver=None):
    text = re.sub(r'\(set-logic\s+QF_BVFF\s*\)', '(set-logic ALL)', text)
    if solver == 'z3':
        # Z3 already supports incremental commands; cvc5's enabling option is
        # not a Z3 parameter. Remove only a standalone true setting, preserving
        # all assertions, push/pop, assumptions and check-sat commands. Keeping
        # the solver argument explicit leaves historical replays reproducible.
        text = re.sub(r'(?m)^[ \t]*\(set-option\s+:incremental\s+true\s*\)[ \t]*(?=;|$)', '', text)
    return text


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--corpus', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--z3', type=Path, required=True)
    ap.add_argument('--cvc5', type=Path, required=True)
    ap.add_argument('--timeout', type=float, default=10)
    ap.add_argument('--jobs', type=int, default=4)
    ap.add_argument('--memory-mib', type=int, default=4096)
    ap.add_argument('--limit', type=int)
    args = ap.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    bins = args.out / 'binaries'; bins.mkdir(exist_ok=True)
    versions = {}
    for name, source in [('z3', args.z3), ('cvc5', args.cvc5)]:
        target = bins / name
        if not target.exists(): shutil.copy2(source, target)
        else:
            assert hashlib.sha256(source.read_bytes()).digest() == hashlib.sha256(target.read_bytes()).digest(), 'use a fresh result directory for a different solver binary'
        versions[name] = dict(sha256=hashlib.sha256(target.read_bytes()).hexdigest(),
            version=subprocess.check_output([str(target.resolve()), '--version'], text=True).splitlines()[0])
    manifest = json.loads((args.corpus/'manifest.json').read_text())
    unique = {r['sha256']: r for r in manifest['entries']}
    params = dict(timeout=args.timeout, jobs=args.jobs, platform=platform.platform(),
                  binaries=versions, seed=20260922, repetitions=1,
                  timing='fresh process wall time, bounded concurrent throughput run',
                  adaptation='QF_BVFF -> ALL on both solvers; remove standalone :incremental true for Z3; no assertion changes',
                  memory_mib=args.memory_mib,
                  memory='per-process peak RSS, sampled every 50 ms; kill on exceedance; sampling overshoot possible')
    meta = args.out/'metadata.json'
    if meta.exists():
        old = json.loads(meta.read_text())
        assert all(old[k] == params[k] for k in ['timeout','jobs','binaries','memory_mib','adaptation']), 'incompatible resume'
    else: meta.write_text(json.dumps(params, indent=2)+'\n')
    shutil.copy2(args.corpus/'manifest.json', args.out/'manifest.json')
    output = args.out/'runs.jsonl'
    previous = list(map(json.loads, output.read_text().splitlines())) if output.exists() else []
    if any(r['result'] == 'infrastructure_error' for r in previous):
        raise SystemExit('Infrastructure errors are preserved in runs.jsonl. Use a new output directory for a clean rerun; do not pool these rows with solver measurements.')
    done = {(r['sha256'], r['solver']) for r in previous}
    hashes = sorted(unique); random.Random(20260922).shuffle(hashes)
    if args.limit: hashes = hashes[:args.limit]
    commands = {'z3': [str((bins/'z3').resolve()), '-in'],
                'cvc5': [str((bins/'cvc5').resolve()), '--lang=smt2'],
                'cvc5_split': [str((bins/'cvc5').resolve()), '--lang=smt2', '--ff-solver=split']}
    tasks = []
    for i, sha in enumerate(hashes):
        labels = list(commands); labels = labels[i%3:]+labels[:i%3]
        tasks.extend((sha, label) for label in labels if (sha, label) not in done)

    def task(pair):
        sha, label = pair
        text = (args.corpus/'inputs'/(sha+'.smt2')).read_text()
        assert hashlib.sha256(text.encode()).hexdigest() == sha
        smt = prepare(text, solver=label)
        cmd = list(commands[label])
        if unique[sha]['checks'] > 1 and label != 'z3': cmd.append('--incremental')
        row = run(dict(command=cmd, smt=smt, timeout=args.timeout, checks=unique[sha]['checks'], memory_mib=args.memory_mib))
        row.update(sha256=sha, solver=label, input_sha256=hashlib.sha256(smt.encode()).hexdigest())
        if row['result'] in ('sat','unsat'): row.pop('stdout')
        return row

    print(f'{len(unique)} distinct inputs; {len(tasks)} runs pending; {args.jobs} workers; {args.timeout}s hard timeout', flush=True)
    start = time.monotonic()
    failed = 0
    with output.open('a', buffering=1) as f, concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        for i, row in enumerate(pool.map(task, tasks)):
            f.write(json.dumps(row)+'\n')
            failed += row['result'] == 'infrastructure_error'
            if i%100 == 0:
                print(f'{i+1}/{len(tasks)} new runs; elapsed {time.monotonic()-start:.0f}s; last {row["solver"]} {row["result"]}', flush=True)
    if failed:
        raise SystemExit(f'{failed} infrastructure errors recorded; use a new output directory for a clean rerun.')
    print('completed', flush=True)


if __name__ == '__main__':
    if '--worker' in sys.argv:
        def terminate_worker(signum, frame):
            raise SystemExit(128 + signum)
        signal.signal(signal.SIGTERM, terminate_worker)
        print(json.dumps(worker(json.load(sys.stdin))))
    else: main()
