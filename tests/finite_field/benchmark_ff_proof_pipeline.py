"""Fixed FMCAD proof-subset screen; original bytes, deduplication, full outcomes.

POSIX: one wall-clock deadline covers preprocessing, production and all checks.
External children are killed by the pipeline runner when the deadline fires.
"""
import argparse
import collections
import concurrent.futures
import hashlib
import json
from pathlib import Path
import signal
import sys
import time
import zipfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
import ff_proof_pipeline as pp


def execute(job):
    row, text, destination, z3, carcara, ffpacheck, timeout = job
    out = Path(destination) / row['sha256']
    result = dict(sha256=row['sha256'], member=row['member'], status='error')
    start = time.monotonic()
    def expired(signum, frame):
        raise pp.fc.Invalid('whole pipeline timeout')
    signal.signal(signal.SIGALRM, expired)
    signal.setitimer(signal.ITIMER_REAL, timeout)
    try:
        normalized = pp.LiteralProblem(text).normalized()
        out.mkdir()
        (out / 'problem.smt2').write_text(text)
        solver = pp.run([z3, '-in'], timeout, normalized + f'(ff-certify :timeout {int(timeout * 900)})\n')
        result['producer_seconds'] = solver['seconds']
        dag = solver['stdout']
        if not dag.startswith('(ff-certificate\n'):
            result.update(status='unavailable', reason=dag.strip())
        else:
            t = time.monotonic()
            normalized, alethe, pac = pp.export_artifact(text, dag)
            result['export_seconds'] = time.monotonic() - t
            for name, data in [('certificate.ffcert', dag), ('polynomial-input.smt2', normalized),
                               ('proof.alethe', alethe), ('proof.pac', pac)]:
                (out / name).write_text(data)
            stages = pp.check_bundle(out, carcara, ffpacheck, timeout)
            result.update(status='checked', stages=stages,
                          bytes=dict(dag=len(dag.encode()), alethe=len(alethe.encode()), pac=len(pac.encode())))
    except (pp.fc.Invalid, ValueError, TypeError, IndexError, KeyError, OSError, RecursionError) as e:
        result['reason'] = str(e)
        result['status'] = 'timeout' if 'timeout' in str(e) else 'rejected' if out.exists() else 'unsupported'
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    result['seconds'] = time.monotonic() - start
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, required=True)
    parser.add_argument('--corpus', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    for tool in ['z3', 'carcara', 'ffpacheck']:
        parser.add_argument('--' + tool, type=Path, required=True)
    parser.add_argument('--timeout', type=float, default=10)
    parser.add_argument('--jobs', type=int, default=4)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=False)
    manifest = json.loads(args.manifest.read_text())
    members = [r for r in manifest['entries'] if r['paper'] == 'FMCAD26' and 'benchmark_set_FF_UNSAT_SMT' in r['paper_sets']]
    selected = {r['sha256']: r for r in members}
    (args.out / 'selection.json').write_text(json.dumps(list(selected.values()), indent=2))
    metadata = dict(timeout=args.timeout, jobs=args.jobs, budget='whole pipeline wall time per distinct input',
                    memory_limit='none (bounded Python checker and Z3 reconstruction)', members=len(members),
                    carcara_revision=pp.CARCARA_REVISION, ffpacheck_revision=pp.FFPACHECK_REVISION,
                    ffpacheck_patch='tests/finite_field/proof_checkers/ffpacheck-completion.patch',
                    binaries={k: dict(path=str(getattr(args,k).resolve()), sha256=pp.digest(getattr(args,k)))
                              for k in ['z3','carcara','ffpacheck']}, python=sys.version)
    (args.out / 'metadata.json').write_text(json.dumps(metadata, indent=2))
    jobs = []
    with zipfile.ZipFile(args.corpus) as z:
        for h, row in sorted(selected.items()):
            data = z.read('inputs/' + h + '.smt2')
            assert hashlib.sha256(data).hexdigest() == h
            jobs.append((row, data.decode(), str(args.out.resolve()), str(args.z3.resolve()),
                         str(args.carcara.resolve()), str(args.ffpacheck.resolve()), args.timeout))
    counts, reasons = collections.Counter(), collections.Counter()
    with concurrent.futures.ProcessPoolExecutor(max_workers=args.jobs) as pool, (args.out / 'runs.jsonl').open('w') as f:
        for i, r in enumerate(pool.map(execute, jobs), 1):
            f.write(json.dumps(r) + '\n'); f.flush()
            counts[r['status']] += 1
            if r['status'] != 'checked': reasons[r.get('reason', '')] += 1
            if i % 25 == 0: print(i, dict(counts), flush=True)
    summary = dict(distinct=len(jobs), counts=dict(counts), reasons=dict(reasons))
    (args.out / 'summary.json').write_text(json.dumps(summary, indent=2))
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
