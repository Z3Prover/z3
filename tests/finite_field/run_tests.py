#!/usr/bin/env python3
"""Run the finite-field acceptance suites against one CMake build (Python 3.12+)."""
import argparse
import concurrent.futures
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
TESTS = Path(__file__).resolve().parent
CORE = [
    'test_ff_combination.py', 'test_ff_large_combination.py',
    'test_ff_root_clauses.py', 'test_ff_simplify.py',
    'test_ff_bit_propagation.py', 'test_ff_basis_cache.py',
    'test_ff_backend_recovery.py', 'test_qfff.py', 'test_ff_integration.py',
    'test_ff_general_algebra.py', 'test_ff_matrix.py', 'test_ff_basis_storage.py',
    'test_ff_reduction.py', 'test_ff_sparse_reducers.py', 'test_ff_round6.py',
    'test_ff_round7.py', 'test_ff_round8_roots.py', 'test_ff_preprocess.py',
    'test_zk.py', 'test_ff_review.py',
]
PROOFS = ['test_ff_certificates.py', 'test_ff_proof_pipeline.py', 'test_ff_boolean_proof.py']
CLI = {'test_qfff.py', 'test_ff_backend_recovery.py', 'test_ff_integration.py'}
EXTERNAL = {'test_ff_proof_pipeline.py', 'test_ff_boolean_proof.py'}
NATIVE = ['finite_field', 'ast', 'smt_context', 'smt2print_parse', 'api', 'arith_rewriter']


def positive(value):
    value = int(value)
    if value <= 0:
        raise argparse.ArgumentTypeError('must be positive')
    return value


def execute(name, command, env, output, timeout):
    started = time.monotonic()
    status, code = 'error', None
    # Use files rather than pipes: a failing solver must not fill the runner's
    # memory. A separate process group lets a timeout stop child solver processes.
    with (output / (name + '.log')).open('w') as log:
        try:
            proc = subprocess.Popen(command, cwd=ROOT, env=env, stdout=log,
                                    stderr=subprocess.STDOUT, start_new_session=True)
            try:
                code = proc.wait(timeout=timeout)
                status = 'passed' if code == 0 else 'failed'
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                proc.wait()
                status = 'timeout'
        except OSError as error:
            log.write(str(error) + '\n')
    result = dict(name=name, status=status, returncode=code,
                  seconds=time.monotonic() - started, command=command)
    print(f'{status.upper():7} {name} ({result["seconds"]:.2f}s)', flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build', type=Path, required=True)
    parser.add_argument('--suite', choices=['core', 'proofs', 'all'], default='core')
    parser.add_argument('--out', type=Path, required=True, help='new log directory')
    parser.add_argument('--jobs', type=positive, default=2)
    parser.add_argument('--timeout', type=positive, default=300, help='seconds per suite')
    parser.add_argument('--carcara', type=Path)
    parser.add_argument('--ffpacheck', type=Path)
    args = parser.parse_args()
    if os.name != 'posix':
        parser.error('this runner currently supports Linux and macOS')
    if sys.flags.optimize:
        parser.error('run without -O: the regression suites use Python assertions')
    build, output = args.build.resolve(), args.out.resolve()
    z3 = str(build / 'z3')
    jobs = []
    if args.suite in ('core', 'all'):
        jobs.extend(('native-' + n, [str(build / 'test-z3'), n]) for n in NATIVE)
        jobs.append(('cpp-api', [str(build / 'test-ff-api')]))
        for name in CORE:
            command = [sys.executable, str(TESTS / name)]
            if name in CLI:
                command += ['--z3', z3]
            jobs.append((name.removesuffix('.py'), command))
    if args.suite in ('proofs', 'all'):
        if not args.carcara or not args.ffpacheck:
            parser.error('proof suites require --carcara and --ffpacheck; none are silently skipped')
        for path in [args.carcara, args.ffpacheck]:
            if not path.is_file() or not os.access(path, os.X_OK):
                parser.error(f'checker is not executable: {path}')
        for name in PROOFS:
            command = [sys.executable, str(TESTS / name), '--z3', z3]
            if name in EXTERNAL:
                command += ['--carcara', str(args.carcara.resolve()),
                            '--ffpacheck', str(args.ffpacheck.resolve())]
            jobs.append((name.removesuffix('.py'), command))
    env = dict(os.environ, PYTHONPATH=str(build / 'python'),
               Z3_LIBRARY_PATH=str(build), PYTHONNOUSERSITE='1')
    env.pop('PYTHONOPTIMIZE', None)
    output.mkdir(parents=True, exist_ok=False)
    # Fail early if Python or its shared library came from an installed Z3.
    probe = '''import sys, ctypes, z3
from pathlib import Path
from z3 import z3core
build = Path(sys.argv[1])
assert Path(z3.__file__).resolve().is_relative_to(build / 'python'), z3.__file__
library = build / ('libz3.dylib' if sys.platform == 'darwin' else 'libz3.so')
expected = ctypes.CDLL(str(library))
loaded_function = z3core.Z3_mk_context.__defaults__[0].f
assert ctypes.cast(loaded_function, ctypes.c_void_p).value == ctypes.cast(expected.Z3_mk_context, ctypes.c_void_p).value, 'wrong shared library'
assert z3.FiniteFieldSort(7).size() == 7
print(z3.get_full_version(), z3.__file__, str(library), sep='\\n')
'''
    results = [execute('bindings', [sys.executable, '-c', probe, str(build)], env, output, args.timeout)]
    if results[0]['status'] == 'passed':
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
            futures = [pool.submit(execute, name, command, env, output, args.timeout)
                       for name, command in jobs]
            results.extend(f.result() for f in futures)
    summary = dict(suite=args.suite, build=str(build), python=sys.executable,
                   planned=len(jobs) + 1, results=results)
    (output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    failed = sum(r['status'] != 'passed' for r in results)
    print(f'{len(results) - failed}/{summary["planned"]} passed; logs: {output}')
    return int(failed != 0 or len(results) != summary['planned'])


if __name__ == '__main__':
    sys.exit(main())
