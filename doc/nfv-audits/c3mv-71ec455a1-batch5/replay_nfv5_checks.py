"""Replay exact inputs outside immutable evidence; default to four successful gates."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import time

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('nfv5_bounded_runner', Path(__file__).with_name('verify_nfv5.py'))
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


def at(base, name):
    path = (base / name).resolve()
    assert path.is_relative_to(base.resolve()) and path.is_file(), name
    return path


def run_checks(bundle, chosen, dafny, solver, output, allow_resource=False):
    bundle, output = bundle.resolve(), output.resolve()
    assert not output.is_relative_to(bundle), 'Use output outside immutable bundle'
    assert not output.exists(), 'Use a new output directory'
    models = bundle / 'nfv5-models'
    for check in chosen:
        assert hashlib.sha256(at(models, check['input']).read_bytes()).hexdigest() == check['input_sha256']
        assert allow_resource or check['sequence'] != 13 and not check.get('wall_timed_out'), 'Resource-interrupted replay requires explicit opt-in'
    output.mkdir(parents=True)
    results = []
    for check in chosen:
        path = at(models, check['input'])
        command = [str(dafny.resolve()), 'verify', str(path), '--solver-path', str(solver.resolve()),
            '--verification-time-limit', '30', '--cores', '2', '--allow-warnings', '--show-snippets', 'false']
        if '--progress' in check['command']:
            command += ['--progress', 'Symbol']
        if check.get('mbqi'):
            assert check['command'][check['command'].index('--solver-option') + 1] == 'O:smt.mbqi=true'
            command += ['--solver-option', 'O:smt.mbqi=true']
        assert ('--isolate-assertions' in check['command']) == check.get('isolate_assertions', False)
        if check.get('isolate_assertions'):
            command += ['--isolate-assertions']
        log = output / (path.stem + '.log')
        start = time.monotonic()
        wall = min(check.get('wall_time_limit_seconds', 600), 600)
        with log.open('wb') as stream:
            actual, timed_out, interrupted_exit = runner.run_bounded(command, stream, wall)
        result = dict(sequence=check['sequence'], input=check['input'], input_sha256=check['input_sha256'],
            expected_exit=check['exit_code'], actual_exit=actual, matched=actual == check['exit_code'],
            seconds=round(time.monotonic()-start, 3), command=command, wall_time_limit_seconds=wall,
            wall_timed_out=timed_out, interrupted_process_exit_code=interrupted_exit,
            original_external_interruption=check['sequence']==13, log=log.name,
            log_sha256=hashlib.sha256(log.read_bytes()).hexdigest())
        results.append(result)
        (output / 'results.json').write_text(json.dumps(results, indent=2)+'\n', encoding='utf-8', newline='\n')
        print(json.dumps({k:result[k] for k in ['sequence','expected_exit','actual_exit','matched']}), flush=True)
    return 0 if all(row['matched'] for row in results) else 1


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bundle', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--dafny', type=Path, required=True)
    parser.add_argument('--solver', type=Path, required=True)
    parser.add_argument('--select', type=int, nargs='+', default=[1,2,3,6])
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--allow-resource-checks', action='store_true')
    args = parser.parse_args()
    checks = json.loads((args.bundle / 'nfv5-models' / 'checks.json').read_text())
    assert set(args.select) <= {c['sequence'] for c in checks}, 'Unknown check number'
    chosen = [c for c in checks if c['sequence'] in args.select]
    raise SystemExit(run_checks(args.bundle, chosen, args.dafny, args.solver, args.output, args.allow_resource_checks))
