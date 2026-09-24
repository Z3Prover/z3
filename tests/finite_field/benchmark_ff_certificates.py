"""Small reproducible certificate-cost screen; not a corpus coverage benchmark."""
import argparse
import hashlib
import json
from pathlib import Path
import statistics
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
import ff_certificate as checker

LARGE = 21888242871839275222246405745257275088548364400416034343698204186575808495617


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--z3', type=Path, required=True)
    parser.add_argument('--baseline', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--repeat', type=int, default=5)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    metadata = {'binaries': {name: {'path': str(path.resolve()), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
                              for name, path in [('candidate', args.z3), ('baseline', args.baseline)]}, 'repeat': args.repeat,
                'description': 'Two asserted equations x^degree=0 and x*y=1; no expected result is supplied to the producer/checker.'}
    (args.out / 'metadata.json').write_text(json.dumps(metadata, indent=2))
    results = []
    for p in [7, LARGE]:
        for degree in [4, 8, 16, 32]:
            name = f'{"large" if p == LARGE else "small"}-{degree}'
            text = f'(set-logic QF_FF)\n(define-sort F () (_ FiniteField {p}))\n(declare-const x F)\n(declare-const y F)\n'
            text += '(assert (= (ff.mul ' + ' '.join(['x'] * degree) + ') (as ff0 F)))\n'
            text += '(assert (= (ff.mul x y) (as ff1 F)))\n'
            (args.out / (name + '.smt2')).write_text(text)
            timings = {key: [] for key in ['baseline', 'disabled', 'certificate', 'dag_check', 'alethe_check']}
            rss = {key: [] for key in ['baseline', 'disabled', 'certificate']}
            for repetition in range(args.repeat):
                # Alternate baseline/candidate order, keep certificate runs after
                # both. Each invocation is isolated and has the same deadline.
                configurations = [('baseline', args.baseline, '(check-sat)\n'), ('disabled', args.z3, '(check-sat)\n')]
                if repetition % 2:
                    configurations.reverse()
                configurations.append(('certificate', args.z3, '(ff-certify)\n'))
                for mode, binary, suffix in configurations:
                    start = time.perf_counter()
                    command = [str(binary.resolve()), '-in']
                    if sys.platform == 'darwin': command = ['/usr/bin/time', '-l'] + command
                    result = subprocess.run(command, input=text + suffix, text=True,
                                            capture_output=True, timeout=15)
                    timings[mode].append(time.perf_counter() - start)
                    assert result.returncode == 0, result
                    if sys.platform == 'darwin':
                        match = re.search(r'(\d+)\s+maximum resident set size', result.stderr)
                        assert match, result.stderr
                        rss[mode].append(int(match[1]) / (1024 * 1024))
                    else: assert not result.stderr, result.stderr
                    if mode == 'certificate':
                        proof = result.stdout
                        start = time.perf_counter(); _, cert, _ = checker.verify(text, proof)
                        timings['dag_check'].append(time.perf_counter() - start)
                        alethe = checker.export_alethe(text, proof)
                        start = time.perf_counter(); checker.verify_alethe(text, alethe)
                        timings['alethe_check'].append(time.perf_counter() - start)
                    else:
                        assert result.stdout.strip() == 'unsat', result.stdout
            (args.out / (name + '.ffcert')).write_text(proof)
            (args.out / (name + '.alethe')).write_text(alethe)
            row = {'case': name, 'prime': str(p), 'degree': degree, 'timings': timings,
                   'median_seconds': {k: statistics.median(v) for k, v in timings.items()},
                   'peak_rss_mib': rss,
                   'dag_nodes': len(cert[':nodes']), 'dag_bytes': len(proof.encode()), 'alethe_bytes': len(alethe.encode())}
            results.append(row)
            print(name, row['median_seconds'], 'nodes', row['dag_nodes'], flush=True)
    (args.out / 'results.json').write_text(json.dumps(results, indent=2))


if __name__ == '__main__':
    main()
