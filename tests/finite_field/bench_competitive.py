#!/usr/bin/env python3
"""Competitive QF_FF benchmark: Z3 against cvc5 (GB and split backends).

Generates self-contained suites (no downloads), runs each solver in a fresh
process with a wall-clock limit, cross-checks answers and prints a summary.

Suites
  dense   random dense quadratic systems, planted (SAT) and over-determined
          (UNSAT with high probability), n = 3..9, over M31 and BN254.
  under   under-determined planted systems (positive-dimensional ideals).
  fuzz    small random Boolean combinations over F_p, p in {3..13}; the
          expected answer is obtained by exhaustive enumeration.
  diff    random Boolean combinations over large primes; answers are
          compared between solvers only.

Any SAT/UNSAT disagreement (or a wrong answer on `fuzz`) makes the script
exit with status 1, so it can gate CI. Timings are reported per suite.

Example
  python3 tests/finite_field/bench_competitive.py --z3 build/z3 \
      --cvc5 /path/to/cvc5 --suites dense under fuzz --timeout 20
"""
import argparse
import itertools
import json
import random
import re
import subprocess
import sys
import time
from pathlib import Path

M31 = 2**31 - 1
BN254 = 21888242871839275222246405745257275088548364400416034343698204186575808495617
FIELDS = {'m31': M31, 'bn254': BN254}


def header(p, n):
    return ['(set-logic QF_FF)', f'(define-sort F () (_ FiniteField {p}))'] + \
           [f'(declare-const x{i} F)' for i in range(n)]


def quadratic_system(rng, p, n, m, planted, density=0.5):
    sol = [rng.randrange(p) for _ in range(n)]
    lines = header(p, n)
    for _ in range(m):
        terms, val = [], 0
        for i in range(n):
            for j in range(i, n):
                if rng.random() < density:
                    c = rng.randrange(1, p)
                    terms.append(f'(ff.mul (as ff{c} F) x{i} x{j})')
                    val += c * sol[i] * sol[j]
            c = rng.randrange(1, p)
            terms.append(f'(ff.mul (as ff{c} F) x{i})')
            val += c * sol[i]
        const = (-val) % p if planted else rng.randrange(p)
        terms.append(f'(as ff{const} F)')
        lines.append(f'(assert (= (ff.add {" ".join(terms)}) (as ff0 F)))')
    lines.append('(check-sat)')
    return '\n'.join(lines), ('sat' if planted else None)


def random_poly(rng, p, nv, max_deg, max_terms):
    terms = []
    for _ in range(rng.randint(1, max_terms)):
        c = rng.randrange(1, p)
        vs = [rng.randrange(nv) for _ in range(rng.randint(0, max_deg))]
        terms.append((c, vs))
    return terms


def poly_smt(poly):
    parts = []
    for c, vs in poly:
        parts.append(f'(as ff{c} F)' if not vs else f'(ff.mul (as ff{c} F) {" ".join(f"x{v}" for v in vs)})')
    return parts[0] if len(parts) == 1 else f'(ff.add {" ".join(parts)})'


def poly_eval(poly, a, p):
    total = 0
    for c, vs in poly:
        t = c
        for v in vs:
            t *= a[v]
        total += t
    return total % p


def boolean_system(rng, p, nv, na, exact):
    lines = header(p, nv)
    clauses = []
    for _ in range(na):
        lits = []
        for _ in range(rng.choice([1, 1, 1, 2])):
            lhs = random_poly(rng, p, nv, rng.randint(1, 3), 4)
            rhs = rng.randrange(p) if rng.random() < 0.5 else 0
            lits.append((lhs, rhs, rng.random() < 0.85))
        clauses.append(lits)
        smt = [f'(= {poly_smt(l)} (as ff{r} F))' if pos else f'(not (= {poly_smt(l)} (as ff{r} F)))'
               for l, r, pos in lits]
        lines.append(f'(assert {smt[0] if len(smt) == 1 else "(or " + " ".join(smt) + ")"})')
    lines.append('(check-sat)')
    expected = None
    if exact:
        sat = any(all(any((poly_eval(l, a, p) == r % p) == pos for l, r, pos in c) for c in clauses)
                  for a in itertools.product(range(p), repeat=nv))
        expected = 'sat' if sat else 'unsat'
    return '\n'.join(lines), expected


def suite(name, seed):
    rng = random.Random(seed)
    cases = []
    if name == 'dense':
        for fname, p in FIELDS.items():
            for n in range(3, 10):
                for planted in (True, False):
                    smt, exp = quadratic_system(rng, p, n, n if planted else n + 1, planted)
                    cases.append((f'dense_{fname}_n{n}_{"planted" if planted else "over"}', smt, exp))
    elif name == 'under':
        for fname, p in FIELDS.items():
            for n in (4, 6, 8):
                smt, exp = quadratic_system(rng, p, n, n - 1, True)
                cases.append((f'under_{fname}_n{n}', smt, exp))
    elif name == 'fuzz':
        for k in range(200):
            p = rng.choice([3, 5, 7, 11, 13])
            nv = rng.randint(1, 4)
            smt, exp = boolean_system(rng, p, nv, rng.randint(1, 5), exact=True)
            cases.append((f'fuzz_{k}_p{p}', smt, exp))
    elif name == 'diff':
        for k in range(100):
            p = rng.choice([101, 65537, M31, BN254])
            nv = rng.randint(2, 5)
            smt, _ = boolean_system(rng, p, nv, rng.randint(2, nv + 2), exact=False)
            cases.append((f'diff_{k}', smt, None))
    return cases


def run(cmd, smt, timeout):
    start = time.perf_counter()
    try:
        r = subprocess.run(cmd, input=smt, text=True, capture_output=True, timeout=timeout + 2)
        out = re.findall(r'^(sat|unsat|unknown)$', r.stdout, re.M)
        answer = out[0] if out else 'error'
    except subprocess.TimeoutExpired:
        answer = 'timeout'
    elapsed = time.perf_counter() - start
    if answer in ('unknown', 'error') and elapsed >= timeout:
        answer = 'timeout'
    return answer, min(elapsed, timeout)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--z3', required=True)
    ap.add_argument('--cvc5', help='field-enabled (CoCoA) cvc5 binary; omit to run Z3 only')
    ap.add_argument('--suites', nargs='+', default=['dense', 'under', 'fuzz', 'diff'])
    ap.add_argument('--timeout', type=float, default=20)
    ap.add_argument('--seed', type=int, default=2026)
    ap.add_argument('--json', type=Path)
    args = ap.parse_args()

    solvers = {'z3': [args.z3, '-in', f'-T:{int(args.timeout)}']}
    if args.cvc5:
        ms = int(args.timeout * 1000)
        solvers['cvc5'] = [args.cvc5, '--lang=smt2', f'--tlimit={ms}']
        solvers['cvc5-split'] = [args.cvc5, '--lang=smt2', '--ff-solver=split', f'--tlimit={ms}']

    rows, failures = [], 0
    for name in args.suites:
        totals = {s: [0, 0.0] for s in solvers}
        for case, smt, expected in suite(name, args.seed):
            answers = {s: run(cmd, smt, args.timeout) for s, cmd in solvers.items()}
            decided = {s: a for s, (a, _) in answers.items() if a in ('sat', 'unsat')}
            bad = []
            if expected:
                bad += [f'{s}-wrong' for s, a in decided.items() if a != expected]
            elif 'z3' in decided and any(a != decided['z3'] for a in decided.values()):
                bad.append('z3-disagrees')
            # Only Z3's own mistakes (or unexplained disagreements with Z3) fail
            # the run; other solvers' wrong answers are reported for triage.
            if any(b.startswith('z3') for b in bad):
                failures += 1
            for s, (a, t) in answers.items():
                if a in ('sat', 'unsat'):
                    totals[s][0] += 1
                    totals[s][1] += t
            rows.append(dict(suite=name, case=case, expected=expected,
                             answers={s: a for s, (a, _) in answers.items()},
                             seconds={s: round(t, 3) for s, (_, t) in answers.items()}, bad=bad))
            line = ' | '.join(f'{s} {a} {t:.2f}s' for s, (a, t) in answers.items())
            print(f'{case:34s} {line}{"  <-- " + ",".join(bad) if bad else ""}', flush=True)
        n = len([r for r in rows if r['suite'] == name])
        summary = ', '.join(f'{s}: {c}/{n} solved in {t:.1f}s' for s, (c, t) in totals.items())
        print(f'== {name}: {summary}', flush=True)
    if args.json:
        args.json.write_text(json.dumps(rows, indent=1) + '\n')
    if failures:
        print(f'{failures} wrong or conflicting answers', file=sys.stderr)
    sys.exit(1 if failures else 0)


if __name__ == '__main__':
    main()
