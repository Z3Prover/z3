#!/usr/bin/env python3
"""CLI compatibility, global budgets and scoped finite-field integration."""
import argparse
import subprocess
import re


def run(z3, source, options=(), error=False):
    r = subprocess.run([z3, '-in', *options], input=source, text=True,
                       capture_output=True, timeout=20)
    if error:
        assert '(error' in r.stdout, r
    else:
        assert r.returncode == 0 and '(error' not in r.stdout, r
    return r.stdout


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--z3', required=True)
    z3 = p.parse_args().z3
    for logic in ['', '(set-logic ALL)']:
        # Indexed native sorts must coexist with an old user-defined name.
        src = logic + '''
(declare-sort FiniteField 0)
(declare-const old FiniteField)
(declare-const x (_ FiniteField 7))
(assert (= x (as #f5m7 (_ FiniteField 7))))
(check-sat)
'''
        assert run(z3, src).strip() == 'sat'
    assert run(z3, '(simplify (as #f5m7 (_ FiniteField 7)))').strip() == '(as ff5 (_ FiniteField 7))'
    run(z3, '(simplify (as #f5m7 (_ FiniteField 11)))', error=True)
    run(z3, '(set-logic QF_UF)(declare-const x (_ FiniteField 7))', error=True)
    assert run(z3, '(declare-const c Bool)(simplify (= (ite c #f1m7 #f2m7) #f1m7))').strip() == 'c'
    src = '''(set-logic QF_FF)
(declare-const x (_ FiniteField 7))
(assert (= (ff.mul x x) #f2m7))
'''
    check = '(check-sat-using ff-solve)'
    assert run(z3, src + check).strip() == 'sat'
    # Both configuration entry points must reach the engine. A tactic-local
    # override takes precedence over a command-line/global budget.
    for param in ['max_steps', 'max_terms']:
        assert run(z3, src + check, ['smt.ff.' + param + '=0']).strip() == 'unknown'
        local = '(check-sat-using (using-params ff-solve :ff.' + param + ' 2000000))'
        assert run(z3, src + local, ['smt.ff.' + param + '=0']).strip() == 'sat'
        assert run(z3, src + '(check-sat-using (using-params ff-solve :ff.' + param + ' 0))').strip() == 'unknown'
    # The public solver must conservatively recover after a native budget hit.
    assert run(z3, src + '(check-sat)', ['smt.ff.max_steps=0']).strip() == 'sat'
    mixed = """(declare-const x (_ FiniteField 7))
(declare-fun f ((_ FiniteField 7)) Int)
(assert (= (ff.mul x x) #f1m7))
(assert (distinct (f x) (f #f1m7)))
(assert (distinct (f x) (f #f6m7)))
(check-sat-using smt)"""
    for enabled in [False, True]:
        out = run(z3, mixed, ['-st', 'smt.ff.root_split=' + str(enabled).lower()])
        assert out.startswith('unsat'), out
        stats = {k: float(v) for k, v in re.findall(r':([a-z-]+)\s+([0-9.]+)', out)}
        assert bool(stats.get('ff-root-clauses', 0)) == enabled, out
    print('FF CLI integration: legacy names, qualified literals, equality rewriting and global/local budgets passed')


if __name__ == '__main__':
    main()
