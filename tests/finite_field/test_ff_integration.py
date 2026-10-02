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
    # Adding a theory must preserve existing family IDs: renumbering them
    # changes AST hashes and even the printed model for a field-free script.
    # This snapshot matches upstream and failed with early FF registration.
    unrelated = '(declare-const a String)(declare-const b String)' \
                '(assert (= a "abc"))(assert (= b "de"))(check-sat)(get-model)'
    assert run(z3, unrelated) == 'sat\n(\n  (define-fun b () String\n    "de")\n  (define-fun a () String\n    "abc")\n)\n'
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
    # Compound sorts must print and parse native indexed field sorts, including
    # moduli too large for the parser's unsigned-index declaration metadata.
    for prime in [7, 2305843009213693951,
                  21888242871839275222246405745257275088548364400416034343698204186575808495617]:
        field = f'(_ FiniteField {prime})'
        for container, value in [
            (f'(Array Int {field})', f'((as const (Array Int {field})) #f2m{prime})'),
            (f'(Seq {field})', f'(seq.unit #f2m{prime})'),
            (f'(Array Int (Seq {field}))',
             f'((as const (Array Int (Seq {field}))) (seq.unit #f2m{prime}))'),
        ]:
            source = f'(set-logic ALL)(declare-const a {container})(assert (= a {value}))'
            output = run(z3, source + '(check-sat)(get-model)', ['model_validate=true'])
            assert output.startswith('sat\n(') and container in ' '.join(output.split()), output
            # Reparse the printed definitions in a fresh command context.
            model = output.split('\n', 1)[1].strip()
            assert model.startswith('(') and model.endswith(')'), model
            assert run(z3, model[1:-1] + '(check-sat)').strip() == 'sat'
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
