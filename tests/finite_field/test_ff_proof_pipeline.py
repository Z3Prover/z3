"""End-to-end artifact-format tests; requires real Carcara and FFPacheck binaries."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
import ff_proof_pipeline as pp

LARGE = 21888242871839275222246405745257275088548364400416034343698204186575808495617


def reject(operation):
    try:
        operation()
    except pp.fc.Invalid:
        return
    raise AssertionError('invalid input/proof accepted')


def source(p, body, extra=''):
    return f'(set-logic QF_FF)\n(define-sort F () (_ FiniteField {p}))\n(declare-const x F)\n(declare-const y F)\n{extra}\n{body}\n'


def produce(text, args, out):
    out.mkdir()
    normalized = pp.LiteralProblem(text).normalized()
    dag = pp.run([args.z3, '-in'], 10, normalized + '(ff-certify)\n')['stdout']
    normalized, alethe, pac = pp.export_artifact(text, dag)
    for name, value in [('problem.smt2', text), ('polynomial-input.smt2', normalized),
                        ('certificate.ffcert', dag), ('proof.alethe', alethe), ('proof.pac', pac)]:
        (out / name).write_text(value)
    pp.check_bundle(out, args.carcara, args.ffpacheck)
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['z3', 'carcara', 'ffpacheck']:
        parser.add_argument('--' + name, required=True)
    args = parser.parse_args()
    checked, rejected = 0, 0
    with tempfile.TemporaryDirectory(prefix='ff-pipeline-tests-') as temp:
        root = Path(temp)
        for p in [2, 3, 7, 4294967311, LARGE]:
            for body in [
                '(assert (= (ff.mul x y) (as ff1 F)))\n(assert (= (ff.mul x (ff.add y (as ff1 F))) (as ff1 F)))',
                '(assert (and (= x y) (not (= (ff.mul x x) (ff.mul y y)))))',
                '(assert (not (= x x)))',
                '(assert (= (as ff1 F) (as ff0 F)))',
                '(assert (and (and (= x (as ff0 F)) (= y x)) (not (= y (as ff0 F)))))',
            ]:
                last = produce(source(p, body), args, root / str(checked)); checked += 1
        for text in [
            source(7, '(assert (let ((a x) (b y)) (and (= a b) (not (= b a)))))'),
            source(7, '(assert (and (= alias (as ff0 F)) (not (= |quoted x| (as ff0 F)))))',
                   '(declare-const |quoted x| F)\n(define-fun alias () F |quoted x|)'),
            source(7, '(assert (and (= ff_witness_0 ff_witness_0_bound) (not (= ff_witness_0 ff_witness_0_bound))))',
                   '(declare-const ff_witness_0 F)\n(declare-const ff_witness_0_bound F)'),
            source(LARGE, '(assert (! (= x (as ff-1 F)) :named a))\n(assert (not (= x (as ff-1 F))))'),
        ]:
            last = produce(text, args, root / str(checked)); checked += 1
        # Bundle rechecking reads stored proof bytes. It must reject corruption,
        # not regenerate a fresh proof and mistakenly validate that replacement.
        edits = [
            ('proof.pac', lambda s: s.replace('m ', 'm 1', 1)),
            ('proof.pac', lambda s: s.replace('a 1 ', 'a 1 1 + ', 1)),
            ('proof.pac', lambda s: s.replace('v1', 'v999')),
            ('proof.pac', lambda s: s.replace('unsat', '')),
            ('proof.pac', lambda s: s + 'a 999 1;\n'),
            ('proof.alethe', lambda s: s.replace(':rule ff_pac', ':rule hole')),
            ('proof.alethe', lambda s: s.replace('(step contradiction (cl)', '(step contradiction (cl false)')),
            ('proof.alethe', lambda s: s.replace(':rule ff_diseq', ':rule hole')),
            ('proof.alethe', lambda s: s.replace('choice', 'exists')),
            ('proof.alethe', lambda s: s + '(step extra (cl) :rule hole)\n'),
            ('polynomial-input.smt2', lambda s: s.replace('(assert', '; changed\n(assert', 1)),
            ('certificate.ffcert', lambda s: s.replace(':modulus ', ':modulus 1', 1)),
            ('problem.smt2', lambda s: s.replace('(as ff-1 F)', '(as ff0 F)', 1)),
        ]
        for file, mutate in edits:
            path = last / file; original = path.read_text(); changed = mutate(original)
            assert changed != original, file
            path.write_text(changed)
            reject(lambda: pp.check_bundle(last, args.carcara, args.ffpacheck)); rejected += 1
            path.write_text(original)
        for text in [
            source(7, '(assert (or (= x y) (not (= x y))))'),
            source(7, '(assert (= (ff.bitsum x y) (as ff0 F)))'),
            source(7, '(push)\n(assert (= x y))'),
            source(7, '(assert (= b b))', '(declare-const b Bool)'),
        ]:
            reject(lambda: pp.LiteralProblem(text).normalized()); rejected += 1
        # SAT inputs must not acquire a certificate through inverse witnesses.
        for p in [2, 7, LARGE]:
            text = source(p, '(assert (not (= x (as ff0 F))))')
            normalized = pp.LiteralProblem(text).normalized()
            dag = pp.run([args.z3, '-in'], 10, normalized + '(ff-certify)\n')['stdout']
            assert 'ff-certificate-unavailable' in dag
            reject(lambda: pp.export_artifact(text, dag)); rejected += 1
        # Real external negative checks: missing contradiction and false arithmetic.
        for pac in ['', 'm 7;\na 1 v1;\n', 'm 7;\na 1 v1;\nl 2 1*(1), 1;\nunsat\n']:
            path = root / 'bad.pac'; path.write_text(pac)
            result = subprocess.run([args.ffpacheck, str(path)], capture_output=True, timeout=10)
            assert result.returncode != 0, 'external checker accepted incomplete/false proof'
            rejected += 1
        # The public Carcara bridge does not bind ff_pac axioms to premises.
        # Keep this executable witness of why check_bundle is mandatory.
        sat = root / 'sat.smt2'; sat.write_text(source(7, '(assert (= x x))'))
        alien = root / 'alien.alethe'
        alien.write_text('(step c (cl) :rule ff_pac :args (m 7;\na 1 1;\nl 2 1*(1), 1;\nunsat\n))\n')
        result = pp.run([args.carcara, 'check', str(alien), str(sat), '--ff-pac-solver', args.ffpacheck], 10)
        assert result['stdout'].strip() == 'valid', 'upstream binding behavior changed; reevaluate guard requirement'
        # Our input-bound checker must still reject that proof.
        original = (last / 'proof.alethe').read_text()
        (last / 'proof.alethe').write_text(alien.read_text())
        reject(lambda: pp.check_bundle(last, args.carcara, args.ffpacheck)); rejected += 1
        (last / 'proof.alethe').write_text(original)
        # Deadline enforcement is part of the pipeline contract.
        reject(lambda: pp.run([sys.executable, '-c', 'import time; time.sleep(30)'], 0.1)); rejected += 1
    print(json.dumps(dict(externally_checked=checked, rejected=rejected,
                          carcara_unbound_pac_reproduced=True)))


if __name__ == '__main__':
    main()
