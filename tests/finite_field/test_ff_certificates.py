"""Independent positive, exhaustive, corruption, and resource tests for FF certificates."""
import argparse
import copy
import itertools
import math
from pathlib import Path
import random
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
import ff_certificate as checker

LARGE = 21888242871839275222246405745257275088548364400416034343698204186575808495617


def source(p, equations, extra='', declarations='(declare-const x F)\n(declare-const y F)'):
    return f'(set-logic QF_FF)\n(define-sort F () (_ FiniteField {p}))\n{declarations}\n{extra}\n' + '\n'.join(f'(assert {eq})' for eq in equations) + '\n'


def numeral(c):
    return f'(as ff{c} F)'


def polynomial(terms):
    out = []
    for mon, c in terms.items():
        factors = [numeral(c)] + ['xy'[v] for v in mon]
        out.append(factors[0] if len(factors) == 1 else '(ff.mul ' + ' '.join(factors) + ')')
    return numeral(0) if not out else out[0] if len(out) == 1 else '(ff.add ' + ' '.join(out) + ')'


def run(binary, text, options=''):
    completed = subprocess.run([binary, '-in'], input=text + f'(ff-certify {options})\n', text=True, capture_output=True, timeout=15)
    assert not completed.stderr, completed.stderr
    return completed.stdout


def rejected(f, *args):
    try:
        f(*args)
    except checker.Invalid:
        return
    raise AssertionError('invalid certificate accepted')


def check_both(text, proof):
    checker.verify(text, proof)
    alethe = checker.export_alethe(text, proof)
    checker.verify_alethe(text, alethe)
    return alethe


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--z3', default=str(ROOT / 'build-ff-cmake/z3'))
    args = parser.parse_args()
    checked = 0
    for p in [2, 3, 7, 4294967291, 4294967311, LARGE]:
        fixtures = [
            [f'(= (ff.mul x y) {numeral(1)})', f'(= (ff.mul x (ff.add y {numeral(1)})) {numeral(1)})'],
            [f'(= (ff.mul x x) y)', f'(= (ff.mul x y) {numeral(1)})', f'(= (ff.mul y y) {numeral(0)})'],
            [f'(= {numeral(-1)} {numeral(0)})'],
            [f'(and (= x {numeral(0)}) (= (ff.bitsum y x) {numeral(0)}) (= y {numeral(1)}))'],
            [f'(= (let ((a (ff.add x {numeral(1)}))) (ff.mul a y)) {numeral(1)})', f'(= x {numeral(-1)})'],
            [f'(! (= (ff.neg x) {numeral(-1)}) :named first)', f'(= x {numeral(0)})'],
        ]
        for equations in fixtures:
            text = source(p, equations)
            proof = run(args.z3, text)
            check_both(text, proof); checked += 1
    # Search may reorder premises; every permutation must still bind its DAG
    # input nodes to the original equation indices, including unused premises.
    for p in [7, LARGE]:
        equations = [f'(= (ff.mul x y) {numeral(1)})', f'(= x {numeral(0)})', f'(= y {numeral(2)})']
        for permutation in itertools.permutations(equations):
            text = source(p, permutation)
            check_both(text, run(args.z3, text)); checked += 1
    # The first order exhausts the basis cap before seeing the last premise.
    # Reordering must preserve the original premise index in the checked proof.
    text = source(7, [f'(= v{i} {numeral(0)})' for i in range(257)] +
                  [f'(= {numeral(1)} {numeral(0)})'],
                  declarations='\n'.join(f'(declare-const v{i} F)' for i in range(257)))
    check_both(text, run(args.z3, text)); checked += 1
    # Definitions, simultaneous let binding and quoting are checked without Z3.
    text = source(LARGE, ['(= alias (as ff1 F))', '(= |quoted x| (as ff0 F))'],
                  extra='(define-fun alias () F (let ((z |quoted x|)) z))',
                  declarations='(declare-const |quoted x| F)')
    check_both(text, run(args.z3, text)); checked += 1
    text = source(7, ['(= (let ((x y) (y x)) (ff.add x (ff.neg y))) (as ff1 F))', '(= x y)'])
    check_both(text, run(args.z3, text)); checked += 1
    text = source(7, ['(= x #f-1m7)', '(= x #f0m7)'])
    check_both(text, run(args.z3, text)); checked += 1

    randomizer = random.Random(1729)
    sat, unsat = 0, 0
    monomials = [(), (0,), (1,), (0, 0), (0, 1), (1, 1)]
    for p in [2, 3, 5]:
        for _ in range(48):
            polynomials = [{m: randomizer.randrange(p) for m in monomials} for _ in range(2)]
            exists = any(all(sum(c * (1 if not m else math.prod(values[v] for v in m)) for m, c in f.items()) % p == 0
                             for f in polynomials) for values in itertools.product(range(p), repeat=2))
            # Explicitly asserted field equations make the algebraic ideal
            # complete for this exhaustive test. No implicit field axiom is
            # being smuggled into the checker or producer.
            polynomials += [{(v,) * p: 1, (v,): p - 1} for v in [0, 1]]
            text = source(p, [f'(= {polynomial(f)} {numeral(0)})' for f in polynomials])
            proof = run(args.z3, text)
            if exists:
                assert proof.strip() == '(ff-certificate-unavailable no-polynomial-refutation)', proof
                sat += 1
            else:
                check_both(text, proof); checked += 1; unsat += 1
    print(f'{checked} DAG/Alethe pairs checked; exhaustive systems: {unsat} UNSAT, {sat} SAT')

    text = source(LARGE, [f'(= (ff.mul x y) {numeral(1)})', f'(= (ff.mul x (ff.add y {numeral(1)})) {numeral(1)})'])
    proof = run(args.z3, text)
    obj = checker.parse(proof)[0]
    mutations = []
    def changed(key, value):
        result = copy.deepcopy(obj); result[result.index(key) + 1] = value; return result
    mutations += [changed(':root', '0'), changed(':root', '999999'), changed(':version', '2'), changed(':modulus', '7'),
                  changed(':variables', ['x', 'x']), changed(':variables', ['y', 'undeclared'])]
    nodes = obj[obj.index(':nodes') + 1]
    for i, node in enumerate(nodes):
        if node[0] == 'mul':
            corrupted = copy.deepcopy(nodes); corrupted[i][2] = str((int(node[2]) + 1) % LARGE)
            mutations.append(changed(':nodes', corrupted))
    for bad in [['input', '999'], ['add', '0', '999'], ['mul', '0', '1', ['999']], ['hole']]:
        mutations.append(changed(':nodes', [bad] + nodes[1:]))
    inputs = copy.deepcopy(obj[obj.index(':inputs') + 1]); inputs[0][0][0] = '2'
    mutations += [changed(':inputs', inputs), changed(':inputs', inputs[:-1]), changed(':nodes', nodes[:-1])]
    for malformed in mutations:
        rejected(checker.verify, text, checker.sexpr(malformed))
    rejected(checker.verify, text, proof[:-2])
    rejected(checker.verify, text, proof + proof)
    wrong_problem = text.replace('(as ff1 F)', '(as ff0 F)')
    rejected(checker.verify, wrong_problem, proof)
    mixed_problem = text.replace('(as ff1 F)', '(as ff1 (_ FiniteField 7))', 1)
    rejected(checker.verify, mixed_problem, proof)
    alethe = checker.export_alethe(text, proof)
    for bad in [alethe.replace('ff_poly_mul', 'hole', 1), alethe.replace(':args (', ':args (999 ', 1),
                alethe.replace(':premises (t', ':premises (missing', 1),
                alethe.replace('(cl)', '(cl false)'), '\n'.join(alethe.splitlines()[:-1]),
                alethe.replace('(as ff1 F)', '(as ff0 F)', 1)]:
        rejected(checker.verify_alethe, text, bad)
    rejected(checker.verify_alethe, wrong_problem, alethe)
    rejected(checker.verify_alethe, text, alethe.replace('(as ff1 (_ FiniteField', '(as ff2 (_ FiniteField', 1))
    print(f'{len(mutations) + 12} corrupt/wrong-problem/truncated certificate cases rejected')

    # No certificate is stronger than a misleading partial or native proof.
    for options in [':max_nodes 0', ':max_steps 0', ':max_terms 0']:
        assert run(args.z3, text, options).strip() == '(ff-certificate-unavailable budget)'
    transcript = run(args.z3, text + '(ff-certify :max_nodes 0)\n')
    assert transcript.startswith('(ff-certificate-unavailable budget)\n')
    check_both(text, transcript.split('\n', 1)[1])
    root_only = source(3, [f'(= (ff.mul x x) {numeral(-1)})'])
    assert 'no-polynomial-refutation' in run(args.z3, root_only)
    for unsupported in [source(7, ['(not (= x y))']), source(7, ['(or (= x y) (= x (as ff0 F)))']),
                        source(7, ['(= (f x) x)'], extra='(declare-fun f (F) F)'),
                        source(7, ['(= x y)', '(= z z)'], extra='(declare-const z (_ FiniteField 11))')]:
        assert '(error ' in run(args.z3, unsupported)
    rejected(checker.verify, text + '(push 1)\n', proof)
    # Reconstruction must not change the normal solver's assertions/result.
    lifecycle = source(7, ['(= x y)']) + '(check-sat)\n(ff-certify)\n(push 1)\n'
    lifecycle += '(assert (= x (as ff0 F)))\n(assert (= y (as ff1 F)))\n(ff-certify)\n(pop 1)\n(check-sat)\n'
    result = subprocess.run([args.z3, '-in'], input=lifecycle, text=True, capture_output=True, timeout=15)
    assert result.returncode == 0 and not result.stderr
    objects = checker.parse(result.stdout)
    assert objects[0] == objects[-1] == 'sat' and objects[1][0] == 'ff-certificate-unavailable'
    check_both(source(7, ['(= x y)', '(= x (as ff0 F))', '(= y (as ff1 F))']), checker.sexpr(objects[2]))
    print('budget recovery, unsupported paths and root-only UNSAT correctly refuse certificates')


if __name__ == '__main__':
    main()
