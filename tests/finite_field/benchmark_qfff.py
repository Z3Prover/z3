#!/usr/bin/env python3
"""Reproducible synthetic ZK-gadget benchmarks (not a production circuit suite)."""
import argparse
import json
import statistics
import subprocess
import time
from pathlib import Path

FIELDS={
 'bn254':21888242871839275222246405745257275088548364400416034343698204186575808495617,
 'bls12_381_scalar':52435875175126190479447740508185965837690552500527637822603658699938581184513,
}

def benchmark_cases(p):
    pre=f'(set-logic QF_FF)\n(define-sort F () (_ FiniteField {p}))\n'
    def val(n):return f'(as ff{n%p} F)'
    for n in [16,64,256,1024]:
        lines=[pre]+[f'(declare-const x{i} F)' for i in range(n+1)]
        lines.append(f'(assert (= x0 {val(7)}))');value=7
        for i in range(n):
            lines.append(f'(assert (= x{i+1} (ff.add (ff.mul {val(i+2)} x{i}) {val(11)})))')
            value=((i+2)*value+11)%p
        for wrong in [False,True]:
            yield f'linear_{n}_{"unsat" if wrong else "sat"}', '\n'.join(lines+[f'(assert (= x{n} {val(value+wrong)}))','(check-sat)']), 'unsat' if wrong else 'sat'
    for n in [8,32,128,512]:
        lines=[pre]+[f'(declare-const x{i} F)' for i in range(n+1)]
        lines.append(f'(assert (= x0 {val(7)}))');value=7
        for i in range(n):
            t=f'(ff.add x{i} {val(i+1)})'
            lines.append(f'(assert (= x{i+1} (ff.mul {t} {t} {t} {t} {t})))')
            value=pow(value+i+1,5,p)
        for wrong in [False,True]:
            yield f'power5_chain_{n}_{"unsat" if wrong else "sat"}', '\n'.join(lines+[f'(assert (= x{n} {val(value+wrong)}))','(check-sat)']), 'unsat' if wrong else 'sat'
    for rounds in [8,32]:
        lines=[pre]+[f'(declare-const x{r}_{j} F)' for r in range(rounds+1) for j in range(3)]
        state=[1,2,3]
        for j in range(3):lines.append(f'(assert (= x0_{j} {val(state[j])}))')
        for r in range(rounds):
            nonlinear=[]
            for j in range(3):
                t=f'(ff.add x{r}_{j} {val(3*r+j+1)})'
                nonlinear.append(f'(ff.mul {t} {t} {t} {t} {t})')
            next_values=[pow(state[j]+3*r+j+1,5,p) for j in range(3)]
            state=[(sum(next_values)+next_values[j])%p for j in range(3)]
            for j in range(3):
                terms=' '.join(f'(ff.mul {val(2 if j==k else 1)} {nonlinear[k]})' for k in range(3))
                lines.append(f'(assert (= x{r+1}_{j} (ff.add {terms})))')
        for wrong in [False,True]:
            yield f'sbox_mds_{rounds}_{"unsat" if wrong else "sat"}', '\n'.join(lines+[f'(assert (= x{rounds}_0 {val(state[0]+wrong)}))','(check-sat)']), 'unsat' if wrong else 'sat'
    yield 'symbolic_square_identity',pre+f'''
(declare-const x F)(declare-const y F)
(assert (distinct (ff.mul (ff.add x y) (ff.add x y))
 (ff.add (ff.mul x x) (ff.mul {val(2)} x y) (ff.mul y y))))
(check-sat)''','unsat'
    yield 'inverse_zero',pre+f'(declare-const x F)(declare-const y F)(assert (= (ff.mul x y) {val(1)}))(assert (= x {val(0)}))(check-sat)','unsat'
    for n in [8,32,128]:
        lines=[pre]
        for name in ['a','b']:
            for i in range(n):
                lines += [f'(declare-const {name}{i} F)',f'(assert (= (ff.mul {name}{i} {name}{i}) {name}{i}))']
        left=' '.join(f'a{i}' for i in range(n));right=' '.join(f'b{i}' for i in range(n))
        lines += [f'(assert (= (ff.bitsum {left}) (ff.bitsum {right})))','(assert (distinct a0 b0))','(check-sat)']
        yield f'bitsum_injective_{n}','\n'.join(lines),'unsat'
    for n in [8,32,128]:
        lines=[pre]
        for i in range(n):lines += [f'(declare-const b{i} F)',f'(assert (= (ff.mul b{i} b{i}) b{i}))']
        bits=' '.join(f'b{i}' for i in range(n))
        lines += [f'(assert (= (ff.bitsum {bits}) {val(37)}))','(check-sat)']
        yield f'bitsum_value_{n}','\n'.join(lines),'sat'
    # Nontrivial quadratic root extraction at cryptographic field sizes.
    yield 'square_roots_excluded',pre+f'(declare-const x F)(assert (= (ff.mul x x) {val(4)}))(assert (distinct x {val(2)} {val(-2)}))(check-sat)','unsat'


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--z3',default='build-ff-cmake/z3');ap.add_argument('--cvc5',required=True);ap.add_argument('--out',default='tests/finite_field/results');ap.add_argument('--timeout',type=float,default=10);ap.add_argument('--repeat',type=int,default=3);ap.add_argument('--filter',default='')
    args=ap.parse_args();out=Path(args.out);out.mkdir(parents=True,exist_ok=True)
    rows=[]
    for field,p in FIELDS.items():
        for name,smt,expected in benchmark_cases(p):
            case=f'{field}_{name}'
            if args.filter and args.filter not in case:continue
            (out/(case+'.smt2')).write_text(smt+'\n')
            row={'case':case,'expected':expected}
            for label,cmd in [('z3',[args.z3,'-in']),('cvc5',[args.cvc5,'--lang=smt2']),('cvc5_split',[args.cvc5,'--lang=smt2','--ff-solver=split'])]:
                times=[];answer=''
                for _ in range(args.repeat):
                    start=time.perf_counter()
                    try:
                        r=subprocess.run(cmd,input=smt,text=True,capture_output=True,timeout=args.timeout)
                        answer=r.stdout.strip();times.append(time.perf_counter()-start)
                        if r.returncode or answer!=expected:raise AssertionError((case,cmd,answer,r.stderr))
                    except subprocess.TimeoutExpired:answer='timeout';break
                row[label]={'result':answer,'seconds':statistics.median(times) if answer!='timeout' else args.timeout}
            rows.append(row);print(json.dumps(row),flush=True)
            (out/'results.json').write_text(json.dumps(rows,indent=2)+'\n')
    versions={name:subprocess.check_output([binary,'--version'],text=True).splitlines()[0] for name,binary in [('z3',args.z3),('cvc5',args.cvc5)]}
    (out/'versions.json').write_text(json.dumps(versions,indent=2)+'\n')

if __name__=='__main__':main()
