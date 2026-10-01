#!/usr/bin/env python3
"""QF_FF semantic tests: independent enumeration, cvc5 comparison, and APIs.
Run with PYTHONPATH=build-ff-cmake/python python3 tests/finite_field/test_qfff.py
  --z3 build-ff-cmake/z3 --cvc5 /path/to/field-enabled/cvc5
"""
import argparse
import itertools
import random
import re
import subprocess
from pathlib import Path


def run(binary, text, timeout=15):
    cmd = [str(binary), '-in'] if Path(binary).name.startswith('z3') else [str(binary), '--lang=smt2', '--incremental']
    r = subprocess.run(cmd, input=text, text=True, capture_output=True, timeout=timeout)
    if r.returncode or '(error' in r.stdout or 'error' in r.stderr.lower():
        raise AssertionError((cmd, text, r.stdout, r.stderr))
    return r.stdout


def problem(p, formula):
    return f'''(set-logic QF_FF)
(define-sort F () (_ FiniteField {p}))
(declare-const x F)
(declare-const y F)
(assert {formula})
(check-sat)
'''


def generate(rng, p):
    def term(depth):
        if depth == 0 or rng.random() < .3:
            name = rng.choice(['x', 'y', str(rng.randrange(-2*p, 2*p))])
            if name == 'x': return ('x', lambda x,y: x)
            if name == 'y': return ('y', lambda x,y: y)
            n = int(name)
            return (f'(as ff{n} F)', lambda x,y: n % p)
        a, fa = term(depth-1)
        if rng.random() < .2: return (f'(ff.neg {a})', lambda x,y: -fa(x,y)%p)
        b, fb = term(depth-1)
        if rng.random() < .15:
            return (f'(ite (= x y) {a} {b})', lambda x,y: fa(x,y) if x==y else fb(x,y))
        op = rng.choice(['add','mul','bitsum'])
        return (f'(ff.{op} {a} {b})', lambda x,y: (fa(x,y)*fb(x,y) if op=='mul' else fa(x,y)+(2 if op=='bitsum' else 1)*fb(x,y))%p)
    def atom():
        a,fa=term(2); b,fb=term(2)
        neq=rng.random()<.35
        s=f'(= {a} {b})'
        return (f'(not {s})' if neq else s, lambda x,y: (fa(x,y)==fb(x,y)) != neq)
    a,fa=atom(); b,fb=atom()
    op=rng.choice(['and','and','or','=>','xor'])
    return f'({op} {a} {b})', lambda x,y: {'and':lambda:fa(x,y) and fb(x,y),'or':lambda:fa(x,y) or fb(x,y),'=>':lambda:not fa(x,y) or fb(x,y),'xor':lambda:fa(x,y)!=fb(x,y)}[op]()


def semantic_tests(args):
    rng=random.Random(9017)
    count=0
    native_count=0
    for p in [2,3,5,7,17]:
        for i in range(args.cases):
            formula, evaluate=generate(rng,p)
            expected='sat' if any(evaluate(x,y) for x,y in itertools.product(range(p),repeat=2)) else 'unsat'
            smt=problem(p,formula)
            for binary in [args.z3]+([args.cvc5] if args.cvc5 else []):
                out=run(binary,smt).strip()
                assert out==expected,(p,i,expected,out,smt)
            if expected=='sat':
                for check in ['(check-sat)','(check-sat-using (then ff2bv qfbv))']:
                    model_text=run(args.z3,smt.replace('(check-sat)',check)+'(get-value (x y))\n')
                    values=[int(v)%p for v in re.findall(r'\(as ff(-?\d+) ',model_text)]
                    assert len(values)==2 and evaluate(*values),('invalid model',values,smt,model_text)
            # Exercise the complete encoder even when algebra can solve the case.
            out=run(args.z3,smt.replace('(check-sat)','(check-sat-using (then ff2bv qfbv))')).strip()
            assert out==expected,('ff2bv',expected,out,smt)
            for tactic in ['ff-solve','ff-sat']:
                out=run(args.z3,smt.replace('(check-sat)',f'(check-sat-using {tactic})')).strip()
                assert out in [expected,'unknown'],(tactic,expected,out,smt)
                native_count += out==expected
            count+=1
    for p in [3,7,11,19,23,31]:
        # No root in the prime field even though roots exist in its algebraic closure.
        smt=problem(p,'(= (ff.mul x x) (as ff-1 F))')
        assert run(args.z3,smt).strip()=='unsat'
    print(f'{native_count} successful native tactic checks')
    print(f'{count} random formulas checked against exhaustive enumeration'+(' and cvc5' if args.cvc5 else ''))


def api_tests():
    from z3 import (FiniteFieldSort,FiniteFieldVal,FiniteFieldElems,FiniteFieldBitsum,
                    SolverFor,Solver,Context,Tactic,Goal,Then,Bool,If,Or,And,Distinct,
                    simplify,sat,unsat,unknown,Z3Exception,parse_smt2_string)
    F=FiniteFieldSort(13)
    x,y=FiniteFieldElems('x y',F)
    assert F.size()==13 and FiniteFieldVal(-14,F).as_long()==12
    assert simplify(FiniteFieldVal(12,F)*12).as_long()==1
    assert simplify(FiniteFieldBitsum(FiniteFieldVal(1,F),2,3)).as_long()==4
    for factory in [lambda:SolverFor('QF_FF'),Solver]:
        s=factory(); s.add(x+y==1,x*y==1)
        assert s.check()==sat
        model=s.model()
        assert model.eval(x+y).as_long()==1 and model.eval(x*y).as_long()==1
        assert model.eval(And(x+y==1,x*y==1)) == True
        s.push(); s.add(x==2); assert s.check()==unsat; s.pop(); assert s.check()==sat
        assert s.check(x==2)==unsat
        assert s.check(x==4)==sat
        s2=s.translate(Context()); assert s2.check()==sat
        limited=factory();limited.add(x*x==3);limited.set(rlimit=1)
        assert limited.check()==unknown
        limited.set(rlimit=0);assert limited.check()==sat
        assert limited.model().eval(x*x).as_long()==3
    for p in [2,3,5,7,17,257]:
        f=FiniteFieldSort(p); a,b=FiniteFieldElems('a b',f)
        s=SolverFor('QF_FF'); s.add(a==p-1,b==p-1,a*b!=1); assert s.check()==unsat
        s=SolverFor('QF_FF'); s.add(a==p-1,b==p-1,a+b!=p-2); assert s.check()==unsat
    s=SolverFor('QF_FF'); s.add(If(Bool('choice'),x,y)==3, x==4, y==3); assert s.check()==sat
    assert s.model().eval(If(Bool('choice'),x,y)).as_long()==3
    s=SolverFor('QF_FF'); s.set(unsat_core=True)
    a,b=Bool('a'),Bool('b');s.assert_and_track(x==2,a);s.assert_and_track(x==3,b)
    assert s.check()==unsat and len(s.unsat_core())==2
    G=FiniteFieldSort(7);z=FiniteFieldElems('z',G)[0]
    s=SolverFor('QF_FF');s.add(x*x==3,z*z==2); assert s.check()==sat
    for bad in [0,1,4,9,15,341,561,3215031751,3825123056546413051]:
        try: FiniteFieldSort(bad)
        except Z3Exception: pass
        else: raise AssertionError(('accepted composite',bad))
    try: simplify(x+z)
    except Z3Exception: pass
    else: raise AssertionError('mixed fields accepted')
    try: FiniteFieldVal('1/2',F)
    except Z3Exception: pass
    else: raise AssertionError('fraction accepted')
    # Tactic model conversion and context translation retain field values.
    goal=Goal();goal.add(x+y==1,x*y==1)
    sub=Then('ff2bv','qfbv')(goal)[0]
    empty=Solver();assert empty.check()==sat
    converted=sub.convert_model(empty.model())
    assert converted.eval(x*y).as_long()==1
    for p in [21888242871839275222246405745257275088548364400416034343698204186575808495617,
              52435875175126190479447740508185965837690552500527637822603658699938581184513]:
        f=FiniteFieldSort(p);a,b=FiniteFieldElems('a b',f)
        s=SolverFor('QF_FF');s.add(7*a==3,b==a*a);assert s.check()==sat
        mdl=s.model();assert (7*mdl[a].as_long())%p==3 and mdl[b].as_long()==pow(mdl[a].as_long(),2,p)
        s=SolverFor('QF_FF');s.add(a*a==4,a!=2,a!=-2);assert s.check()==unsat
    # Bit-decomposition shortcuts require every bit and a no-wrap range.
    f=FiniteFieldSort(3);a,b,c,d=FiniteFieldElems('a b c d',f)
    s=SolverFor('QF_FF');s.add(a*a==a,b*b==b,c*c==c,d*d==d,
        FiniteFieldBitsum(a,b)==FiniteFieldBitsum(c,d),a==1,b==1,c==0,d==0)
    assert s.check()==sat
    f=FiniteFieldSort(17);a,b=FiniteFieldElems('a b',f)
    s=SolverFor('QF_FF');s.add(a*a==a,FiniteFieldBitsum(a,b)==0,a==1)
    assert s.check()==sat and s.model()[b].as_long()==8
    s=SolverFor('QF_FF');s.add(a*a==a,b*b==b,FiniteFieldBitsum(a,b)==4)
    assert s.check()==unsat
    s=SolverFor('QF_FF');s.set(**{'ff.max_steps':1});s.add(x*x==3);assert s.check()==sat
    s=SolverFor('QF_FF');s.add(Or(x*x==3,x*x==4),x!=2,x!=-2)
    assert s.check()==sat
    # Round-trip full-width moduli through SMT-LIB and model evaluation.
    for prime in [2147483647,4294967291,2**61-1,2**127-1]:
        f=FiniteFieldSort(prime);a=FiniteFieldElems('a',f)[0]
        s=SolverFor('QF_FF');s.add(a+1==0)
        text=s.to_smt2();other=SolverFor('QF_FF');other.add(parse_smt2_string(text))
        assert other.check()==sat and other.model()[a].as_long()==prime-1
    pctx=Context(proof=True);pf=FiniteFieldSort(7,pctx);a=FiniteFieldElems('a',pf)[0]
    s=SolverFor('QF_FF',pctx);s.add(a*a==3);assert s.check()==unknown
    assert 'certificates' in s.reason_unknown()
    print('API, models, incrementality, cores, contexts, resource limits, invalid inputs, large primes and proof rejection passed')


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--z3',default='build-ff-cmake/z3');parser.add_argument('--cvc5');parser.add_argument('--cases',type=int,default=30)
    args=parser.parse_args()
    semantic_tests(args)
    for smt in [problem(13,'(= x #f-14m13)'),problem(13,'(= x (as ff-14 F))')]:
        assert run(args.z3,smt).strip()=='sat'
    api_tests()

if __name__=='__main__':main()
