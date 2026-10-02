#!/usr/bin/env python3
"""Check standalone field rewriting independently of solver search."""
import itertools
import random
from z3 import (FiniteFieldSort, FiniteFieldElems, FiniteFieldVal, FiniteFieldBitsum,
                simplify, eq, is_true, is_false, substitute, parse_smt2_string,
                Goal, Then, Solver, sat, Context, Tactic, Z3Exception)
from test_qfff import generate


def main():
    f = FiniteFieldSort(13); x,y = FiniteFieldElems('x y',f)
    for term, expected in [(x+0,x),(x*1,x),(x*0,FiniteFieldVal(0,f)),(-(-x),x),
                           (x-x,FiniteFieldVal(0,f)),(2*x+3*x,5*x),
                           ((2*x)*7,x),((x+y)-(y+x),FiniteFieldVal(0,f))]:
        assert eq(simplify(term), simplify(expected)), (term,simplify(term),expected)
    assert is_true(simplify(x+3==x+16))
    assert is_false(simplify(x+3==x+4))
    assert eq(simplify(3*x+2==5),x==1)
    assert eq(simplify(2*x+y==x+y+3),x==3)
    # Cancellation of an unknown multiplicative factor would be unsound at x=0.
    formula = simplify(x*y==x*3)
    assert is_true(simplify(substitute(formula,(x,FiniteFieldVal(0,f)),(y,FiniteFieldVal(7,f)))))
    # Positional bitsum must retain zero operands and their places.
    assert simplify(substitute(FiniteFieldBitsum(FiniteFieldVal(0,f),x),(x,FiniteFieldVal(3,f)))).as_long()==6
    goal=Goal();goal.add(x==2,y==x+3)
    result=Then('ff-simplify','ff-solve')(goal)[0]
    solver=Solver();assert solver.check()==sat
    model=result.convert_model(solver.model())
    assert model.eval(x).as_long()==2 and model.eval(y).as_long()==5
    proof_context=Context(proof=True);pf=FiniteFieldSort(7,proof_context);a=FiniteFieldElems('a',pf)[0]
    pg=Goal(proofs=True,ctx=proof_context);pg.add(a*a==3)
    try: Tactic('ff-simplify',ctx=proof_context)(pg)
    except Z3Exception as e: assert 'certificates' in str(e)
    else: raise AssertionError('proof-producing preprocessing accepted')
    checked=0;rng=random.Random(4469)
    for prime in [2,3,5,7,17]:
        f=FiniteFieldSort(prime);x,y=FiniteFieldElems('x y',f)
        for _ in range(60):
            text,oracle=generate(rng,prime)
            original=parse_smt2_string(f'(define-sort F () (_ FiniteField {prime}))(declare-const x F)(declare-const y F)(assert {text})')[0]
            reduced=simplify(original)
            assert eq(simplify(reduced),reduced),('not idempotent',original,reduced,simplify(reduced))
            for a,b in itertools.product(range(prime),repeat=2):
                value=simplify(substitute(reduced,(x,FiniteFieldVal(a,f)),(y,FiniteFieldVal(b,f))))
                assert is_true(value)==bool(oracle(a,b)) and (is_true(value) or is_false(value)),(prime,text,reduced,a,b,value)
                checked+=1
    print(f'Symbolic identities, constant propagation, reconstructed models, proof rejection and {checked} exhaustive rewrite evaluations passed')


if __name__=='__main__':main()
