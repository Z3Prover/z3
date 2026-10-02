#!/usr/bin/env python3
"""Contextual field preprocessing: guarded zero tests, cores, DAGs and bit search."""
import itertools
from z3 import *


def verify(formulas, expected, tracked=False):
    solver = SolverFor('QF_FF')
    if tracked:
        solver.set(unsat_core=True)
        for i, f in enumerate(formulas): solver.assert_and_track(f, Bool(f'premise_{i}'))
    else: solver.add(formulas)
    assert solver.check() == expected, (formulas, solver.reason_unknown())
    if expected == sat:
        model = solver.model()
        assert all(is_true(model.eval(f, model_completion=True)) for f in formulas), (formulas, model)
    elif tracked:
        core = [int(str(x).split('_')[-1]) for x in solver.unsat_core()]
        assert core
        return core


def main():
    checked = 0
    for p in [2,3,5,7,17]:
        f = FiniteFieldSort(p)
        x,z,u,w,v,a = FiniteFieldElems('x z u w v a',f)
        for nonzero in [False,True]:
            for scale in [1,p-1]:
                definitions = [z==scale*x*u if nonzero else z==1-scale*x*u,
                               w==x*v if nonzero else w==1-x*v]
                guards = [x*(1-z)==0 if nonzero else x*z==0,
                          x*(1-w)==0 if nonzero else x*w==0]
                formulas = definitions+guards+[z!=w]
                core = verify(formulas,unsat,True)
                # Omitting either kind of premise must not manufacture uniqueness.
                for omit in range(4): verify([q for i,q in enumerate(formulas) if i!=omit],sat)
                if p <= 7:
                    for xv,zv,uv,wv,vv in itertools.product(range(p),repeat=5):
                        zs = scale*xv*uv%p; ws=xv*vv%p
                        vals=[zv==(zs if nonzero else (1-zs)%p),
                              wv==(ws if nonzero else (1-ws)%p),
                              xv*((1-zv) if nonzero else zv)%p==0,
                              xv*((1-wv) if nonzero else wv)%p==0,zv!=wv]
                        assert not all(vals[i] for i in core),(p,nonzero,scale,core,vals)
                # Composite inputs and arbitrary scaling are not variable-name rules.
                verify([z==1-scale*x*a*u,w==1-x*a*v,x*a*z==0,x*a*w==0,z!=w],unsat)
                checked += 1
        # Repeated/cyclic occurrences must not hide an acyclic definition.
        g=Goal();g.add(x==x*z+a)
        r=Tactic('simplify')(g)[0]
        assert any(is_eq(q) and (eq(q.arg(0),a) or eq(q.arg(1),a)) for q in r)
        verify([x*x==x,z*z==z,x+2*z==2],sat)
        expected = sat if any((a+2*b-2)%p==0 and a!=0 for a,b in itertools.product([0,1],repeat=2)) else unsat
        verify([x*x==x,z*z==z,x+2*z==2,x!=0],expected)
        # A missing Booleanity guard leaves z free, including values beyond 1.
        if p > 3: verify([x*x==x,x==1,x+2*z==0],sat)
    # Circuit equivalence with different multiplication schedules and model restoration.
    f=FiniteFieldSort(101);x,a,b,c,d,y,z=FiniteFieldElems('x a b c d y z',f)
    verify([a==x*x,b==a*a,y==b*x,c==a*x,z==c*a,y!=z],unsat,True)
    verify([a==x*x,b==a*a,y==b*x,c==a*x,z==c*a],sat)
    # Exhaustive small bit domain: no solution, with a core carrying both guards.
    f=FiniteFieldSort(17);x,y=FiniteFieldElems('x y',f)
    core=verify([x*x==x,y*y==y,x+2*y==4],unsat,True)
    assert set(core)=={0,1,2}
    # Preserve alternative Booleanity syntax through wire elimination too.
    bits=FiniteFieldElems('b0 b1 b2 b3',f);out=FiniteFieldElem('out',f)
    for guards in [[b*(b-1)==0 for b in bits],[b*b-b==0 for b in bits]]:
        verify(guards+[out==5,Sum([2**i*b for i,b in enumerate(bits)])==out],sat)
        verify(guards+[out==16,Sum([2**i*b for i,b in enumerate(bits)])==out],unsat,True)
    # Cyclic definitions must remain constraints, including alongside a pure wire.
    z=FiniteFieldElem('z',f)
    verify([x==y+1,y==x+1,z==x*x],unsat,True)
    verify([x==y+1,y==x-1,z==x*x],sat)
    verify([z==x*x,y==x-1,x==y+1],sat)
    print(f'{checked} guarded zero/nonzero-test families, missing premises, exhaustive cores, circuit models and bit-domain cases passed')


if __name__=='__main__': main()
