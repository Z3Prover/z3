"""Soundness checks for repeated no-wrap reasoning and shared polynomial tails."""
import itertools
from z3 import *


def layered():
    """The second no-wrap equality becomes visible only after first-layer aliases."""
    p = 21888242871839275222246405745257275088548364400416034343698204186575808495617
    field = FiniteFieldSort(p)
    left, right = Consts('layer_input_left layer_input_right', field)
    constraints = [left == right]
    for layer in range(3):
        outputs = []
        for side, value in enumerate([left, right]):
            digits = [Const(f'digit_{layer}_{side}_{i}', field) for i in range(4)]
            constraints += [b*b == b for b in digits]
            constraints.append(value == Sum([2**i*b for i, b in enumerate(digits)]))
            output = Const(f'layer_output_{layer}_{side}', field)
            constraints.append(output == (digits[0]+2*digits[1])*(digits[2]+2*digits[3]))
            outputs.append(output)
        left, right = outputs
    solver = Tactic('ff-solve').solver()
    solver.set(**{'ff.max_steps': 100000})
    solver.add(constraints+[left != right])
    assert solver.check() == unsat
    assert solver.statistics().get_key_value('ff bit rounds') >= 2


def main():
    layered()
    checked=0
    for p in [3,5,7,17]:
        f=FiniteFieldSort(p)
        a,b,c,d,x,y=FiniteFieldElems('a b c d x y',f)
        domains=[v*v==v for v in [a,b,c,d]]
        for scale in [1,2,p-1]:
            equations=[scale*(a+2*b-x*y)==0,scale*(c+2*d-x*y)==0]
            query=domains+equations+[a!=c]
            # Independent enumeration of the four Boolean digits and shared
            # product (every field value is achievable by x=1, y=value).
            expected=any((aa+2*bb-cc-2*dd)%p==0 and aa!=cc
                         for aa,bb,cc,dd in itertools.product([0,1],repeat=4))
            for enabled in [False, True]:
                s=SolverFor('QF_FF');s.set(**{'ff.bit_propagation':enabled})
                s.add(query);result=s.check();assert result==(sat if expected else unsat),(p,scale,result)
                if result==sat:assert all(is_true(s.model().eval(q,model_completion=True)) for q in query)
                checked+=1
        # A missing Boolean premise permits a non-binary modular packing.
        s=SolverFor('QF_FF');s.add(domains[:3]+[a+2*b==c+2*d,a!=c])
        expected=any((aa+2*bb-cc-2*dd)%p==0 and aa!=cc for aa,bb,cc in itertools.product([0,1],repeat=3) for dd in range(p))
        assert s.check()==(sat if expected else unsat)
        # Tracked provenance must still be sufficient for the contradiction.
        if p>=5:
            s=SolverFor('QF_FF');s.set(unsat_core=True)
            query=domains+[a+2*b==x*y,c+2*d==x*y,a!=c]
            for i,q in enumerate(query):s.assert_and_track(q,Bool('tag'+str(i)))
            assert s.check()==unsat
            chosen=[int(str(q)[3:]) for q in s.unsat_core()]
            for vals in itertools.product(range(p),repeat=4):
                aa,bb,cc,dd=vals
                for product in range(p):
                    truth=[v*v%p==v for v in vals]+[(aa+2*bb-product)%p==0,(cc+2*dd-product)%p==0,aa!=cc]
                    assert not all(truth[i] for i in chosen),(p,chosen,vals,product)
            checked+=1
    print('bit propagation:',checked,'solver checks plus exhaustive core verification')


if __name__=='__main__':main()
