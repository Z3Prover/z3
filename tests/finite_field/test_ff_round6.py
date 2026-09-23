"""Independent semantic and provenance checks for round-six experiments."""
import itertools
import random
from z3 import *

FLAGS = ['linear_split', 'basis_bits', 'compact_matrix', 'model_search', 'bit_bounds']


def algebra_solver(flags):
    s = Tactic('ff-solve').solver()
    # Flags describe an isolated experiment, not additions to whichever
    # model-search default a future solver release happens to adopt.
    s.set(**{'ff.model_search': 'model_search' in flags})
    s.set(**{'ff.'+k: True for k in flags}, **{'ff.sparse_witness': False, 'ff.enum_bits': 0})
    return s


def random_systems():
    rng = random.Random(619923)
    count = 0
    stats = {}
    for p in [2, 3, 5, 7, 11]:
        field = FiniteFieldSort(p)
        xs = Consts('r6_x r6_y r6_z', field)
        points = list(itertools.product(range(p), repeat=3))
        for trial in range(24):
            specs=[]; constraints=[]
            for i in range(rng.randrange(2, 6)):
                terms=[(rng.randrange(1,p),tuple(rng.randrange(3) for _ in range(rng.randrange(4)))) for _ in range(rng.randrange(2,6))]
                different=rng.randrange(6)==0
                e=FiniteFieldVal(0,field)
                for c,mon in terms:
                    t=FiniteFieldVal(c,field)
                    for j in mon:t*=xs[j]
                    e+=t
                constraints.append(e!=0 if different else e==0);specs.append((terms,different))
            def holds(point,indices):
                for i in indices:
                    terms,different=specs[i];v=0
                    for c,mon in terms:
                        for j in mon:c*=point[j]
                        v+=c
                    if (v%p!=0)!=different:return False
                return True
            expected=sat if any(holds(pt,range(len(specs))) for pt in points) else unsat
            for flags in [FLAGS, ['compact_matrix'], ['model_search']]:
                s=SolverFor('QF_FF');s.set(unsat_core=True, **{"ff."+k:True for k in flags})
                s.set(**{'ff.model_search': 'model_search' in flags})
                for i,q in enumerate(constraints):s.assert_and_track(q,Bool('r6_tag'+str(i)))
                answer=s.check();assert answer==expected,(p,trial,flags,answer,expected,s.reason_unknown())
                if answer==sat:assert all(is_true(s.model().eval(q,model_completion=True)) for q in constraints)
                else:
                    selected=[int(str(v).removeprefix('r6_tag')) for v in s.unsat_core()]
                    assert not any(holds(pt,selected) for pt in points),(p,trial,selected)
                for k,v in s.statistics():
                    if k.startswith('ff '):stats[k]=stats.get(k,0)+v
                count+=1
    assert stats.get('ff matrix batches',0)>0
    print(count,'enumerated random systems and cores;',stats,flush=True)


def bit_bounds():
    rng=random.Random(934192)
    count=0
    for p in [3,5,7,17,65537]:
        f=FiniteFieldSort(p);xs=Consts('bound_a bound_b bound_c bound_d',f)
        for trial in range(32):
            weights=[rng.randrange(-12,13) for _ in xs];offset=rng.randrange(-20,21)
            expected=any((sum(c*v for c,v in zip(weights,pt))+offset)%p==0 for pt in itertools.product([0,1],repeat=4))
            qs=[x*x==x for x in xs]+[Sum([c*x for c,x in zip(weights,xs)])+offset==0]
            s=algebra_solver(FLAGS);s.add(qs)
            assert s.check()==(sat if expected else unsat),(p,weights,offset)
            if expected:assert all(is_true(s.model().eval(q,model_completion=True)) for q in qs)
            count+=1
        # Dropping a Boolean premise must permit non-binary digits and modular wraps.
        s=algebra_solver(FLAGS);s.add(xs[0]*xs[0]==xs[0],xs[0]+2*xs[1]==0,xs[0]==1)
        assert s.check()==sat
    f=FiniteFieldSort(17);a,b=Consts('bound_pinned_a bound_pinned_b',f)
    s=algebra_solver(['bit_bounds']);s.add(a*a==a,b*b==b,a+3*b==0)
    assert s.check()==sat
    assert s.statistics().get_key_value('ff bound facts') >= 2
    print(count,'signed Boolean interval/wrap checks and missing-domain cases',flush=True)


def interval_cores():
    for p in [7,17,65537]:
        f=FiniteFieldSort(p);a,b=Consts('interval_core_a interval_core_b',f)
        for solver in [SolverFor('QF_FF'),SimpleSolver()]:
            solver.set(unsat_core=True, **{'ff.bit_bounds':True, 'ff.model_search':False})
            for name,q in [('a_domain',a*a==a),('b_domain',b*b==b),('sum',a+b+1==0)]:
                solver.assert_and_track(q,Bool(name))
            assert solver.check()==unsat
            assert set(map(str,solver.unsat_core()))=={'a_domain','b_domain','sum'}
    print('interval deductions retain both Boolean premises in unsat cores',flush=True)


def unequal_widths():
    for p in [3,5,7,17,65537]:
        f=FiniteFieldSort(p);a,b,c,d,e=Consts('width_a width_b width_c width_d width_e',f)
        qs=[x*x==x for x in [a,b,c,d,e]]+[a+2*b==c+2*d+4*e,a!=c]
        expected=any((aa+2*bb-cc-2*dd-4*ee)%p==0 and aa!=cc for aa,bb,cc,dd,ee in itertools.product([0,1],repeat=5))
        s=algebra_solver(['basis_bits']);s.add(qs);assert s.check()==(sat if expected else unsat)
    print('unequal-width bit encodings including non-injective small fields',flush=True)


def disjunctions():
    for p in [2,3,7,17,65537]:
        f=FiniteFieldSort(p);x,y=Consts('disj_x disj_y',f)
        for affine in [False,True]:
            q=Or(x==0,x==1) if not affine else Or(0==-x,0==x-1)
            for value in range(min(p,4)):
                g=Goal();g.add(q,y==x,y==value)
                t=With(Tactic('ff-simplify'), **{'ff.disjunctive_bits':True})
                result=t(g)
                s=algebra_solver(FLAGS);s.add(result.as_expr())
                assert s.check()==(sat if value in [0,1] else unsat)
        # Exporters often name 0 and -1. Constant propagation must precede
        # recognizing the disjunctive domain, otherwise its three leaves hide it.
        zero, minus = Consts('disj_zero disj_minus',f)
        g=Goal();g.add(zero==0,minus==-1,Or(zero==x+minus,zero==x))
        result=With(Tactic('ff-simplify'), **{'ff.disjunctive_bits':True})(g)
        assert not any(is_or(q) for q in result[0]), result
        # Rewrite must preserve dependency cores across assumptions.
        set_param('smt.ff.disjunctive_bits',True)
        s=SolverFor('QF_FF');s.set(unsat_core=True)
        s.assert_and_track(Or(x==0,x==1),Bool('domain'))
        s.assert_and_track(x!=0,Bool('nz'));s.assert_and_track(x!=1,Bool('no'))
        assert s.check()==unsat
        assert set(map(str,s.unsat_core()))=={'domain','nz','no'}
        set_param('smt.ff.disjunctive_bits',False)
    print('disjunctive domains, affine spellings and tracked cores',flush=True)


if __name__=='__main__':
    random_systems();bit_bounds();interval_cores();unequal_widths();disjunctions()
    import test_ff_general_algebra
    set_param('smt.ff.compact_matrix',True)
    test_ff_general_algebra.word_boundary()
    set_param('smt.ff.compact_matrix',False)
