#
# The following script synthesizes case analysis for bounds propagation with inequalities.
# There are two versions of the script: non-strict and strict inequality v <= w, v < w,
# respectively.
#
# It is used for code in src/math/polysat/fixplex_def.h
#

from z3 import *

nb = 12
v = BitVec("v", nb)
w = BitVec("w", nb)
i, j, k, l = BitVecs('lo(v) hi(v) lo(w) hi(w)', nb)

def in_bounds(x, i, j):
    return Or([And(ULT(i, j), ULE(i, x), ULT(x, j)),
               And(ULT(j, i), j != 0, ULE(i, x)),
               And(ULT(j, i), j != 0, ULT(x, j)),
               And(ULT(j, i), j == 0, ULE(i, x)),
               i == j])

def at_upper(x, i, j):
    return Or([i == j, x + 1 == j])
        
    
s = Solver()
s0 = Solver()
s1 = Solver()
s.add(in_bounds(v, i, j))
s.add(in_bounds(w, k, l))
s1.add(in_bounds(v, i, j))
s1.add(in_bounds(w, k, l))

s.set("core.minimize", True)
s1.set("core.minimize", True)

def add_def(name, p):
    b = Bool(name)
    s.add(b == p)
    s0.add(b == p)
    s1.add(b == p)
    return b

is_free_v = add_def("is_free(v)", i == j)
is_free_w = add_def("is_free(w)", k == l)
is_zero_lo_v = add_def("lo(v) == 0", i == 0)
is_zero_lo_w = add_def("lo(w) == 0", k == 0)
s.add(Implies(is_free_v, is_zero_lo_v))
s.add(Implies(is_free_w, is_zero_lo_w))
s0.add(Implies(is_free_v, is_zero_lo_v))
s0.add(Implies(is_free_w, is_zero_lo_w))
s1.add(Implies(is_free_v, is_zero_lo_v))
s1.add(Implies(is_free_w, is_zero_lo_w))

preds = [add_def("lo(v) <= hi(v)", ULE(i, j)),
         add_def("lo(w) <= hi(w)", ULE(k, l)),
         add_def("hi(v) <= lo(w)", ULE(j, k)),
         add_def("lo(w) <= hi(v)", ULE(k, j)),
         add_def("lo(v) <= lo(w)", ULE(i, k)),
         add_def("lo(w) <= lo(v)", ULE(k, i)),
         add_def("hi(w) <= lo(v)", ULE(l, i)),
         add_def("lo(v) <= hi(w)", ULE(i, l)),
         add_def("hi(w) <= hi(v)", ULE(l, j)),
         add_def("hi(v) <= hi(w)", ULE(j, l)),
         is_zero_lo_v,
         add_def("hi(v) == 0", j == 0),
         is_zero_lo_w,         
         add_def("hi(w) == 0", l == 0),
         add_def("hi(v) == 1", j == 1),
         add_def("hi(w) == 1", l == 1),
         add_def("is_fixed(v)", i + 1 == j),
         add_def("is_fixed(w)", k + 1 == l),
         add_def("lo(v) + 1 == hi(w)", i + 1 == l),
         add_def("lo(v) + 1 == 0", i + 1 == 0),
         is_free_v,
         is_free_w
         ]

def is_tight(s, core, x, lo, hi):
    s.push()
    s.add(core)
    s.add(Not(in_bounds(x, lo, hi)))
    r = s.check()
    s.pop()
    if unsat != r:
        return False
    s.push()
    s.add(core)
    s.add(x == lo)
    r = s.check()
    s.pop()
    if sat != r:
        return False
    s.push()
    s.add(core)
    s.add(x + 1 == hi, hi != lo)
    r = s.check()
    s.pop()
    if sat != r:
        return False
    #print(core, x, lo, hi)
    #print(core)
    #print(Not(in_bounds(x, lo, hi)))
    #print(s)
    return True

def is_tighter(s, core, x, lo1, hi1, lo2, hi2):
    s.push()
    s.add(core)
    s.add(in_bounds(x, lo1, hi1))
    s.add(Not(in_bounds(x, lo2, hi2)))
    r = s.check()
    s.pop()
    return r == unsat

def core2deps(core):
    deps = set([])
    for c in core:
        sc = f"{c}"
        if "lo(v)" in sc:
            deps |= { "vlo" }
        if "lo(w)" in sc:
            deps |= { "wlo" }
        if "hi(v)" in sc:
            deps |= { "vhi" }
        if "hi(w)" in sc:
            deps |= { "whi" }
        if "fixed(v)" in sc:
            deps |= { "vlo", "vhi" }
        if "fixed(w)" in sc:
            deps |= { "wlo", "whi" }
    deps = list(deps)
    sorted(deps)
    return ", ".join(deps)

def core2pred(core):
    return " && ".join([f"!({c.arg(0)})" if is_not(c) else f"{c}" for c in core ])
        

def propagate_bounds(core, x, lo, hi):
    deps = core2deps(core)
    sys.stdout.write("if (")
    sys.stdout.write(core2pred(core))
    sys.stdout.write(f" && !new_bound(i, {x}, {lo}, {hi}, {deps}))\n")
    sys.stdout.write("   return false;\n")
    sys.stdout.flush()

def propagate_conflict(core):
    deps = core2deps(core)
    sys.stdout.write("if (")
    sys.stdout.write(core2pred(core))
    sys.stdout.write(f")\n")
    sys.stdout.write(f"   return conflict(i, {deps}), false;\n")
    sys.stdout.flush()

lows  = [BitVecVal(0, nb), l, k, i, j, k + 1, i + 1]
highs = [BitVecVal(0, nb), l, k, i, j, l - 1, j - 1]

def find_new_bounds(s, core, x):
    bound = None
    for lo in lows:
        for hi in highs:
            if is_tight(s, core, x, lo, hi):
                if not bound:
                    bound = (lo, hi)
                else:
                    lo2, hi2 = bound
                    if is_tighter(s, core, x, lo, hi, lo2, hi2):
                        #print("tighter", lo, hi, lo2, hi2)
                        bound = (lo, hi)

    if bound:
        lo, hi = bound
        propagate_bounds(core, x, lo, hi)
    else:
        print("Could not find new bounds", x, lows, highs)
            



num_tries = 0
num_found = 0
num_nodes = 0

# set_param(verbose=2)

def explore(s, s0, ps):
    global num_tries
    global num_found    
    num_tries += 1
    r = s.check(ps)
    if r == unsat:
        core = s.unsat_core()
        propagate_conflict(core)
        s0.add(Not(And(core)))
        num_found += 1

        return

    found = False
    s.push()
    s.add(v == i)
    r = s.check(ps)
    if r == unsat:
        core = s.unsat_core()
        s0.add(Not(And(core)))
        found = True
    s.pop()
    if r == unsat:
        find_new_bounds(s, core, v)

    s.push()
    s.add(w == k)
    r = s.check(ps)
    if r == unsat:
        core = s.unsat_core()
        s0.add(Not(And(core)))
        found = True
    s.pop()
    if r == unsat:
        find_new_bounds(s, core, w)

    s.push()
    s.add(at_upper(v, i, j))
    r = s.check(ps)
    if r == unsat:
        core = s.unsat_core()
        s0.add(Not(And(core)))
        found = True
    s.pop()
    if r == unsat:
        find_new_bounds(s, core, v)

    s.push()
    s.add(at_upper(w, k, l))
    r = s.check(ps)
    if r == unsat:
        core = s.unsat_core()
        s0.add(Not(And(core)))
        found = True
    s.pop()
    if r == unsat:
        find_new_bounds(s, core, w)

    if found:
        num_found += 1
        

def search(s, s0, trail, preds):
    global num_nodes
    num_nodes += 1
    r = s0.check(trail)
    if r == unsat:
        return
    if len(preds) == 0:
        explore(s, s0, trail)
        return
    hd = preds[0]
    tl = preds[1:]
    search(s, s0, trail + [hd], tl)
    search(s, s0, trail + [Not(hd)], tl)

def create_bounds(p):
    global num_tries
    global num_found    
    global num_nodes    
    num_tries = 0
    num_found = 0
    num_nodes = 0    
    s0.push()
    s.push()
    s.add(p)
    search(s, s0, [], preds)
    s.pop()
    s0.pop()
    print("attempted predicates: ", num_tries, "predicates: ", num_found, "nodes: ", num_nodes)

def search_primal():
    print("strict")
    create_bounds(ULT(v, w))
    print("non-strict")
    create_bounds(ULE(v, w))

#search_primal()

def extract_predicates(s):
    for p in preds:
        r = s.check(p)
        if r == sat:
            yield p
        r = s.check(Not(p))
        if r == sat:
            yield Not(p)

def test_le(ineq, lov, hiv, low, hiw):
    if lov == hiv and lov > 0:
        return
    if low == hiw and low > 0:
        return
    s0.push()
    s0.add(i == lov)
    s0.add(j == hiv)
    s0.add(k == low)
    s0.add(l == hiw)
    r = s0.check()
    s0.pop()    
    if r == unsat:
        return
    s.push()    
    s.add(i == lov)
    s.add(j == hiv)
    s.add(k == low)
    s.add(l == hiw)
    r = s.check()
    assert r == sat
    
    preds = list(extract_predicates(s))
    s.add(ineq)
    if r == unsat:
        print("core", preds)
        s.pop()
        return

    def test_bound(x, p):
        s.push()
        s.add(p)
        r = s.check()        
        s.pop()
        if r == unsat:
            s1.push()
            s1.add(p)
            s1.add(ineq)
            r = s1.check(preds)
            if r == unsat:
                core = [c for c in s1.unsat_core()]
            else:
                print("Did not find core for lower bound v")
                print(lov, hiv, low, hiw)
                print(s1)
                for p in preds:
                    print(p)
            s1.pop()
            if r == unsat:
                s1.push()
                s1.add(ineq)
                r = s1.check(core)
                if r == unsat:
                    propagate_conflict(core)
                else:
                    find_new_bounds(s1, core, x)
                s1.pop()
                s0.add(Not(And(core)))

    test_bound(v, v == i)
    test_bound(w, w == k)
    test_bound(v, at_upper(v, i, j))
    test_bound(w, at_upper(w, k, l))
    s.pop()
    

bounds = [0, 1, 2, 3, 10, 2**nb - 3, 2**nb - 2, 2**nb - 1]

def search_dual_loop(p):
    for i in bounds:
        for j in bounds:
            for k in bounds:
                for l in bounds:
                    test_le(p, i, j, k, l)


def search_dual():
    s0.push()
    s1.push()
    print("strict")
    search_dual_loop(ULT(v, w))
    s0.pop()
    s1.pop()
    print("non-strict")
    search_dual_loop(ULE(v, w))

search_dual()
    

# Sketch v-next approach that 
# Maintain a transition relation T(B0, B1)
# where B := (lo(v), hi(v), lo(w), hi(w)) are variables.
# Initially T is B0 = B1
# Enumerate representative values of B0
#   Enumerate solutions for  T(B0, B1) given value for B0
#      Check if B & v < w and v = lo(v) is unsat (similar to w = lo(w), v = hi(v)-1, )
#      If it is unsat then find predicate cover P for B1
#      B1 |= P,
#      * P & v < w & not in_bounds(v, lo(v)', hi(v)') is unsat
#        where lo(v)', hi(v)' is a tightest bound under B1
#        Update T by adding transition (P => B2 = lo(v)', hi(v)', lo(w), hi(w)) & (~P => B2 = B1)
#      * P & v < w is unsat
#        Update T by adding not P
#
