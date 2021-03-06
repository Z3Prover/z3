#
# Unweighted hitting set maxsat solver.
# interleaved with local hill-climbing improvements
#

from z3 import *
import random


                
class Soft:
    def __init__(self, soft):
        self.formulas = soft
        self.name2formula = { Bool(f"s{s}") : s for s in soft }
        self.formula2name = { s : v for (v, s) in self.name2formula.items() }


def improve(hi, mdl, new_model, soft):
    cost = len([f for f in soft.formulas if not is_true(new_model.eval(f))])
    if mdl is None:
        mdl = new_model
    if cost <= hi:
        print("improve", hi, cost)
        mdl = new_model
    if cost < hi:
        hi = cost
    assert mdl
    return hi, mdl

#
# This can improve lower bound, but is expensive.
# Note that Z3 does not work well for hitting set optimization.
# MIP solvers contain better
# tuned approaches thanks to LP lower bounds and likely other properties.
# Would be nice to have a good hitting set
# heuristic built into Z3....
#
def pick_hs_(K, lo, soft):
    hs = set()
    for k in K:
        ks = set(k)
        if len(ks & hs) > 0:
            continue
        h = random.choice([h for h in k])
        hs = hs | { h }
    print("approximate hitting set", len(hs), "smallest possible size", lo)
    return hs, lo

opt_backoff_limit = 0
opt_backoff_count = 0
timeout_value = 6000
def pick_hs(K, lo, soft):
    global timeout_value
    global opt_backoff_limit
    global opt_backoff_count
    if opt_backoff_count < opt_backoff_limit:
        opt_backoff_count += 1
        return pick_hs_(K, lo, soft)
    opt = Optimize()
    for k in K:
        opt.add(Or([soft.formula2name[f] for f in k]))        
    for n in soft.formula2name.values():
        obj = opt.add_soft(Not(n))
    opt.set("timeout", timeout_value)
    is_sat = opt.check()
    lo = max(lo, opt.lower(obj).as_long())
    if is_sat == sat:
        mdl = opt.model()
        hs = [soft.name2formula[n] for n in soft.formula2name.values() if is_true(mdl.eval(n))]
        return hs, lo
    else:
        print("Timeout", timeout_value, "lo", lo, "limit", opt_backoff_limit)
        opt_backoff_limit += 1
        opt_backoff_count = 0
        timeout_value += 500
        return pick_hs_(K, lo, soft)



def local_mss(hi, mdl, s, soft):
    mss = { f for f in soft.formulas if is_true(mdl.eval(f)) }
    ps = set(soft.formulas) - mss
    backbones = set()
    qs = set()
    while len(ps) > 0:
        p = random.choice([p for p in ps])
        ps = ps - { p }
        is_sat = s.check(mss | backbones | { p })
        print(p, len(ps), is_sat)
        sys.stdout.flush()
        if is_sat == sat:
            mdl = s.model()
            rs = { p }
            
# by commenting this out, we use a more stubborn exploration
# by using the random seed as opposed to current model as a guide
# to what gets satisfied.
#
# Not sure if it really has an effect.
#           rs = rs | { q for q in ps if is_true(mdl.eval(q)) }
            rs = rs | { q for q in qs if is_true(mdl.eval(q)) }
            mss = mss | rs
            ps = ps - rs 
            qs = qs - rs
            hi, mdl = improve(hi, mdl, s.model(), soft)
        elif is_sat == unsat:
            backbones = backbones | { Not(p) }            
        else:
            qs = qs | { p }
    return hi, mdl

def get_cores(hi, hs, mdl, s, soft):
    core = s.unsat_core()
    remaining = set(soft.formulas) - set(core) - set(hs)
    num_cores = 0
    cores = [core]
    print("new core of size", len(core))    
    while True:        
        is_sat = s.check(remaining)
        if unsat == is_sat:
            core = s.unsat_core()
            print("new core of size", len(core))
            cores += [core]
            remaining = remaining - set(core)
        elif sat == is_sat and num_cores == len(cores):
            hi, mdl = local_mss(hi, s.model(), s, soft)
            break
        elif sat == is_sat:
            hi, mdl = improve(hi, mdl, s.model(), soft)

            #
            # Extend the size of the hitting set using the new cores
            # and update remaining using these cores.
            # The new hitting set contains at least one new element
            # from the original core
            #
            hs = set(hs)
            for i in range(num_cores, len(cores)):
                h = random.choice([c for c in cores[i]])
                hs = hs | { h }
            remaining = set(soft.formulas) - set(core) - set(hs)
            num_cores = len(cores)
        else:
            print(is_sat)
            break
    return hi, mdl, cores

def hs(lo, hi, mdl, K, s, soft):    
    hs, lo = pick_hs(K, lo, soft)
    is_sat = s.check(set(soft.formulas) - set(hs))    
    if is_sat == sat:
        hi, mdl = improve(hi, mdl, s.model(), soft)
    elif is_sat == unsat:
        hi, mdl, cores = get_cores(hi, hs, mdl, s, soft)
        K +=  [set(core) for core in cores]
        hi, mdl = local_mss(hi, mdl, s, soft)
        print("total number of cores", len(K))
    else:
        print("unknown")
    print("maxsat [", lo, ", ", hi, "]")
    return lo, hi, mdl, K
        
#set_option(verbose=1)
def main(file):
    s = Solver()
    opt = Optimize()
    opt.from_file(file)
    s.add(opt.assertions())
    soft = [f.arg(0) for f in opt.objectives()[0].children()]
    K = []
    lo = 0
    hi = len(soft)
    soft = Soft(soft)
    while lo < hi:
        lo, hi, mdl, K = hs(lo, hi, None, K, s, soft)


if __name__ == '__main__':
    main(sys.argv[1])
        
    
