#
# Unweighted hitting set maxsat solver.
#

class Soft:
    __init__(self, soft):
        self.formulas = soft
        self.name2formula = { Bool(f"s{s}") : s for s in soft }
        self.formula2name = { s : v for (v, s) in self._name2formula.items() }

def improve(hi, mdl, new_model, soft):
    cost = len([f for f in soft.formulas if not is_true(new_model.eval(f))])
    if cost <= hi:
        mdl = new_model
    if cost < hi:
        hi = cost
    return hi, mdl

def pick_hs(K, soft):
    opt = Optimize()
    for k in K:
        opt.add(Or(soft.formula2name[f] for f in k))        
    for n in soft.formula2name.values():
        opt.add_soft(Not(n))
    print(opt.check())
    mdl = opt.model()
    hs = [soft.name2formula[n] for n in soft.formula2name.values() if is_true(mdl.eval(n))]
    return hs, True

def hs(lo, hi, mdl, K, s, soft):    
    hs, is_min = pick_hs(K, soft)
    is_sat = s.check(set(soft.formulas) - set(hs))
    if is_sat == sat:
        hi, mdl = improve(hi, mdl, s.model(), soft)
    elif is_sat == unsat:
        core = s.unsat_core()
        K += [set(core)]
        if is_min:
            lo = max(lo, len(hs))
    else:
        print("unknown")
    print(lo, hi)
    return lo, hi, mdl, K
        

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

def __main__():
    main(sys.argv[0])
        
    
