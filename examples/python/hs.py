#
# Unweighted hitting set maxsat solver.
# interleaved with local hill-climbing improvements
# and also maxres relaxation steps to reduce number
# of soft constraints.
#

from z3 import *
import random


def add_def(s, fml):
    name = Bool(f"f{fml}")
    s.add(name == fml)
    return name

def relax_core(s, core, Fs):
    core = list(core)
    if len(core) == 0:
        return
    prefix = BoolVal(True)
    Fs -= { f for f in core }
    for i in range(len(core)-1):
        prefix = add_def(s, And(core[i], prefix))
        Fs |= { add_def(s, Or(prefix, core[i+1])) }

def restrict_cs(s, cs, Fs):
    cs = list(cs)
    if len(cs) == 0:
        return
    prefix = BoolVal(False)
    Fs -= { f for f in cs }
    for i in range(len(cs)-1):
        prefix = add_def(s, Or(cs[i], prefix))
        Fs |= { add_def(s, And(prefix, cs[i+1])) }

def count_sets_by_size(sets):
    sizes = {}
    for core in sets:
        sz = len(core)
        if sz not in sizes:
            sizes[sz] = 0
        sizes[sz] += 1
    sizes = list(sizes.items())
    sizes = sorted(sizes, key = lambda p : p[0])
    print(sizes)
        

#set_param("sat.euf", True)
#set_param("tactic.default_tactic","sat")
#set_param(verbose=1)
                
class Soft:
    def __init__(self, soft):
        self.formulas = soft
        self.offset = 0
        self.init_names()

    def init_names(self):
        self.name2formula = { Bool(f"s{s}") : s for s in self.formulas }
        self.formula2name = { s : v for (v, s) in self.name2formula.items() }

class HsPicker:
    def __init__(self, soft):
        self.soft = soft
        self.opt_backoff_limit = 0  
        self.opt_backoff_count = 0
        self.timeout_value = 6000        

    def pick_hs_(self, Ks, lo):
        hs = set()
        for ks in Ks:
            if not any(k in ks for k in hs):
                h = random.choice([h for h in ks])
                hs = hs | { h }
        print("approximate hitting set", len(hs), "smallest possible size", lo)
        return hs, lo

    #
    # This can improve lower bound, but is expensive.
    # Note that Z3 does not work well for hitting set optimization.
    # MIP solvers contain better
    # tuned approaches thanks to LP lower bounds and likely other properties.
    # Would be nice to have a good hitting set
    # heuristic built into Z3....
    #

    def pick_hs(self, Ks, lo):
        if self.opt_backoff_count < self.opt_backoff_limit:
            self.opt_backoff_count += 1
            return self.pick_hs_(Ks, lo)
        opt = Optimize()
        for k in Ks:
            opt.add(Or([self.soft.formula2name[f] for f in k]))        
        for n in self.soft.formula2name.values():
            obj = opt.add_soft(Not(n))
        opt.set("timeout", self.timeout_value)
        is_sat = opt.check()
        lo = max(lo, opt.lower(obj).as_long())
        if is_sat == sat:
            mdl = opt.model()
            hs = [self.soft.name2formula[n] for n in self.soft.formula2name.values() if is_true(mdl.eval(n))]
            return hs, lo
        else:
            print("Timeout", self.timeout_value, "lo", lo, "limit", self.opt_backoff_limit)
            self.opt_backoff_limit += 1
            self.opt_backoff_count = 0
            self.timeout_value += 500
            return self.pick_hs_(Ks, lo)


class HsMaxSAT:
        
    def __init__(self, soft, s):
        self.s = s                    # solver object
        self.original_soft = soft
        self.soft = Soft(soft)        # Soft constraints
        self.hs = HsPicker(self.soft) # Pick a hitting set
        self.mdl = None               # Current best model
        self.lo = 0                   # Current lower bound
        self.hi = len(soft)           # Current upper bound
        self.Ks = []                  # Set of Cores
        self.Cs = []                  # Set of correction sets
        self.small_set_size = 6
        self.small_set_threshold = 2
        self.num_max_res_failures = 0        

    def has_many_small_sets(self, sets):
        small_count = len([c for c in sets if len(c) <= self.small_set_size])
        return self.small_set_threshold <= small_count

    def get_small_disjoint_sets(self, sets):
        hs = set()
        result = []
        min_size = min(len(s) for s in sets)
        def insert(bound, sets, hs, result):            
            for s in sets:
                if len(s) <= bound and not any(c in hs for c in s):
                    result += [s]
                    hs = hs | set(s)
            return hs, result
        for sz in range(min_size, self.small_set_size + 1):
            hs, result = insert(sz, sets, hs, result)
        return result

    def reinit_soft(self, num_cores_relaxed):
        self.soft.init_names()
        self.soft.offset += num_cores_relaxed
        self.Ks = []
        self.Cs = []
        self.lo -= num_cores_relaxed
        self.hi -= num_cores_relaxed
        print("New offset", self.soft.offset)
                
    def maxres(self):
        #
        # If there are sufficiently many small cores, then
        # we reduce the soft constraints by maxres.
        #
        if self.has_many_small_sets(self.Ks):
            self.num_max_res_failures = 0
            cores = self.get_small_disjoint_sets(self.Ks)
            self.soft.formulas = set(self.soft.formulas)
            for core in cores:
                self.small_set_size = min(self.small_set_size, len(core) - 2)
                relax_core(self.s, core, self.soft.formulas)
            self.reinit_soft(len(cores))
            return
        #
        # If there are sufficiently many small correction sets, then
        # we reduce the soft constraints by dual maxres (IJCAI 2014)
        # 
        if self.has_many_small_sets(self.Cs):
            self.num_max_res_failures = 0
            cs = self.get_small_disjoint_sets(self.Cs)
            self.soft.formulas = set(self.soft.formulas)            
            for corr_set in cs:
                print("restrict cs", len(corr_set))
                self.small_set_size = min(self.small_set_size, len(corr_set) - 2)
                restrict_cs(self.s, corr_set, self.soft.formulas)
                s.add(Or(corr_set))
            self.reinit_soft(0)
            return
        #
        # Increment the failure count. If the failure count reaches a threshold
        # then increment the lower bounds for performing maxres or dual maxres
        # 
        self.num_max_res_failures += 1
        if self.num_max_res_failures > 6:
            self.num_max_res_failures = 0
            self.small_set_size += 2

    def pick_hs(self):
        hs, self.lo = self.hs.pick_hs(self.Ks, self.lo)
        return hs    

    def save_model(self):
        # 
        # You can save a model here.
        # For example, add the string: self.mdl.sexpr()
        # to a file, or print bounds in custom format.
        #
        # print(f"Bound: {self.lo}")
        # for f in self.original_soft:
        #     print(f"{f} := {self.mdl.eval(f)}")
        pass

    def improve(self, new_model):
        mss = { f for f in self.soft.formulas if is_true(new_model.eval(f)) }
        cs = set(self.soft.formulas) - mss
        self.Cs += [cs]
        cost = len(cs)
        if self.mdl is None:
            self.mdl = new_model
        if cost <= self.hi:
            print("improve", self.hi, cost)
            self.mdl = new_model
            self.save_model()
        if cost < self.hi:
            self.hi = cost
        assert self.mdl

    def local_mss(self, hi, new_model):
        mss = { f for f in self.soft.formulas if is_true(new_model.eval(f)) }
        ps = set(self.soft.formulas) - mss
        backbones = set()
        qs = set()
        while len(ps) > 0:
            p = random.choice([p for p in ps])
            ps = ps - { p }
            is_sat = self.s.check(mss | backbones | { p })
            print(len(ps), is_sat)
            sys.stdout.flush()
            if is_sat == sat:
                mdl = self.s.model()
                rs = { p }

                #
                # by commenting this out, we use a more stubborn exploration
                # by using the random seed as opposed to current model as a guide
                # to what gets satisfied.
                #
                # Not sure if it really has an effect.
                #           rs = rs | { q for q in ps if is_true(mdl.eval(q)) }
                #
                rs = rs | { q for q in qs if is_true(mdl.eval(q)) }
                mss = mss | rs
                ps = ps - rs 
                qs = qs - rs
                self.improve(mdl)
            elif is_sat == unsat:
                backbones = backbones | { Not(p) }
            else:
                qs = qs | { p }
        if len(qs) > 0:
            print("Number undetermined", len(qs))

    def get_cores(self, hs):
        core = self.s.unsat_core()
        remaining = set(self.soft.formulas) - set(core) - set(hs)
        num_cores = 0
        cores = [core]
        if len(core) == 0:
            self.lo = self.hi
            return []
        print("new core of size", len(core))    
        while True:        
            is_sat = self.s.check(remaining)
            if unsat == is_sat:
                core = self.s.unsat_core()
                print("new core of size", len(core))
                cores += [core]
                remaining = remaining - set(core)
            elif sat == is_sat and num_cores == len(cores):
                self.local_mss(self.hi, self.s.model())
                break
            elif sat == is_sat:
                self.improve(self.s.model())

                #
                # Extend the size of the hitting set using the new cores
                # and update remaining using these cores.
                # The new hitting set contains at least one new element
                # from the original cores
                #
                hs = set(hs)
                for i in range(num_cores, len(cores)):
                    h = random.choice([c for c in cores[i]])
                    hs = hs | { h }
                remaining = set(self.soft.formulas) - set(core) - set(hs)
                num_cores = len(cores)
            else:
                print(is_sat)
                break
        return cores

    def step(self):
        soft = self.soft
        hs = self.pick_hs()
        is_sat = self.s.check(set(soft.formulas) - set(hs))    
        if is_sat == sat:
            self.improve(self.s.model())
        elif is_sat == unsat:
            cores = self.get_cores(hs)            
            self.Ks += [set(core) for core in cores]
            print("total number of cores", len(self.Ks))
            print("total number of correction sets", len(self.Cs))
        else:
            print("unknown")
        print("maxsat [", self.lo + soft.offset, ", ", self.hi + soft.offset, "]","offset", soft.offset)
        count_sets_by_size(self.Ks)
        count_sets_by_size(self.Cs)
        self.maxres()

    def run(self):
        while self.lo < self.hi:
            self.step()

                
#set_option(verbose=1)
def main(file):
    s = Solver()
    opt = Optimize()
    opt.from_file(file)
    s.add(opt.assertions())
    #
    # We just assume this is an unweighted MaxSAT optimization problem.
    # Weights are ignored.
    #
    soft = [f.arg(0) for f in opt.objectives()[0].children()]
    hs = HsMaxSAT(soft, s)
    hs.run()


if __name__ == '__main__':
    main(sys.argv[1])
        
    
