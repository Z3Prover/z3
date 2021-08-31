#
# Unweighted hitting set maxsat solver.
# interleaved with local hill-climbing improvements
# and also maxres relaxation steps to reduce number
# of soft constraints.
#

from z3 import *
import random

counter = 0

def add_def(s, fml):
    global counter
    name = Bool(f"def-{counter}")
    counter += 1
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
#set_param("sat.cardinality.solver",False)
#set_param("sat.cardinality.encoding", "circuit")
#set_param(verbose=1)
                
class Soft:
    def __init__(self, soft):
        self.formulas = set(soft)
        self.original_soft = soft.copy()
        self.offset = 0
        self.init_names()

    def init_names(self):
        self.name2formula = { Bool(f"s{s}") : s for s in self.formulas }
        self.formula2name = { s : v for (v, s) in self.name2formula.items() }

#
# TODO: try to replace this by a recursive invocation of HsMaxSAT
# such that the invocation is incremental with respect to adding constraints
# and has resource bounded invocation.
# 
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
        if len(Ks) == 0:
            return set(), lo
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
        self.opt_backoff_count = 0
        if is_sat == sat:
            if self.opt_backoff_limit > 1:
                self.opt_backoff_limit -= 1
                self.timeout_value += 500
            mdl = opt.model()
            hs = [self.soft.name2formula[n] for n in self.soft.formula2name.values() if is_true(mdl.eval(n))]
            return set(hs), lo
        else:
            print("Timeout", self.timeout_value, "lo", lo, "limit", self.opt_backoff_limit)
            self.opt_backoff_limit += 1
            self.timeout_value += 500
            return self.pick_hs_(Ks, lo)


class HsMaxSAT:
        
    def __init__(self, soft, s):
        self.s = s                    # solver object
        self.soft = Soft(soft)        # Soft constraints
        self.hs = HsPicker(self.soft) # Pick a hitting set
        self.model = None               # Current best model
        self.lo = 0                   # Current lower bound
        self.hi = len(soft)           # Current upper bound
        self.Ks = []                  # Set of Cores
        self.Cs = []                  # Set of correction sets
        self.small_set_size = 6
        self.small_set_threshold = 1
        self.num_max_res_failures = 0
        self.corr_set_enabled = True
        self.patterns = []

    def has_many_small_sets(self, sets):
        small_count = len([c for c in sets if len(c) <= self.small_set_size])
        return self.small_set_threshold <= small_count

    def get_small_disjoint_sets(self, sets):
        hs = set()
        result = []
        min_size = min(len(s) for s in sets)
        def insert(bound, sets, hs, result):            
            for s in sets:
                if len(s) == bound and not any(c in hs for c in s):
                    result += [s]
                    hs = hs | set(s)
            return hs, result
        for sz in range(min_size, min_size + 3):
            hs, result = insert(sz, sets, hs, result)
        return result

    def reinit_soft(self, num_cores_relaxed):
        self.soft.init_names()
        self.soft.offset += num_cores_relaxed
        self.Ks = []
        self.Cs = []
        self.lo -= num_cores_relaxed
        print("New offset", self.soft.offset)
                
    def maxres(self):
        #
        # If there are sufficiently many small cores, then
        # we reduce the soft constraints by maxres.
        #
        if self.has_many_small_sets(self.Ks) or (not self.corr_set_enabled and not self.has_many_small_sets(self.Cs) and self.num_max_res_failures > 0):
            self.num_max_res_failures = 0
            cores = self.get_small_disjoint_sets(self.Ks)
            for core in cores:
                self.small_set_size = max(4, min(self.small_set_size, len(core) - 2))
                relax_core(self.s, core, self.soft.formulas)
            self.reinit_soft(len(cores))
            self.corr_set_enabled = True
            return
        #
        # If there are sufficiently many small correction sets, then
        # we reduce the soft constraints by dual maxres (IJCAI 2015)
        #
        # TODO: the heuristic for when to invoking correction set restriction
        # needs fine-tuning. For example, the if min(Ks)*optimality_gap < min(Cs)*(max(SS))
        # we might want to prioritize core relaxation to make progress with less overhead.
        # here: max(SS) = |Soft|-min(Cs) is the size of the maximal satisfying subset
        # the optimality gap is self.hi - self.offset
        # which is a bound on how many cores have to be relaxed before determining optimality.
        # 
        if self.corr_set_enabled and self.has_many_small_sets(self.Cs):
            self.num_max_res_failures = 0
            cs = self.get_small_disjoint_sets(self.Cs)
            for corr_set in cs:
                print("restrict cs", len(corr_set))
                # self.small_set_size = max(4, min(self.small_set_size, len(corr_set) - 2))
                restrict_cs(self.s, corr_set, self.soft.formulas)
                self.s.add(Or(corr_set))
            self.reinit_soft(0)
            self.corr_set_enabled = False
            return
        #
        # Increment the failure count. If the failure count reaches a threshold
        # then increment the lower bounds for performing maxres or dual maxres
        # 
        self.num_max_res_failures += 1
        print("Small set size", self.small_set_size, "num skips", self.num_max_res_failures)
        if self.num_max_res_failures > 3:
            self.num_max_res_failures = 0
            self.small_set_size += 100

    def pick_hs(self):
        hs, self.lo = self.hs.pick_hs(self.Ks, self.lo)
        return hs    

    def save_model(self):
        # 
        # You can save a model here.
        # For example, add the string: self.model.sexpr()
        # to a file, or print bounds in custom format.
        #
        # print(f"Bound: {self.lo}")
        # for f in self.soft.original_soft:
        #     print(f"{f} := {self.model.eval(f)}")
        pass

    def add_pattern(self, orig_cs):
        named = { f"{f}" : f for f in self.soft.original_soft }
        sorted_names = sorted(named.keys())
        sorted_soft = [named[f] for f in sorted_names]
        bits = [1 if f not in orig_cs else 0 for f in sorted_soft]
        def eq_bits(b1, b2):
            return all(b1[i] == b2[i] for i in range(len(b1)))
        def num_overlaps(b1, b2):
            return sum(b1[i] == b2[i] for i in range(len(b1)))
        
        if not any(eq_bits(b, bits) for b in self.patterns):
            if len(self.patterns) > 0:
                print(num_overlaps(bits, self.patterns[-1]), len(bits), bits)
            self.patterns += [bits]
            counts = [sum(b[i] for b in self.patterns) for i in range(len(bits))]
            print(counts)

    #
    # Crude, quick core reduction attempt
    # 
    def reduce_core(self, core):
        s = self.s        
        if len(core) <= 4:
            return core

        s.set("timeout", 200)
        i = 0
        num_undef = 0
        orig_len = len(core)
        core = list(core)
        while i < len(core):
            is_sat = s.check([core[j] for j in range(len(core)) if j != i])
            if is_sat == unsat:
                core = s.unsat_core()
            elif is_sat == sat:
                self.improve(s.model())
                bound = self.hi - self.soft.offset - 1
            else:
                num_undef += 1
                if num_undef > 3:
                    break
            i += 1
        print("Reduce", orig_len, "->", len(core), "iterations", i, "unknown", num_undef)
        s.set("timeout", 100000000)
        return core
                
    def improve(self, new_model):
        mss = { f for f in self.soft.formulas if is_true(new_model.eval(f)) }
        cs = self.soft.formulas - mss
        self.Cs += [cs]
        orig_cs = { f for f in self.soft.original_soft if not is_true(new_model.eval(f)) }
        cost = len(orig_cs) 
        if self.model is None:
            self.model = new_model
        if cost <= self.hi:
            self.add_pattern(orig_cs)
            print("improve", self.hi, cost)
            self.model = new_model
            self.save_model()
        assert self.model            
        if cost < self.hi:
            self.hi = cost
            return True
        return False

    def try_rotate(self, mss):
        backbones = set()
        backbone2core = {}
        ps = self.soft.formulas - mss
        num_sat = 0
        num_unsat = 0
        improved = False
        while len(ps) > 0:
            p = random.choice([p for p in ps])
            ps = ps - { p }
            is_sat = self.s.check(mss | backbones | { p })
            if is_sat == sat:
                mdl = self.s.model()
                mss = mss | {p}
                ps = ps - {p}
                if self.improve(mdl):
                    improved = True
                num_sat += 1
            elif is_sat == unsat:
                backbones = backbones | { Not(p) }
                core = set()
                for c in self.s.unsat_core():
                    if c in backbone2core:
                        core = core | backbone2core[c]
                    else:
                        core = core | { c }
                if len(core) < 20:
                    self.Ks += [core]
                backbone2core[Not(p)] = set(core) - { p }
                num_unsat += 1
            else:
                print("unknown")
        print("rotate-1 done, sat", num_sat, "unsat", num_unsat)
        if improved:
            self.mss_rotate(mss, backbone2core)
        return improved

    def mss_rotate(self, mss, backbone2core):
        counts = { c : 0 for c in mss }
        max_count = 0
        max_val = None
        for core in backbone2core.values():
            for c in core:
                assert c in mss
                counts[c] += 1
                if max_count < counts[c]:
                    max_count = counts[c]
                    max_val = c
        print("rotate max-count", max_count, "num occurrences", len({c for c in counts if counts[c] == max_count}))
        print("Number of plateaus", len({ c for c in counts if counts[c] <= 1 }))
        for c in counts:
            if counts[c] > 1:
                print("try-rotate", counts[c])
                if self.try_rotate(mss - { c }):
                    break


    def local_mss(self, new_model):
        mss = { f for f in self.soft.formulas if is_true(new_model.eval(f)) }

        ########################################
        # test effect of random sub-sampling
        #
        #mss = list(mss)
        #ms = set()
        #for i in range(len(mss)//2):
        #    ms = ms | { random.choice([p for p in mss]) }
        #mss = ms
        ####
        
        ps = self.soft.formulas - mss
        backbones = set()
        qs = set()
        backbone2core = {}
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
                if self.improve(mdl):
                    self.mss_rotate(mss, backbone2core)
            elif is_sat == unsat:
                core = set()
                for c in self.s.unsat_core():
                    if c in backbone2core:
                        core = core | backbone2core[c]
                    else:
                        core = core | { c }
                core = self.reduce_core(core)
                self.Ks += [core]
                backbone2core[Not(p)] = set(core) - { p }
                backbones = backbones | { Not(p) }
            else:
                qs = qs | { p }
        if len(qs) > 0:
            print("Number undetermined", len(qs))

    def unsat_core(self):
        core = self.s.unsat_core()
        return self.reduce_core(core)
        
    def get_cores(self, hs):
        core = self.unsat_core()
        remaining = self.soft.formulas - hs
        num_cores = 0
        cores = [core]
        if len(core) == 0:
            self.lo = self.hi - self.soft.offset
            return
        while True:        
            is_sat = self.s.check(remaining)
            if unsat == is_sat:
                core = self.unsat_core()
                if len(core) == 0:
                    self.lo = self.hi - self.soft.offset
                    return
                cores += [core]
                h = random.choice([c for c in core])                
                remaining = remaining - { h }
            elif sat == is_sat and num_cores == len(cores):
                self.local_mss(self.s.model())
                break
            elif sat == is_sat:
                self.improve(self.s.model())

                #
                # Extend the size of the hitting set using the new cores
                # and update remaining using these cores.
                # The new hitting set contains at least one new element
                # from the original cores
                #
                hs = hs | { random.choice([c for c in cores[i]]) for i in range(num_cores, len(cores)) }
                remaining = self.soft.formulas - hs
                num_cores = len(cores)
            else:
                print(is_sat)
                break
        self.Ks += [set(core) for core in cores]
        print("total number of cores", len(self.Ks))
        print("total number of correction sets", len(self.Cs))

    def step(self):
        soft = self.soft
        hs = self.pick_hs()
        is_sat = self.s.check(soft.formulas - set(hs))    
        if is_sat == sat:
            self.improve(self.s.model())
        elif is_sat == unsat:
            self.get_cores(hs)            
        else:
            print("unknown")
        print("maxsat [", self.lo + soft.offset, ", ", self.hi, "]","offset", soft.offset)
        count_sets_by_size(self.Ks)
        count_sets_by_size(self.Cs)
        self.maxres()

    def run(self):
        while self.lo + self.soft.offset < self.hi:
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
        
    
