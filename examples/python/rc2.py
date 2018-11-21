# RC2 algorithm
# basic version without optimizations
# See also https://github.com/pysathq/pysat and papers in CP 2014, JSAT 2015.

from z3 import *

def tt(s, f):
    return is_true(s.model().eval(f))


def add(Ws, f, w):
    Ws[f] = w + (Ws[f] if f in Ws else 0)

def sub(Ws, f, w):
    w1 = Ws[f]
    if w1 > w:
        Ws[f] = w1 - w
    else:
        del(Ws[f])

class RC2:
    def __init__(self, s):
        self.bounds = {}
        self.solver = s
        self.solver.set("sat.cardinality.solver", True)
        self.solver.set("sat.core.minimize", True)
        self.solver.set("sat.core.minimize_partial", True)
        
    def at_most(self, S, k):
        fml = AtMost(S + [k])
        name = Bool("%s" % fml)
        self.solver.add(Implies(name, fml))
        self.bounds[name] = (S, k)
        return name

    # Ws are weighted soft constraints
    # Whenever there is an unsatisfiable core over ws
    # increase the limit of each soft constraint from a bound
    # and create a soft constraint that limits the number of
    # increased bounds to be at most one.
    def maxsat(self, Ws):
        cost = 0
        Ws0 = Ws.copy()
        while unsat == self.solver.check([f for f in Ws]):
            core = list(self.solver.unsat_core())
            print (self.solver.statistics())
            print("Core", core)
            if not core:
                return unsat
            w = min([Ws[c] for c in core])
            cost += w
            for f in core:
                sub(Ws, f, w)
            for f in core:
                if f in self.bounds:
                    S, k = self.bounds[f]
                    if k + 1 < len(S):
                        add(Ws, self.at_most(S, k + 1), w)                
            add(Ws, self.at_most([mk_not(f) for f in core], 1), w)
            
        return cost, { f for f in Ws0 if tt(self.solver, f) }

    def from_file(self, file):
        opt = Optimize()
        opt.from_file(file)
        self.solver.add(opt.assertions())
        obj = opt.objectives()[0]
        Ws = {}        
        for f in obj.children():
            assert(f.arg(1).as_long() == 0)
            add(Ws, f.arg(0), f.arg(2).as_long())
        return self.maxsat(Ws)


def main(file):
    s = SolverFor("QF_FD")
    rc2 = RC2(s)
    set_param(verbose=0)
    cost, trues = rc2.from_file(file)
    print(cost)
    print(s.statistics())

# main(<myfile>)
    
