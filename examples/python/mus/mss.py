############################################
# Copyright (c) 2016 Microsoft Corporation
# 
# MSS enumeration based on maximal resolution.
#
# Author: Nikolaj Bjorner (nbjorner)
############################################

"""

The following is a procedure for enumerating maximal satisfying subsets.
It uses maximal resolution to eliminate cores from the state space.
Whenever the hard constraints are satisfiable, it finds a model that
satisfies the maximal number of soft constraints. 
During this process it collects the set of cores that are encountered.
It then reduces the set of soft constraints using max-resolution in
the style of [Narodytska & Bacchus, AAAI'14]. In other words, 
let F1, ..., F_k be a core among the soft constraints F1,...,F_n 
Replace F1,.., F_k by 
          F1 or F2, F3 or (F2 & F1), F4 or (F3 & (F2 & F1)), ..., 
          F_k or (F_{k-1} & (...))
Optionally, add the core ~F1 or ... or ~F_k to F
The current model M satisfies the new set F, F1,...,F_{n-1} if the core is minimal.
Whenever we modify the soft constraints by the core reduction any assignment
to the reduced set satisfies a k-1 of the original soft constraints.
    
"""

from z3 import *

def main():
    x, y = Reals('x y')
    soft_constraints = [x > 2, x < 1, x < 0, Or(x + y > 0, y < 0), Or(y >= 0, x >= 0), Or(y < 0, x < 0), Or(y > 0, x < 0)]
    hard_constraints = BoolVal(True)
    solver = MSSSolver(hard_constraints, soft_constraints)
    for lits in enumerate_sets(solver):
        print("%s" % lits)


def enumerate_sets(solver):
    while True:
        if sat == solver.s.check():
           MSS = solver.grow()
           yield MSS
        else:
           break

class MSSSolver:
   s = Solver()
   varcache = {}
   idcache = {}

   def __init__(self, hard, soft):
       self.n = len(soft)
       self.soft = soft
       self.s.add(hard)       
       self.soft_vars = set([self.c_var(i) for i in range(self.n)])
       self.orig_soft_vars = set([self.c_var(i) for i in range(self.n)])
       self.s.add([(self.c_var(i) == soft[i]) for i in range(self.n)])

   def c_var(self, i):
       if i not in self.varcache:
          v = Bool(str(self.soft[abs(i)]))
          self.idcache[v] = abs(i)
          if i >= 0:
             self.varcache[i] = v
          else:
             self.varcache[i] = Not(v)
       return self.varcache[i]

   # Retrieve the latest model
   # Add formulas that are true in the model to 
   # the current mss

   def update_unknown(self):
       self.model = self.s.model()
       new_unknown = set([])
       for x in self.unknown:
           if is_true(self.model[x]):
              self.mss.append(x)
           else:
              new_unknown.add(x)
       self.unknown = new_unknown
      
   # Create a name, propositional atom,
   #  for formula 'fml' and return the name.

   def add_def(self, fml):
       name = Bool("%s" % fml)
       self.s.add(name == fml)
       return name

   # replace Fs := f0, f1, f2, .. by
   # Or(f1, f0), Or(f2, And(f1, f0)), Or(f3, And(f2, And(f1, f0))), ...

   def relax_core(self, Fs):
       assert(Fs <= self.soft_vars)
       prefix = BoolVal(True)
       self.soft_vars -= Fs
       Fs = [ f for f in Fs ]
       for i in range(len(Fs)-1):
           prefix = self.add_def(And(Fs[i], prefix))
           self.soft_vars.add(self.add_def(Or(prefix, Fs[i+1])))

   # Resolve literals from the core that 
   # are 'explained', e.g., implied by 
   # other literals.

   def resolve_core(self, core):
       new_core = set([])
       for x in core:
           if x in self.mcs_explain:
              new_core |= self.mcs_explain[x]
           else:
              new_core.add(x)
       return new_core


   # Given a current satisfiable state
   # Extract an MSS, and ensure that currently 
   # encountered cores are avoided in next iterations
   # by weakening the set of literals that are
   # examined in next iterations.
   # Strengthen the solver state by enforcing that
   # an element from the MCS is encountered.

   def grow(self):
       self.mss = []
       self.mcs = []
       self.nmcs = []
       self.mcs_explain = {}
       self.unknown = self.soft_vars
       self.update_unknown()
       cores = []
       while len(self.unknown) > 0:
           x = self.unknown.pop()
           is_sat = self.s.check(self.mss + [x] + self.nmcs)
           if is_sat == sat:
              self.mss.append(x)
              self.update_unknown()
           elif is_sat == unsat:
              core = self.s.unsat_core()
              core = self.resolve_core(core)
              self.mcs_explain[Not(x)] = {y for y in core if not eq(x,y)}
              self.mcs.append(x)
              self.nmcs.append(Not(x)) 
              cores += [core]              
           else:
              print("solver returned %s" % is_sat)
              exit()
       mss = [x for x in self.orig_soft_vars if is_true(self.model[x])]
       mcs = [x for x in self.orig_soft_vars if not is_true(self.model[x])]
       self.s.add(Or(mcs))
       core_literals = set([])
       cores.sort(key=lambda element: len(element))
       for core in cores:
           if len(core & core_literals) == 0:
              self.relax_core(core)
              core_literals |= core
       return mss


main()
