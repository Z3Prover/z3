from z3 import *
import heapq


# Simplistic (and fragile) converter from
# a class of Horn clauses corresponding to 
# a transition system into a transition system
# representation as <init, trans, goal>
# It assumes it is given three Horn clauses
# of the form:
#  init(x) => Invariant(x)
#  Invariant(x) and trans(x,x') => Invariant(x')
#  Invariant(x) and goal(x) => Goal(x)
# where Invariant and Goal are uninterpreted predicates
    
class Horn2Transitions:
    def __init__(self):
        self.trans = True
        self.init = True
        self.goal = True
        self.index = 0
        
    def parse(self, file):
        fp = Fixedpoint()
        goals = fp.parse_file(file)
        for r in fp.get_rules():
            if not is_quantifier(r):
                continue
            b = r.body()
            if not is_implies(b):
                continue
            f = b.arg(0)
            g = b.arg(1)
            if self.is_goal(f, g):
                continue
            if self.is_transition(f, g):
                continue
            if self.is_init(f, g):
                continue

    def is_pred(self, p, name):
        return is_app(p) and p.decl().name() == name
    
    def is_goal(self, body, head):
        if not self.is_pred(head, "Goal"):
            return False
        pred, inv = self.is_body(body)
        if pred is None:
            return False
        self.goal = self.subst_vars("x", inv, pred)
        return True

    def is_body(self, body):
        if not is_and(body):
            return None, None
        fmls = [f for f in body.children() if self.is_inv(f) is None]
        inv = None
        for f in body.children():
            if self.is_inv(f) is not None:
                inv = f;
                break
        return And(fmls), inv

    def is_inv(self, f):
        if self.is_pred(f, "Invariant"):
            return f
        return None

    def is_transition(self, body, head):
        pred, inv0 = self.is_body(body)
        if pred is None:
            return False
        inv1 = self.is_inv(head)
        if inv1 is None:
            return False
        pred = self.subst_vars("x",  inv0, pred)
        self.xs = self.vars
        pred = self.subst_vars("xn", inv1, pred)
        self.xns = self.vars
        self.trans = pred
        return True

    def is_init(self, body, head):
        for f in body.children():
            if self.is_inv(f) is not None:
               return False
        inv = self.is_inv(head)
        if inv is None:
            return False
        self.init = self.subst_vars("x", inv, body)
        return True
    
    def subst_vars(self, prefix, inv, fml):
        subst = self.mk_subst(prefix, inv)
        self.vars = [ v for (k,v) in subst ]
        return substitute(fml, subst)

    def mk_subst(self, prefix, inv):
        self.index = 0
        return [(f, self.mk_bool(prefix)) for f in inv.children()]

    def mk_bool(self, prefix):
        self.index += 1
        return Bool("%s%d" % (prefix, self.index))

# Produce a finite domain solver.
# The theory QF_FD covers bit-vector formulas
# and pseudo-Boolean constraints.
# By default cardinality and pseudo-Boolean 
# constraints are converted to clauses. To override
# this default for cardinality constraints
# we set sat.cardinality.solver to True

def fd_solver():
    s = SolverFor("QF_FD")
    s.set("sat.cardinality.solver", True)
    return s


# negate, avoid double negation
def negate(f):
    if is_not(f):
        return f.arg(0)
    else:
        return Not(f)

def cube2clause(cube):
    return Or([negate(f) for f in cube])

class State:
    def __init__(self, s):
        self.R = set([])
        self.solver = s

    def add(self, clause):
        if clause not in self.R:
           self.R |= { clause }
           self.solver.add(clause)
    
class Goal:
    def __init__(self, cube, parent, level):
        self.level = level
        self.cube = cube
        self.parent = parent

def is_seq(f):
    return isinstance(f, list) or isinstance(f, tuple) or isinstance(f, AstVector)

# Check if the initial state is bad
def check_disjoint(a, b):
    s = fd_solver()
    s.add(a)
    s.add(b)
    return unsat == s.check()


# Remove clauses that are subsumed
def prune(R):
    removed = set([])
    s = fd_solver()
    for f1 in R:
        s.push()
        for f2 in R:
            if f2 not in removed:
               s.add(Not(f2) if f1.eq(f2) else f2)
        if s.check() == unsat:
            removed |= { f1 }
        s.pop()
    return R - removed
                
class MiniIC3:
    def __init__(self, init, trans, goal, x0, xn):
        self.x0 = x0
        self.xn = xn
        self.init = init
        self.bad = goal
        self.trans = trans
        self.min_cube_solver = fd_solver()
        self.min_cube_solver.add(Not(trans))
        self.goals = []
        s = State(fd_solver())
        s.add(init)
        s.solver.add(trans)
        self.states = [s]
        self.s_bad = fd_solver()
        self.s_good = fd_solver()
        self.s_bad.add(self.bad)
        self.s_good.add(Not(self.bad))        
        
    def next(self, f):
        if is_seq(f):
           return [self.next(f1) for f1 in f]
        return substitute(f, zip(self.x0, self.xn))    
    
    def prev(self, f):
        if is_seq(f):
           return [self.prev(f1) for f1 in f]
        return substitute(f, zip(self.xn, self.x0))    
    
    def add_solver(self):
        s = fd_solver()
        s.add(self.trans)
        self.states += [State(s)]        

    def R(self, i):
        return And(self.states[i].R)

    # Check if there are two states next to each other that have the same clauses.
    def is_valid(self):
        i = 1
        while i + 1 < len(self.states):
            if not (self.states[i].R - self.states[i+1].R):
               return And(prune(self.states[i].R))
            i += 1
        return None

    def value2literal(self, m, x):
        value = m.eval(x)
        if is_true(value):
            return x
        if is_false(value):
            return Not(x)
        return None

    def values2literals(self, m, xs):
        p = [self.value2literal(m, x) for x in xs]
        return [x for x in p if x is not None]

    def project0(self, m):
        return self.values2literals(m, self.x0)

    def projectN(self, m):
        return self.values2literals(m, self.xn)

    # Determine if there is a cube for the current state 
    # that is potentially reachable.
    def unfold(self):
        core = []
        self.s_bad.push()
        R = self.R(len(self.states)-1)
        self.s_bad.add(R)
        is_sat = self.s_bad.check()
        if is_sat == sat:
           m = self.s_bad.model()
           props = self.project0(m)
           self.s_good.push()
           self.s_good.add(R)
           is_sat2 = self.s_good.check(props)
           assert is_sat2 == unsat
           core = self.s_good.unsat_core()
           self.s_good.pop()
        self.s_bad.pop()
        return is_sat, core

    # Block a cube by asserting the clause corresponding to its negation
    def block_cube(self, i, cube):
        self.assert_clause(i, cube2clause(cube))

    # Add a clause to levels 0 until i
    def assert_clause(self, i, clause):
        for j in range(i + 1):
            self.states[j].add(clause)

    # minimize cube that is core of Dual solver.
    # this assumes that props & cube => Trans    
    def minimize_cube(self, cube, lits):
        is_sat = self.min_cube_solver.check(lits + [c for c in cube])
        assert is_sat == unsat
        core = self.min_cube_solver.unsat_core()
        assert core
        return [c for c in core if c in set(cube)]

    # push a goal on a heap
    def push_heap(self, goal):
        heapq.heappush(self.goals, (goal.level, goal))

    # A state s0 and level f0 such that
    # not(s0) is f0-1 inductive
    def ic3_blocked(self, s0, f0):
        self.push_heap(Goal(self.next(s0), None, f0))
        while self.goals:
            f, g = heapq.heappop(self.goals)
            sys.stdout.write("%d." % f)
            sys.stdout.flush()
            # Not(g.cube) is f-1 invariant
            if f == 0:
               print("")
               return g
            cube, f, is_sat = self.is_inductive(f, g.cube)
            if is_sat == unsat:
               self.block_cube(f, self.prev(cube))
               if f < f0:
                  self.push_heap(Goal(g.cube, g.parent, f + 1))
            elif is_sat == sat:
               self.push_heap(Goal(cube, g, f - 1))
               self.push_heap(g)
            else:
               return is_sat
        print("")
        return None

    # Rudimentary generalization:
    # If the cube is already unsat with respect to transition relation
    # extract a core (not necessarily minimal)
    # otherwise, just return the cube.
    def generalize(self, cube, f):
        s = self.states[f - 1].solver
        if unsat == s.check(cube):
            return s.unsat_core(), f
        return cube, f

    # Check if the negation of cube is inductive at level f
    def is_inductive(self, f, cube):
        s = self.states[f - 1].solver
        s.push()
        s.add(self.prev(Not(And(cube))))
        is_sat = s.check(cube)
        if is_sat == sat:
           m = s.model()
        s.pop()
        if is_sat == sat:
           cube = self.next(self.minimize_cube(self.project0(m), self.projectN(m)))
        elif is_sat == unsat:
           cube, f = self.generalize(cube, f)
        return cube, f, is_sat
                        
    def run(self):
        if not check_disjoint(self.init, self.bad):
           return "goal is reached in initial state"
        level = 0
        while True:
            inv = self.is_valid()
            if inv is not None:
                return inv
            is_sat, cube = self.unfold()
            if is_sat == unsat:
               level += 1
               print("Unfold %d" % level)
               sys.stdout.flush()
               self.add_solver()
            elif is_sat == sat:
               cex = self.ic3_blocked(cube, level)
               if cex is not None:
                  return cex
            else:
               return is_sat  

def test(file):
    h2t = Horn2Transitions()
    h2t.parse(file)
    mp = MiniIC3(h2t.init, h2t.trans, h2t.goal, h2t.xs, h2t.xns)
    result = mp.run()    
    if isinstance(result, Goal):
       g = result
       print("Trace")
       while g:
          print(g.level, g.cube)
          g = g.parent
       return
    if isinstance(result, ExprRef):
       print("Invariant:\n%s " % result)
       return
    print(result)

test("data/horn1.smt2")
test("data/horn2.smt2")



"""
# TBD: Quip variant of IC3

must = True
may = False

class QGoal:
    def __init__(self, cube, parent, level, must):
        self.level = level
        self.cube = cube
        self.parent = parent
        self.must = must

class Quip(MiniIC3):

    # prev & tras -> r', such that r' intersects with cube
    def add_reachable(self, prev, cube):
        s = fd_solver()
        s.add(self.trans)
        s.add(prev)
        s.add(Or(cube))
        is_sat = s.check()
        assert is_sat == sat
        m = s.model();
        result = self.values2literals(m, cube)
        assert result
        self.reachable.add(result)

    # A state s0 and level f0 such that
    # not(s0) is f0-1 inductive
    def quip_blocked(self, s0, f0):
        self.push_heap(QGoal(self.next(s0), None, f0, must))
        while self.goals:
           f, g = heapq.heappop(self.goals)
           sys.stdout.write("%d." % f)
           sys.stdout.flush()
           if f == 0:
              if g.must:
                 print("")
                 return g
              self.add_reachable(self.init, p.parent.cube)
              continue

        # TBD
        return None

                        
    def run(self):
        if not check_disjoint(self.init, self.bad):
           return "goal is reached in initial state"
        level = 0
        while True:
            inv = self.is_valid()
            if inv is not None:
                return inv
            is_sat, cube = self.unfold()
            if is_sat == unsat:
               level += 1
               print("Unfold %d" % level)
               sys.stdout.flush()
               self.add_solver()
            elif is_sat == sat:
               cex = self.quipie_blocked(cube, level)
               if cex is not None:
                  return cex
            else:
               return is_sat  

"""