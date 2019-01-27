from z3 import *
import heapq
import numpy
import time
import random

verbose = True

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
        self.inputs = []
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
        self.goal = self.subst_vars("i", self.goal, self.goal)
        self.inputs += self.vars
        self.inputs = list(set(self.inputs))
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
        pred = self.subst_vars("i", pred, pred)
        self.inputs += self.vars
        self.inputs = list(set(self.inputs))
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
        if self.is_inv(inv) is not None:
            return [(f, self.mk_bool(prefix)) for f in inv.children()]
        else:
            vars = self.get_vars(inv)
            return [(f, self.mk_bool(prefix)) for f in vars]

    def mk_bool(self, prefix):
        self.index += 1
        return Bool("%s%d" % (prefix, self.index))

    def get_vars(self, f, rs=[]):
        if is_var(f):
            return z3util.vset(rs + [f], str)
        else:
            for f_ in f.children():
                rs = self.get_vars(f_, rs)
            return z3util.vset(rs, str)

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

# Quip variant of IC3

must = True
may = False

class QLemma:
    def __init__(self, c):
        self.cube = c
        self.clause = cube2clause(c)
        self.bad = False

    def __hash__(self):
        return hash(tuple(set(self.cube)))

    def __eq__(self, qlemma2):
        if set(self.cube) == set(qlemma2.cube) and self.bad == qlemma2.bad:
            return True
        else:
            return False

    def __ne__():
        if not self.__eq__(self, qlemma2):
            return True
        else:
            return False


class QGoal:
    def __init__(self, cube, parent, level, must, encounter):
        self.level = level
        self.cube = cube
        self.parent = parent
        self.must = must

    def __lt__(self, other):
        return self.level < other.level


class QReach:

    # it is assumed that there is a single initial state
    # with all latches set to 0 in hardware design, so
    # here init will always give a state where all variable are set to 0
    def __init__(self, init, xs):
        self.xs = xs
        self.constant_xs = [Not(x) for x in self.xs]
        s = fd_solver()
        s.add(init)
        is_sat = s.check()
        assert is_sat == sat
        m = s.model()
        # xs is a list, "for" will keep the order when iterating
        self.states = numpy.array([[False for x in self.xs]])  # all set to False
        assert not numpy.max(self.states)  # since all element is False, so maximum should be False

    # check if new state exists
    def is_exist(self, state):
        if state in self.states:
            return True
        return False

    def enumerate(self, i, state_b, state):
        while i < len(state) and state[i] not in self.xs:
            i += 1
        if i >= len(state):
            if state_b.tolist() not in self.states.tolist():
                self.states = numpy.append(self.states, [state_b], axis = 0)
                return state_b
            else:
                return None
        state_b[i] = False
        if self.enumerate(i+1, state_b, state) is not None:
            return state_b
        else:
            state_b[i] = True
            return self.enumerate(i+1, state_b, state)

    def is_full_state(self, state):
        for i in range(len(self.xs)):
            if state[i] in self.xs:
                return False
        return True

    def add(self, cube):
        state = self.cube2partial_state(cube)
        assert len(state) == len(self.xs)
        if not self.is_exist(state):
            return None
        if self.is_full_state(state):
            self.states = numpy.append(self.states, [state], axis = 0)
        else:
            # state[i] is instance, state_b[i] is boolean
            state_b = numpy.array(state)
            for i in range(len(state)):  # state is of same length as self.xs
                # i-th literal in state hasn't been assigned value
                # init un-assigned literals in state_b as True
                # make state_b only contain boolean value
                if state[i] in self.xs:
                    state_b[i] = True
                else:
                    state_b[i] = is_true(state[i])
            if self.enumerate(0, state_b, state) is not None:
                lits_to_remove = set([negate(f) for f in list(set(cube) - set(self.constant_xs))])
                self.constant_xs = list(set(self.constant_xs) - lits_to_remove)
                return state
        return None


    def cube2partial_state(self, cube):
        s = fd_solver()
        s.add(And(cube))
        is_sat = s.check()
        assert is_sat == sat
        m = s.model()
        state = numpy.array([m.eval(x) for x in self.xs])
        return state


    def state2cube(self, s):
        result = copy.deepcopy(self.xs)  # x1, x2, ...
        for i in range(len(self.xs)):
            if not s[i]:
                result[i] = Not(result[i])
        return result

    def intersect(self, cube):
        state = self.cube2partial_state(cube)
        mask = True
        for i in range(len(self.xs)):
            if is_true(state[i]) or is_false(state[i]):
                mask = (self.states[:, i] == state[i]) & mask
        intersects = numpy.reshape(self.states[mask], (-1, len(self.xs)))
        if intersects.size > 0:
            return And(self.state2cube(intersects[0]))  # only need to return one single intersect
        return None


class Quip:

    def __init__(self, init, trans, goal, x0, inputs, xn):
        self.x0 = x0
        self.inputs = inputs
        self.xn = xn
        self.init = init
        self.bad = goal
        self.trans = trans
        self.min_cube_solver = fd_solver()
        self.min_cube_solver.add(Not(trans))
        self.goals = []
        s = State(fd_solver())
        s.add(init)
        s.solver.add(trans)  # check if a bad state can be reached in one step from current level
        self.states = [s]
        self.s_bad = fd_solver()
        self.s_good = fd_solver()
        self.s_bad.add(self.bad)
        self.s_good.add(Not(self.bad))
        self.reachable = QReach(self.init, x0)
        self.frames = []  # frames is a 2d list, each row (representing level) is a set containing several (clause, bad) pairs
        self.count_may = 0

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

    def projectI(self, m):
        return self.values2literals(m, self.inputs)

    def projectN(self, m):
        return self.values2literals(m, self.xn)


    # Block a cube by asserting the clause corresponding to its negation
    def block_cube(self, i, cube):
        self.assert_clause(i, cube2clause(cube))

    # Add a clause to levels 1 until i
    def assert_clause(self, i, clause):
        for j in range(1, i + 1):
            self.states[j].add(clause)
            assert str(self.states[j].solver) != str([False])


    # minimize cube that is core of Dual solver.
    # this assumes that props & cube => Trans
    # which means props & cube can only give us a Tr in Trans,
    # and it will never make !Trans sat
    def minimize_cube(self, cube, inputs, lits):
        # min_cube_solver has !Trans (min_cube.solver.add(!Trans))
        is_sat = self.min_cube_solver.check(lits + [c for c in cube] + [i for i in inputs])
        assert is_sat == unsat
        # unsat_core gives us some lits which make Tr sat,
        # so that we can ignore other lits and include more states
        core = self.min_cube_solver.unsat_core()
        assert core
        return [c for c in core if c in set(cube)]

    # push a goal on a heap
    def push_heap(self, goal):
        heapq.heappush(self.goals, (goal.level, goal))


    # make sure cube to be blocked excludes all reachable states
    def check_reachable(self, cube):
        s = fd_solver()
        for state in self.reachable.states:
            s.push()
            r = self.reachable.state2cube(state)
            s.add(And(self.prev(r)))
            s.add(self.prev(cube))
            is_sat = s.check()
            s.pop()
            if is_sat == sat:
                # if sat, it means the cube to be blocked contains reachable states
                # so it is an invalid cube
                return False
        # if all fail, is_sat will be unsat
        return True

    # Rudimentary generalization:
    # If the cube is already unsat with respect to transition relation
    # extract a core (not necessarily minimal)
    # otherwise, just return the cube.
    def generalize(self, cube, f):
        s = self.states[f - 1].solver
        if unsat == s.check(cube):
            core = s.unsat_core()
            if self.check_reachable(core):
                return core, f
        return cube, f


    def valid_reachable(self, level):
        s = fd_solver()
        s.add(self.init)
        for i in range(level):
            s.add(self.trans)
        for state in self.reachable.states:
            s.push()
            s.add(And(self.next(self.reachable.state2cube(state))))
            print self.reachable.state2cube(state)
            print s.check()
            s.pop()

    def lemmas(self, level):
        return [(l.clause, l.bad) for l in self.frames[level]]

    # whenever a new reachable state is found, we use it to mark some existing lemmas as bad lemmas
    def mark_bad_lemmas(self, new):
        s = fd_solver()
        reset = False
        for frame in self.frames:
            for lemma in frame:
                s.push()
                s.add(lemma.clause)
                is_sat = s.check(new)
                if is_sat == unsat:
                    reset = True
                    lemma.bad = True
                s.pop()
        if reset:
            self.states = [self.states[0]]
            for i in range(1, len(self.frames)):
                self.add_solver()
                for lemma in self.frames[i]:
                    if not lemma.bad:
                        self.states[i].add(lemma.clause)

    # prev & tras -> r', such that r' intersects with cube
    def add_reachable(self, prev, cube):
        s = fd_solver()
        s.add(self.trans)
        s.add(prev)
        s.add(self.next(And(cube)))
        is_sat = s.check()
        assert is_sat == sat
        m = s.model()
        new = self.projectN(m)
        state = self.reachable.add(self.prev(new))  # always add as non-primed
        if state is not None:  # if self.states do not have new state yet
            self.mark_bad_lemmas(self.prev(new))


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
            cube = self.next(self.minimize_cube(self.project0(m), self.projectI(m), self.projectN(m)))
        elif is_sat == unsat:
            cube, f = self.generalize(cube, f)
            cube = self.next(cube)
        return cube, f, is_sat


    # Determine if there is a cube for the current state
    # that is potentially reachable.
    def unfold(self, level):
        core = []
        self.s_bad.push()
        R = self.R(level)
        self.s_bad.add(R)  # check if current frame intersects with bad states, no trans
        is_sat = self.s_bad.check()
        if is_sat == sat:
           m = self.s_bad.model()
           cube = self.project0(m)
           props = cube + self.projectI(m)
           self.s_good.push()
           self.s_good.add(R)
           is_sat2 = self.s_good.check(props)
           assert is_sat2 == unsat
           core = self.s_good.unsat_core()
           assert core
           core = [c for c in core if c in set(cube)]
           self.s_good.pop()
        self.s_bad.pop()
        return is_sat, core

    # A state s0 and level f0 such that
    # not(s0) is f0-1 inductive
    def quip_blocked(self, s0, f0):
        self.push_heap(QGoal(self.next(s0), None, f0, must, 0))
        while self.goals:
            f, g = heapq.heappop(self.goals)
            sys.stdout.write("%d." % f)
            if not g.must:
                self.count_may -= 1
            sys.stdout.flush()
            if f == 0:
                if g.must:
                    s = fd_solver()
                    s.add(self.init)
                    s.add(self.prev(g.cube))
                    # since init is a complete assignment, so g.cube must equal to init in sat solver
                    assert is_sat == s.check()
                    if verbose:
                        print("")
                    return g
                self.add_reachable(self.init, g.parent.cube)
                continue

            r0 = self.reachable.intersect(self.prev(g.cube))
            if r0 is not None:
                if g.must:
                    if verbose:
                        print ""
                    s = fd_solver()
                    s.add(self.trans)
                    # make it as a concrete reachable state
                    # intersect returns an And(...), so use children to get cube list
                    g.cube = r0.children()
                    while True:
                        is_sat = s.check(self.next(g.cube))
                        assert is_sat == sat
                        r = self.next(self.project0(s.model()))
                        r = self.reachable.intersect(self.prev(r))
                        child = QGoal(self.next(r.children()), g, 0, g.must, 0)
                        g = child
                        if not check_disjoint(self.init, self.prev(g.cube)):
                            # g is init, break the loop
                            break
                    init = g
                    while g.parent is not None:
                        g.parent.level = g.level + 1
                        g = g.parent
                    return init
                if g.parent is not None:
                    self.add_reachable(r0, g.parent.cube)
                continue

            cube = None
            is_sat = sat
            f_1 = len(self.frames) - 1
            while f_1 >= f:
                for l in self.frames[f_1]:
                    if not l.bad and len(l.cube) > 0 and set(l.cube).issubset(g.cube):
                        cube = l.cube
                        is_sat == unsat
                        break
                f_1 -= 1
            if cube is None:
                cube, f_1, is_sat = self.is_inductive(f, g.cube)
            if is_sat == unsat:
                self.frames[f_1].add(QLemma(self.prev(cube)))
                self.block_cube(f_1, self.prev(cube))
                if f_1 < f0:
                    # learned clause might also be able to block same bad states in higher level
                    if set(list(cube)) != set(list(g.cube)):
                        self.push_heap(QGoal(cube, None, f_1 + 1, may, 0))
                        self.count_may += 1
                    else:
                        # re-queue g.cube in higher level, here g.parent is simply for tracking down the trace when output.
                        self.push_heap(QGoal(g.cube, g.parent, f_1 + 1, g.must, 0))
                        if not g.must:
                            self.count_may += 1
            else:
                # qcube is a predecessor of g
                qcube = QGoal(cube, g, f_1 - 1, g.must, 0)
                if not g.must:
                    self.count_may += 1
                self.push_heap(qcube)

        if verbose:
            print("")
        return None

    # Check if there are two states next to each other that have the same clauses.
    def is_valid(self):
        i = 1
        inv = None
        while True:
            # self.states[].R contains full lemmas
            # self.frames[] contains delta-encoded lemmas
            while len(self.states) <= i+1:
                self.add_solver()
            while len(self.frames) <= i+1:
                self.frames.append(set())
            duplicates = set([])
            for l in self.frames[i+1]:
                if l in self.frames[i]:
                    duplicates |= {l}
            self.frames[i] = self.frames[i] - duplicates
            pushed = set([])
            for l in (self.frames[i] - self.frames[i+1]):
                if not l.bad:
                    s = self.states[i].solver
                    s.push()
                    s.add(self.next(Not(l.clause)))
                    s.add(l.clause)
                    is_sat = s.check()
                    s.pop()
                    if is_sat == unsat:
                        self.frames[i+1].add(l)
                        self.states[i+1].add(l.clause)
                        pushed |= {l}
            self.frames[i] = self.frames[i] - pushed
            if (not (self.states[i].R - self.states[i+1].R)
                and len(self.states[i].R) != 0):
                inv = prune(self.states[i].R)
                F_inf = self.frames[i]
                j = i + 1
                while j < len(self.states):
                    for l in F_inf:
                        self.states[j].add(l.clause)
                    j += 1
                self.frames[len(self.states)-1] = F_inf
                self.frames[i] = set([])
                break
            elif (len(self.states[i].R) == 0
                  and len(self.states[i+1].R) == 0):
                break
            i += 1

        if inv is not None:
            self.s_bad.push()
            self.s_bad.add(And(inv))
            is_sat = self.s_bad.check()
            if is_sat == unsat:
                self.s_bad.pop()
                return And(inv)
            self.s_bad.pop()
        return None

    def run(self):
        if not check_disjoint(self.init, self.bad):
            return "goal is reached in initial state"
        level = 0
        while True:
            inv = self.is_valid()  # self.add_solver() here
            if inv is not None:
                return inv
            is_sat, cube = self.unfold(level)
            if is_sat == unsat:
                level += 1
                if verbose:
                    print("Unfold %d" % level)
                sys.stdout.flush()
            elif is_sat == sat:
                cex = self.quip_blocked(cube, level)
                if cex is not None:
                    return cex
            else:
                return is_sat

def test(file):
    h2t = Horn2Transitions()
    h2t.parse(file)
    if verbose:
        print("Test file: %s") % file
    mp = Quip(h2t.init, h2t.trans, h2t.goal, h2t.xs, h2t.inputs, h2t.xns)
    start_time = time.time()
    result = mp.run()
    end_time = time.time()
    if isinstance(result, QGoal):
        g = result
        if verbose:
            print("Trace")
        while g:
           if verbose:
               print(g.level, g.cube)
           g = g.parent
        print("--- used %.3f seconds ---" % (end_time - start_time))
        validate(mp, result, mp.trans)
        return
    if isinstance(result, ExprRef):
        if verbose:
            print("Invariant:\n%s " % result)
        print("--- used %.3f seconds ---" % (end_time - start_time))
        validate(mp, result, mp.trans)
        return
    print(result)

def validate(var, result, trans):
    if isinstance(result, QGoal):
        g = result
        s = fd_solver()
        s.add(trans)
        while g.parent is not None:
            s.push()
            s.add(var.prev(g.cube))
            s.add(var.next(g.parent.cube))
            assert sat == s.check()
            s.pop()
            g = g.parent
        if verbose:
            print "--- validation succeed ----"
        return
    if isinstance(result, ExprRef):
        inv = result
        s = fd_solver()
        s.add(trans)
        s.push()
        s.add(var.prev(inv))
        s.add(Not(var.next(inv)))
        assert unsat == s.check()
        s.pop()
        cube = var.prev(var.init)
        step = 0
        while True:
            step += 1
            # too many steps to reach invariant
            if step > 1000:
                if verbose:
                    print "--- validation failed --"
                return
            if not check_disjoint(var.prev(cube), var.prev(inv)):
                # reach invariant
                break
            s.push()
            s.add(cube)
            assert s.check() == sat
            cube = var.projectN(s.model())
            s.pop()
        if verbose:
            print "--- validation succeed ----"
        return



test("data/horn1.smt2")
test("data/horn2.smt2")
test("data/horn3.smt2")
test("data/horn4.smt2")
test("data/horn5.smt2")
# test("data/horn6.smt2")  # not able to finish
