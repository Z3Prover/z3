from z3 import *
import math

# Rudimentary bin cover solver using the UserPropagator feature.
# It supports the most basic propagation for bin covering.
# - each bin has a propositional variable set to true if the bin is covered
# - each item has a bit-vector recording the assigned bin
# It searches for a locally optimal solution.

class Bin:
    """
    Each bin carries values:
    - min_bound  - the lower bound required to be added to bin
    - weight     - the sum of weight of items currently added to bin
    - slack      - the difference between the maximal possible assignment and the assignments to other bin2bound.
    - var        - is propagated to true/false if the bin gets filled/cannot be filled.
    """
    def __init__(self, min_bound, index):
        assert min_bound > 0
        assert index >= 0
        self.index = index
        self.min_bound = min_bound
        self.weight = 0
        self.slack = 0
        self.added = []
        self.var = Bool(f"bin-{index}")

    def set_slack(self, slack):
        self.slack = slack

    def set_fill(self, fill):
        self.weight = fill

    def __repr__(self):
        return f"{self.var}:bound-{self.min_bound}"


class Item:
    def __init__(self, weight, index):
        self.weight = weight
        self.index = index
        self.var = None

    def set_var(self, num_bits):
        self.var = BitVec(f"binof-{self.index}", num_bits)

    def __repr__(self):
        return f"binof-{self.index}:weight-{self.weight}"

class BranchAndBound:
    """Branch and Bound solver.
    It keeps track of a current best score and a slack that tracks bins that are set unfilled.
    It blocks branches that are worse than the current best score.
    In Final check it blocks the current assignment.
    """
    def __init__(self, user_propagator):
        self.up = user_propagator

    def init(self, soft_literals):
        self.value = 0
        self.best = 0
        self.slack = 0
        self.id2weight = {}
        self.assigned_to_false = []
        for p, weight in soft_literals:
            self.slack += weight
            self.id2weight[p.get_id()] = weight

    def fixed(self, p, value):
        weight = self.id2weight[p.get_id()]
        if is_true(value):
            old_value = self.value
            self.up.trail += [lambda : self._undo_value(old_value)]
            self.value += weight
        elif self.best > self.slack - weight:
            self.assigned_to_false += [ p ]
            self.up.conflict(self.assigned_to_false)
            self.assigned_to_false.pop(-1)
        else:
            old_slack = self.slack
            self.up.trail += [lambda : self._undo_slack(old_slack)]
            self.slack -= weight
            self.assigned_to_false += [p]

    def final(self):
        if self.value > self.best:
            self.best = self.value
        print("Number of bins filled", self.value)
        for bin in self.up.bins:
            print(bin.var, bin.added)
        self.up.conflict(self.assigned_to_false)

    def _undo_value(self, old_value):
        self.value = old_value

    def _undo_slack(self, old_slack):
        self.slack = old_slack
        self.assigned_to_false.pop(-1)
        
class BinCoverSolver(UserPropagateBase):
    """Represent a bin-covering problem by associating each bin with a variable
       For each item i associate a bit-vector
       - bin-of-i that carries the bin identifier where an item is assigned.

    """

    def __init__(self, s=None, ctx=None):
        UserPropagateBase.__init__(self, s, ctx)
        self.bins = []
        self.items = []
        self.item2index = {}
        self.trail = []  # Undo stack
        self.lim = []
        self.solver = s
        self.initialized = False
        self.add_fixed(lambda x, v : self._fixed(x, v))
        self.branch_and_bound = None


    # Initialize bit-vector variables for items.
    # Register the bit-vector variables with the user propagator to get callbacks
    # Ensure the bit-vector variables are assigned to a valid bin.
    # Initialize the slack of each bin.
    def init(self):
        print(self.bins, len(self.bins))
        print(self.items)
        assert not self.initialized
        self.initialized = True
        powerof2, num_bits = self._num_bits()
        for item in self.items:
            item.set_var(num_bits)
            self.item2index[item.var.get_id()] = item.index
            self.add(item.var)
            if not powerof2:
                bound = BitVecVal(len(self.bins), num_bits)
                ineq = ULT(item.var, bound)
                self.solver.add(ineq)
        total_weight = sum(item.weight for item in self.items)
        for bin in self.bins:
            bin.slack = total_weight

    #
    # Register optional branch and bound weighted solver.
    # If it is registered, it 
    def init_branch_and_bound(self):
        soft = [(bin.var, 1) for bin in self.bins]
        self.branch_and_bound = BranchAndBound(self)
        self.branch_and_bound.init(soft)
        for bin in self.bins:
            self.add(bin.var)
        self.add_final(lambda : self.branch_and_bound.final())
        
    def add_bin(self, min_bound):
        assert not self.initialized
        index = len(self.bins)
        bin = Bin(min_bound, index)
        self.bins += [bin]
        return bin
        
    def add_item(self, weight):
        assert not self.initialized
        assert weight > 0
        index = len(self.items)
        item = Item(weight, index)
        self.items += [item]
        return item
        
    def num_items(self):
        return len(self.items)

    def num_bins(self):
        return len(self.bins)
    
    def _num_bits(self):
        log = math.log2(self.num_bins())
        if log.is_integer():
            return True, int(log)
        else:
            return False, int(log) + 1

    def _set_slack(self, bin, slack_value):
        bin.slack = slack_value
        
    def _set_fill(self, bin, fill_value):
        bin.weight = fill_value
        bin.added.pop()

    def _itemvar2item(self, v):
        index  = self.item2index[v.get_id()]
        if index >= len(self.items):
            return None
        return self.items[index]

    def _value2bin(self, value):
        assert isinstance(value, BitVecNumRef)
        bin_index = value.as_long()
        if bin_index >= len(self.bins):
            return NOne
        return self.bins[bin_index]

    def _add_item2bin(self, item, bin):
        # print("add", item, "to", bin)
        old_weight = bin.weight
        bin.weight += item.weight
        bin.added += [item]
        self.trail += [lambda : self._set_fill(bin, old_weight)]
        if old_weight < bin.min_bound and old_weight + item.weight >= bin.min_bound:
            self._propagate_filled(bin)

    # This item can never go into bin
    def _exclude_item2bin(self, item, bin):
        # print("exclude", item, "from", bin)
        # Check if bin has already been blocked
        if bin.slack < bin.min_bound:
            return
        if bin.weight >= bin.min_bound:
            return
        old_slack = bin.slack
        new_slack = old_slack - item.weight
        bin.slack = new_slack
        self.trail += [lambda : self._set_slack(bin, old_slack)]
        # If the new slack does not permit the bin to be filled, propagate
        if new_slack < bin.min_bound:
            self._propagate_slack(bin)
        

    # Callback from Z3 when an item gets fixed.
    def _fixed(self, _item, value):
        if self.branch_and_bound and is_bool(value):
            self.branch_and_bound.fixed(_item, value)
            return 
        item = self._itemvar2item(_item)
        if item is None:
            print("no item for ", _item)
            return
        bin  = self._value2bin(value)
        if bin is None:
            print("no bin for ", value)
            return
        self._add_item2bin(item, bin)
        for idx in range(len(self.bins)):
            if idx == bin.index:
                continue
            other_bin = self.bins[idx]
            self._exclude_item2bin(item, other_bin)

    def _propagate_filled(self, bin):
        """Propagate that bin_index is filled justified by the set of
        items that have been added
        """
        justification = [i.var for i in bin.added]
        self.propagate(bin.var, justification)

    def _propagate_slack(self, bin):
        """Propagate that bin_index cannot be filled"""
        justification = []
        for other_bin in self.bins:
            if other_bin.index == bin.index:
                continue
            justification += other_bin.added
        justification = [item.var for item in justification]
        self.propagate(Not(bin.var), justification)

    def push(self):
        self.lim += [len(self.trail)]

    def pop(self, n):
        head = self.lim[len(self.lim) - n]
        while len(self.trail) > head:
            self.trail[-1]()
            self.trail.pop(-1)
        self.lim = self.lim[0:len(self.lim)-n]                

# Find a first maximally satisfying subset
class MaximalSatisfyingSubset:
    def __init__(self, s):
        self.s = s
        self.model = None

    def tt(self, f): 
        return is_true(self.model.eval(f))

    def get_mss(self, ps):
        s = self.s
        if sat != s.check():
            return []
        self.model = s.model()
        mss = { q for q in ps if self.tt(q) }
        return self._get_mss(mss, ps)

    def _get_mss(self, mss, ps):
        ps = set(ps) - mss
        backbones = set([])
        s = self.s
        while len(ps) > 0:
            p = ps.pop()
            if sat == s.check(mss | backbones | { p }):
                self.model = s.model()
                mss = mss | { p } | { q for q in ps if self.tt(q) }
                ps  = ps - mss
            else:
                backbones = backbones | { Not(p) }
        return mss
    

class OptimizeBinCoverSolver:
    def __init__(self):
        self.solver = Solver()
        self.bin_solver = BinCoverSolver(self.solver)
        self.mss_solver = MaximalSatisfyingSubset(self.solver)

    #
    # Facilities to set up solver
    # First add items and bins.
    # Keep references to the returned objects.
    # Then call init
    # Then add any other custom constraints to the "solver" object.
    #
    def init(self):
        self.bin_solver.init()

    def add_item(self, weight):
        return self.bin_solver.add_item(weight)

    def add_bin(self, min_bound):
        return self.bin_solver.add_bin(min_bound)

    def optimize(self):
        self.init()
        mss = self.mss_solver.get_mss([bin.var for bin in self.bin_solver.bins])
        print(self.mss_solver.model)
        print("filled bins", mss)
        print("bin contents")
        for bin in self.bin_solver.bins:
            print(bin, bin.added)


def example1():
    s = OptimizeBinCoverSolver()
    i1 = s.add_item(2)
    i2 = s.add_item(4)
    i3 = s.add_item(5)
    i4 = s.add_item(2)
    b1 = s.add_bin(3)
    b2 = s.add_bin(6)
    b3 = s.add_bin(1)
    s.optimize()

#example1()


class BranchAndBoundCoverSolver:
    def __init__(self):
        self.solver = Solver()
        self.bin_solver = BinCoverSolver(self.solver)

    def init(self):
        self.bin_solver.init()
        self.bin_solver.init_branch_and_bound()

    def add_item(self, weight):
        return self.bin_solver.add_item(weight)

    def add_bin(self, min_bound):
        return self.bin_solver.add_bin(min_bound)

    def optimize(self):
        self.init()
        self.solver.check()

def example2():
    s = BranchAndBoundCoverSolver()
    i1 = s.add_item(2)
    i2 = s.add_item(4)
    i3 = s.add_item(5)
    i4 = s.add_item(2)
    b1 = s.add_bin(3)
    b2 = s.add_bin(6)
    b3 = s.add_bin(1)
    s.optimize()

example2()
