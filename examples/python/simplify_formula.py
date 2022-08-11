from z3 import *

def is_atom(t):
    if not is_bool(t):
        return False
    if not is_app(t):
        return False
    k = t.decl().kind()
    if k == Z3_OP_AND or k == Z3_OP_OR or k == Z3_OP_IMPLIES:
        return False
    if k == Z3_OP_EQ and t.arg(0).is_bool():
        return False
    if k == Z3_OP_TRUE or k == Z3_OP_FALSE or k == Z3_OP_XOR or k == Z3_OP_NOT:
        return False
    return True

def atoms(fml):
    visited = set([])
    atms = set([])
    def atoms_rec(t, visited, atms):
        if t in visited:
            return
        visited |= { t }
        if is_atom(t):
            atms |= { t }
        for s in t.children():
            atoms_rec(s, visited, atms)
    atoms_rec(fml, visited, atms)
    return atms

def atom2literal(m, a):
    if is_true(m.eval(a)):
        return a
    return Not(a)

# Extract subset of atoms used to satisfy the negation
# of a formula.
# snot is a solver for Not(fml)
# s    is a solver for fml
# m    is a model for Not(fml)
# evaluate each atom in fml using m and create
# literals corresponding to the sign of the evaluation.
# If the model evaluates atoms to false, the literal is
# negated.
# 
#
def implicant(atoms, s, snot):
    m = snot.model()
    lits = [atom2literal(m, a) for a in atoms]
    is_sat = s.check(lits)
    assert is_sat == unsat
    core = s.unsat_core()
    return Or([mk_not(c) for c in core])

#
# Extract a CNF representation of fml
# The procedure uses two solvers
# Enumerate models for Not(fml)
# Use the enumerated model to identify literals
# that imply Not(fml)
# The CNF of fml is a conjunction of the
# negation of these literals.
#

def to_cnf(fml):
    atms = atoms(fml)
    s = Solver()
    snot = Solver()
    snot.add(Not(fml))
    s.add(fml)

    while sat == snot.check():
        clause = implicant(atms, s, snot)
        yield clause
        snot.add(clause)

        
a, b, c, = Bools('a b c')
fml = Or(And(a, b), And(Not(a), c))

for clause in to_cnf(fml):
    print(clause)
    
