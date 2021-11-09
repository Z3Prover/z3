from z3 import *
from z3.z3util import get_vars

'''
Modified from the example in  pysmt
https://github.com/pysmt/pysmt/blob/97088bf3b0d64137c3099ef79a4e153b10ccfda7/examples/efsmt.py
'''
def efsmt(y, phi, maxloops=None):
    """Solving exists x. forall y. phi(x, y)"""
    vars = get_vars(phi)
    x = [item for item in vars if item not in y]
    esolver = Solver()
    fsolver = Solver()
    esolver.add(BoolVal(True))
    loops = 0
    while maxloops is None or loops <= maxloops:
        loops += 1
        eres = esolver.check()
        if eres == unsat:
            return unsat
        else:
            emodel = esolver.model()
            tau = [emodel.eval(var, True) for var in x]
            sub_phi = phi
            for i in range(len(x)):
                sub_phi = simplify(substitute(sub_phi, (x[i], tau[i])))
            fsolver.add(Not(sub_phi))
            if fsolver.check() == sat:
                fmodel = fsolver.model()
                sigma = [fmodel.eval(v, True) for v in y]
                sub_phi = phi
                for j in range(len(y)):
                    sub_phi = simplify(substitute(sub_phi, (y[j], sigma[j])))
                esolver.add(sub_phi)
            else:
                return sat
    return unknown


def test():
    x, y, z = Reals("x y z")
    fmla = Implies(And(y > 0, y < 10), y - 2 * x < 7)
    fmlb = And(y > 3, x == 1)
    print(efsmt([y], fmla))
    print(efsmt([y], fmlb))
    
test()
