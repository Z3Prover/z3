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
    esolver.add(BoolVal(True))
    loops = 0
    while maxloops is None or loops <= maxloops:
        loops += 1
        eres = esolver.check()
        if eres == unsat:
            return unsat
        else:
            emodel = esolver.model()
            x_mappings = [(var, emodel.eval(var, model_completion=True)) for var in x]
            sub_phi = simplify(substitute(phi, x_mappings))
               
            fsolver = Solver()
            fsolver.add(Not(sub_phi))
            if fsolver.check() == sat:
                fmodel = fsolver.model()
                y_mappings = [(var, fmodel.eval(var, model_completion=True)) for var in y]
                sub_phi = simplify(substitute(phi, y_mappings))
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
