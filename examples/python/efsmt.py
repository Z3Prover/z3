from z3 import *
from z3.z3util import get_vars

'''
Modified from the example in  pysmt
https://github.com/pysmt/pysmt/blob/97088bf3b0d64137c3099ef79a4e153b10ccfda7/examples/efsmt.py
'''

def efsmt(ys, phi, maxloops = None):
    """Solving exists xs. forall ys. phi(x, y)"""
    xs = [x for x in get_vars(phi) if x not in ys]
    E = Solver()
    F = Solver()
    E.add(BoolVal(True))
    loops = 0
    while maxloops is None or loops <= maxloops:
        loops += 1
        eres = E.check()
        if eres == sat:
            emodel = E.model()
            sub_phi = substitute(phi, [(x, emodel.eval(x, True)) for x in xs])
            F.push()
            F.add(Not(sub_phi))
            fres = F.check()
            if fres == sat:
                fmodel = F.model()
                sub_phi = substitute(phi, [(y, fmodel.eval(y, True)) for y in ys])
                E.add(sub_phi)
            else:
                return fres, [(x, emodel.eval(x, True)) for x in xs]
            F.pop()
        else:
            return eres
    return unknown

x, y, z = Reals("x y z")
print(efsmt([y], Implies(And(y > 0, y < 10), y - 2 * x < 7)))
print(efsmt([y], And(y > 3, x == 1)))
