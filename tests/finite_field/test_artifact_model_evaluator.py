#!/usr/bin/env python3
"""Check the independent model evaluator against Z3's established BV semantics.

Exhaustive small widths include division by zero, signed comparisons and shifts
beyond the word size. These cases matter when validating mixed BV/field models.
Run with this branch's Python bindings and shared library on the search path.
"""
import z3
from validate_artifact_models import BV, evaluate


def main():
    ops = {'bvadd': lambda x,y:x+y, 'bvsub': lambda x,y:x-y,
           'bvmul': lambda x,y:x*y, 'bvand': lambda x,y:x&y,
           'bvor': lambda x,y:x|y, 'bvxor': lambda x,y:x^y,
           'bvudiv': z3.UDiv, 'bvurem': z3.URem,
           'bvshl': lambda x,y:x<<y, 'bvlshr': z3.LShR, 'bvashr': lambda x,y:x>>y,
           'bvult': z3.ULT, 'bvule': z3.ULE, 'bvugt': z3.UGT, 'bvuge': z3.UGE,
           'bvslt': lambda x,y:x<y, 'bvsle': lambda x,y:x<=y,
           'bvsgt': lambda x,y:x>y, 'bvsge': lambda x,y:x>=y}
    checks=0
    for width in range(1,5):
        for a in range(1<<width):
            for b in range(1<<width):
                for name, op in ops.items():
                    got=evaluate([name,'a','b'],{'a':BV(a,width),'b':BV(b,width)},7)
                    expected=z3.simplify(op(z3.BitVecVal(a,width),z3.BitVecVal(b,width)))
                    expected=z3.is_true(expected) if z3.is_bool(expected) else BV(expected.as_long(),width)
                    assert got==expected,(name,width,a,b,got,expected)
                    checks+=1
    # Simultaneous let bindings must refer to the outer environment.
    assert evaluate(['let',[['a','b'],['b','a']],['=','a','b']],{'a':1,'b':2},7) is False
    assert evaluate(['let',[['a','b'],['b','a']],'b'],{'a':1,'b':2},7)==1
    print(checks,'exhaustive BV checks and simultaneous-let checks passed')


if __name__=='__main__':main()
