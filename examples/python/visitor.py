# Copyright (c) Microsoft Corporation 2015

from z3 import *

def visitor(e, seen):
    if e in seen:
        return
    seen[e] = True
    yield e
    if is_app(e):
        for ch in e.children():
            for e in visitor(ch, seen):
                yield e
        return
    if is_quantifier(e):
        for e in visitor(e.body(), seen):
            yield e
        return

x, y = Ints('x y')
fml = x + x + y > 2 
seen = {}
for e in visitor(fml, seen):
    if is_const(e) and e.decl().kind() == Z3_OP_UNINTERPRETED:
        print "Variable", e
    else:
        print e
    

