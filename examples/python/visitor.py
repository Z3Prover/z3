# Copyright (c) Microsoft Corporation 2015
from __future__ import print_function
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

def modify(e, fn):
    seen = {}
    def visit(e):
        if e in seen:
            pass
        elif fn(e) is not None:
            seen[e] = fn(e)
        elif is_and(e):
            chs = [visit(ch) for ch in e.children()]
            seen[e] = And(chs)
        elif is_or(e):
            chs = [visit(ch) for ch in e.children()]
            seen[e] = Or(chs)
        elif is_app(e):
            chs = [visit(ch) for ch in e.children()]
            seen[e] = e.decl()(chs)
        elif is_quantifier(e):
            # Note: does not work for Lambda that requires a separate case
            body = visit(e.body())            
            is_forall = e.is_forall()
            num_pats = e.num_patterns()
            pats = (Pattern * num_pats)()
            for i in range(num_pats):
                pats[i] = e.pattern(i).ast

            num_decls = e.num_vars()
            sorts = (Sort * num_decls)()
            names = (Symbol * num_decls)()
            for i in range(num_decls):
                sorts[i] = e.var_sort(i).ast
                names[i] = to_symbol(e.var_name(i), e.ctx)
            r = QuantifierRef(Z3_mk_quantifier(e.ctx_ref(), is_forall, e.weight(), num_pats, pats, num_decls, sorts, names, body.ast), e.ctx)
            seen[e] = r            
        else:
            seen[e] = e
        return seen[e]
    return visit(e)

if __name__ == "__main__":
    x, y = Ints('x y')
    fml = x + x + y > 2 
    seen = {}
    for e in visitor(fml, seen):
        if is_const(e) and e.decl().kind() == Z3_OP_UNINTERPRETED:
            print("Variable", e)
        else:
            print(e)

    s = SolverFor("HORN")
    inv = Function('inv', IntSort(), IntSort(), BoolSort())
    i, ip, j, jp = Ints('i ip j jp')
    s.add(ForAll([i, j], Implies(i == 0, inv(i, j))))
    s.add(ForAll([i, ip, j, jp], Implies(And(inv(i, j), i < 10, ip == i + 1), inv(ip, jp))))
    s.add(ForAll([i, j], Implies(And(inv(i, j), i >= 10),  i == 10)))

    a0, a1, a2 = Ints('a0 a1 a2')
    b0, b1, b2 = Ints('b0 b1 b2')
    x = Var(0, IntSort())
    y = Var(1, IntSort())
    template = And(a0 + a1*x + a2*y >= 0, b0 + b1*x + b2*y >= 0)    
    def update(e):
        if is_app(e) and eq(e.decl(), inv):
            return substitute_vars(template, (e.arg(0)), e.arg(1))
        return None
    for f in s.assertions():
        f_new = modify(f, update)
        print(f_new)

