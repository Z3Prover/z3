############################################
# Copyright (c) 2013 Microsoft Corporation
# 
# Z3 Python interface for Z3 Real Closed Fields
# that may contain 
#    - computable transcendentals
#    - infinitesimals
#    - algebraic extensions
#
# Author: Leonardo de Moura (leonardo)
############################################
from .z3 import *
from .z3core import *
from .z3printer import *
from fractions import Fraction

def _to_rcfnum(num, ctx=None):
    if isinstance(num, RCFNum):
        return num
    else:
        return RCFNum(num, ctx)

def Pi(ctx=None):
    ctx = z3._get_ctx(ctx)
    return RCFNum(Z3_rcf_mk_pi(ctx.ref()), ctx)

def E(ctx=None):
    ctx = z3._get_ctx(ctx)
    return RCFNum(Z3_rcf_mk_e(ctx.ref()), ctx)

def MkInfinitesimal(name="eps", ctx=None):
    # Todo: remove parameter name.
    # For now, we keep it for backward compatibility.
    ctx = z3._get_ctx(ctx)
    return RCFNum(Z3_rcf_mk_infinitesimal(ctx.ref()), ctx)

def MkRoots(p, ctx=None):
    ctx = z3._get_ctx(ctx)
    num = len(p)
    _tmp = [] 
    _as  = (RCFNumObj * num)()
    _rs  = (RCFNumObj * num)() 
    for i in range(num):
        _a = _to_rcfnum(p[i], ctx)
        _tmp.append(_a) # prevent GC
        _as[i] = _a.num
    nr = Z3_rcf_mk_roots(ctx.ref(), num, _as, _rs)
    r  = []
    for i in range(nr):
        r.append(RCFNum(_rs[i], ctx))
    return r

class RCFNum:
    def __init__(self, num, ctx=None):
        # TODO: add support for converting AST numeral values into RCFNum
        if isinstance(num, RCFNumObj):
            self.num = num
            self.ctx = z3._get_ctx(ctx)
        else:
            self.ctx = z3._get_ctx(ctx)
            self.num = Z3_rcf_mk_rational(self.ctx_ref(), str(num))

    def __del__(self):
        Z3_rcf_del(self.ctx_ref(), self.num)

    def ctx_ref(self):
        return self.ctx.ref()
                  
    def __repr__(self):
        return Z3_rcf_num_to_string(self.ctx_ref(), self.num, False, in_html_mode())

    def compact_str(self):
        return Z3_rcf_num_to_string(self.ctx_ref(), self.num, True, in_html_mode())

    def __add__(self, other):
        v = _to_rcfnum(other, self.ctx)
        return RCFNum(Z3_rcf_add(self.ctx_ref(), self.num, v.num), self.ctx)

    def __radd__(self, other):
        v = _to_rcfnum(other, self.ctx)
        return RCFNum(Z3_rcf_add(self.ctx_ref(), v.num, self.num), self.ctx)

    def __mul__(self, other):
        v = _to_rcfnum(other, self.ctx)
        return RCFNum(Z3_rcf_mul(self.ctx_ref(), self.num, v.num), self.ctx)

    def __rmul__(self, other):
        v = _to_rcfnum(other, self.ctx)
        return RCFNum(Z3_rcf_mul(self.ctx_ref(), v.num, self.num), self.ctx)

    def __sub__(self, other):
        v = _to_rcfnum(other, self.ctx)
        return RCFNum(Z3_rcf_sub(self.ctx_ref(), self.num, v.num), self.ctx)

    def __rsub__(self, other):
        v = _to_rcfnum(other, self.ctx)
        return RCFNum(Z3_rcf_sub(self.ctx_ref(), v.num, self.num), self.ctx)

    def __div__(self, other):
        v = _to_rcfnum(other, self.ctx)
        return RCFNum(Z3_rcf_div(self.ctx_ref(), self.num, v.num), self.ctx)

    def __rdiv__(self, other):
        v = _to_rcfnum(other, self.ctx)
        return RCFNum(Z3_rcf_div(self.ctx_ref(), v.num, self.num), self.ctx)

    def __neg__(self):
        return self.__rsub__(0)

    def power(self, k):
        return RCFNum(Z3_rcf_power(self.ctx_ref(), self.num, k), self.ctx)

    def __pow__(self, k):
        return self.power(k)
 
    def decimal(self, prec=5):
        return Z3_rcf_num_to_decimal_string(self.ctx_ref(), self.num, prec)
    
    def __lt__(self, other):
        v = _to_rcfnum(other, self.ctx)
        return Z3_rcf_lt(self.ctx_ref(), self.num, v.num)

    def __rlt__(self, other):
        v = _to_rcfnum(other, self.ctx)
        return Z3_rcf_lt(self.ctx_ref(), v.num, self.num)

    def __gt__(self, other):
        v = _to_rcfnum(other, self.ctx)
        return Z3_rcf_gt(self.ctx_ref(), self.num, v.num)

    def __rgt__(self, other):
        v = _to_rcfnum(other, self.ctx)
        return Z3_rcf_gt(self.ctx_ref(), v.num, self.num)

    def __le__(self, other):
        v = _to_rcfnum(other, self.ctx)
        return Z3_rcf_le(self.ctx_ref(), self.num, v.num)

    def __rle__(self, other):
        v = _to_rcfnum(other, self.ctx)
        return Z3_rcf_le(self.ctx_ref(), v.num, self.num)

    def __ge__(self, other):
        v = _to_rcfnum(other, self.ctx)
        return Z3_rcf_ge(self.ctx_ref(), self.num, v.num)

    def __rge__(self, other):
        v = _to_rcfnum(other, self.ctx)
        return Z3_rcf_ge(self.ctx_ref(), v.num, self.num)

    def __eq__(self, other):
        v = _to_rcfnum(other, self.ctx)
        return Z3_rcf_eq(self.ctx_ref(), self.num, v.num)

    def __ne__(self, other):
        v = _to_rcfnum(other, self.ctx)
        return Z3_rcf_neq(self.ctx_ref(), self.num, v.num)

    def split(self):
        n = (RCFNumObj * 1)()
        d = (RCFNumObj * 1)()
        Z3_rcf_get_numerator_denominator(self.ctx_ref(), self.num, n, d)
        return (RCFNum(n[0], self.ctx), RCFNum(d[0], self.ctx))
