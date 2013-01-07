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
from z3 import *
from z3core import *
from z3printer import *
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
    ctx = z3._get_ctx(ctx)
    return RCFNum(Z3_rcf_mk_infinitesimal(ctx.ref(), name), ctx)

class RCFNum:
    def __init__(self, num, ctx=None):
        # TODO: add support for converting AST numeral values into RCFNum
        if isinstance(num, RCFNumObj):
            self.num = num
            self.ctx = z3._get_ctx(ctx)
        else:
            self.ctx = z3._get_ctx(ctx)
            self.num = Z3_rcf_mk_rational(self.ctx_ref(), str(num))
        Z3_rcf_inc_ref(self.ctx_ref(), self.num)

    def __del__(self):
        Z3_rcf_dec_ref(self.ctx_ref(), self.num)

    def ctx_ref(self):
        return self.ctx.ref()
                  
    def __repr__(self):
        return Z3_rcf_num_to_string(self.ctx_ref(), self.num)

    def __add__(self, other):
        return RCFNum(Z3_rcf_add(self.ctx_ref(), self.num, _to_rcfnum(other, self.ctx).num), self.ctx)

    def __radd__(self, other):
        return RCFNum(Z3_rcf_add(self.ctx_ref(), _to_rcfnum(other, self.ctx).num, self.num), self.ctx)

    def __mul__(self, other):
        return RCFNum(Z3_rcf_mul(self.ctx_ref(), self.num, _to_rcfnum(other, self.ctx).num), self.ctx)

    def __rmul__(self, other):
        return RCFNum(Z3_rcf_mul(self.ctx_ref(), _to_rcfnum(other, self.ctx).num, self.num), self.ctx)

    def __sub__(self, other):
        return RCFNum(Z3_rcf_sub(self.ctx_ref(), self.num, _to_rcfnum(other, self.ctx).num), self.ctx)

    def __rsub__(self, other):
        return RCFNum(Z3_rcf_sub(self.ctx_ref(), _to_rcfnum(other, self.ctx).num, self.num), self.ctx)

    def __div__(self, other):
        return RCFNum(Z3_rcf_div(self.ctx_ref(), self.num, _to_rcfnum(other, self.ctx).num), self.ctx)

    def __rdiv__(self, other):
        return RCFNum(Z3_rcf_div(self.ctx_ref(), _to_rcfnum(other, self.ctx).num, self.num), self.ctx)

    def __neg__(self):
        return self.__rsub__(0)

    def decimal(self, prec=5):
        return Z3_rcf_num_to_decimal_string(self.ctx_ref(), self.num, prec)
    
    def __lt__(self, other):
        return Z3_rcf_lt(self.ctx_ref(), self.num, _to_rcfnum(other, self.ctx).num)

    def __rlt__(self, other):
        return Z3_rcf_lt(self.ctx_ref(), _to_rcfnum(other, self.ctx).num, self.num)

    def __gt__(self, other):
        return Z3_rcf_gt(self.ctx_ref(), self.num, _to_rcfnum(other, self.ctx).num)

    def __rgt__(self, other):
        return Z3_rcf_gt(self.ctx_ref(), _to_rcfnum(other, self.ctx).num, self.num)

    def __le__(self, other):
        return Z3_rcf_le(self.ctx_ref(), self.num, _to_rcfnum(other, self.ctx).num)

    def __rle__(self, other):
        return Z3_rcf_le(self.ctx_ref(), _to_rcfnum(other, self.ctx).num, self.num)

    def __ge__(self, other):
        return Z3_rcf_ge(self.ctx_ref(), self.num, _to_rcfnum(other, self.ctx).num)

    def __rge__(self, other):
        return Z3_rcf_ge(self.ctx_ref(), _to_rcfnum(other, self.ctx).num, self.num)

    def __eq__(self, other):
        return Z3_rcf_eq(self.ctx_ref(), self.num, _to_rcfnum(other, self.ctx).num)

    def __ne__(self, other):
        return Z3_rcf_neq(self.ctx_ref(), self.num, _to_rcfnum(other, self.ctx).num)

