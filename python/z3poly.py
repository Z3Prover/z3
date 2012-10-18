############################################
# Copyright (c) 2012 Microsoft Corporation
# 
# Z3 Polynomial interface
#
# Author: Leonardo de Moura (leonardo)
############################################
from z3 import *

class PolynomialManager:
    """Polynomial Manager.
    """
    def __init__(self, ctx=None):
        self.ctx     = z3._get_ctx(ctx)
        self.manager = Z3_mk_polynomial_manager(self.ctx_ref())
        
    def __del__(self):
        Z3_del_polynomial_manager(self.ctx_ref(), self.manager)

    def ctx_ref(self):
        return self.ctx.ref()

    def m(self):
        return self.manager

_main_pmanager = None
def main_pmanager():
    """Return a reference to the global Polynomial manager.
    """
    global _main_pmanager
    if _main_pmanager == None:
        _main_pmanager = PolynomialManager()
    return _main_pmanager  

def _get_pmanager(ctx):
    if ctx == None:
        return main_pmanager()
    else:
        return ctx

class Polynomial:
    """Multivariate polynomials.
    """
    def __init__(self, poly=None, m=None):
        self.pmanager = _get_pmanager(m)
        if poly == None:
            self.poly = Z3_mk_zero_polynomial(self.ctx_ref(), self.m())
        else:
            self.poly = poly
        Z3_polynomial_inc_ref(self.ctx_ref(), self.m(), self.poly)
    
    def __del__(self):
        Z3_polynomial_dec_ref(self.ctx_ref(), self.m(), self.poly)

    def m(self):
        return self.pmanager.m()

    def ctx_ref(self):
        return self.pmanager.ctx_ref()
    
    def __repr__(self):
        return Z3_polynomial_to_string(self.ctx_ref(), self.m(), self.poly)

# test
p = Polynomial()
print p

