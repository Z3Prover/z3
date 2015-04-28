############################################
# Copyright (c) 2012 Microsoft Corporation
# 
# Complex numbers in Z3
# See http://research.microsoft.com/en-us/um/people/leonardo/blog/2013/01/26/complex.html 
#
# Author: Leonardo de Moura (leonardo)
############################################
from z3 import *

def _to_complex(a):
    if isinstance(a, ComplexExpr):
        return a
    else:
        return ComplexExpr(a, RealVal(0))

def _is_zero(a):
    return (isinstance(a, int) and a == 0) or (is_rational_value(a) and a.numerator_as_long() == 0)

class ComplexExpr:
    def __init__(self, r, i):
        self.r = r
        self.i = i

    def __add__(self, other):
        other = _to_complex(other)
        return ComplexExpr(self.r + other.r, self.i + other.i)

    def __radd__(self, other):
        other = _to_complex(other)
        return ComplexExpr(other.r + self.r, other.i + self.i)

    def __sub__(self, other):
        other = _to_complex(other)
        return ComplexExpr(self.r - other.r, self.i - other.i)

    def __rsub__(self, other):
        other = _to_complex(other)
        return ComplexExpr(other.r - self.r, other.i - self.i)

    def __mul__(self, other):
        other = _to_complex(other)
        return ComplexExpr(self.r*other.r - self.i*other.i, self.r*other.i + self.i*other.r)

    def __mul__(self, other):
        other = _to_complex(other)
        return ComplexExpr(other.r*self.r - other.i*self.i, other.i*self.r + other.r*self.i)

    def __pow__(self, k):
	if k == 0:
	    return ComplexExpr(1, 0)
	if k == 1:
	    return self
	if k < 0:
	    return (self ** (-k)).inv()
	return reduce(lambda x, y: x * y, [self for _ in xrange(k)], ComplexExpr(1, 0))

    def inv(self):
        den = self.r*self.r + self.i*self.i
        return ComplexExpr(self.r/den, -self.i/den)

    def __div__(self, other):
        inv_other = _to_complex(other).inv()
        return self.__mul__(inv_other)

    def __rdiv__(self, other):
        other = _to_complex(other)
        return self.inv().__mul__(other)

    def __eq__(self, other):
        other = _to_complex(other)
        return And(self.r == other.r, self.i == other.i)

    def __neq__(self, other):
        return Not(self.__eq__(other))

    def simplify(self):
        return ComplexExpr(simplify(self.r), simplify(self.i))

    def repr_i(self):
        if is_rational_value(self.i):
            return "%s*I" % self.i
        else:
            return "(%s)*I" % str(self.i)

    def __repr__(self):
        if _is_zero(self.i):
            return str(self.r)
        elif _is_zero(self.r):
            return self.repr_i()
        else:
            return "%s + %s" % (self.r, self.repr_i())

def Complex(a):
    return ComplexExpr(Real('%s.r' % a), Real('%s.i' % a))
I = ComplexExpr(RealVal(0), RealVal(1))

def evaluate_cexpr(m, e):
    return ComplexExpr(m[e.r], m[e.i])

x = Complex("x")
s = Tactic('qfnra-nlsat').solver()
s.add(x*x == -2)
print(s)
print(s.check())
m = s.model()
print('x = %s' % evaluate_cexpr(m, x))
print((evaluate_cexpr(m,x)*evaluate_cexpr(m,x)).simplify())
s.add(x.i != -1)
print(s)
print(s.check())
print(s.model())
s.add(x.i != 1)
print(s.check())
# print(s.model())
print ((3 + I) ** 2)/(5 - I)
print ((3 + I) ** -3)/(5 - I)
