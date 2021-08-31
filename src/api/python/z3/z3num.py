############################################
# Copyright (c) 2012 Microsoft Corporation
#
# Z3 Python interface for Z3 numerals
#
# Author: Leonardo de Moura (leonardo)
############################################
from .z3 import *
from .z3core import *
from .z3printer import *
from fractions import Fraction

from .z3 import _get_ctx


def _to_numeral(num, ctx=None):
    if isinstance(num, Numeral):
        return num
    else:
        return Numeral(num, ctx)


class Numeral:
    """
    A Z3 numeral can be used to perform computations over arbitrary
    precision integers, rationals and real algebraic numbers.
    It also automatically converts python numeric values.

    >>> Numeral(2)
    2
    >>> Numeral("3/2") + 1
    5/2
    >>> Numeral(Sqrt(2))
    1.4142135623?
    >>> Numeral(Sqrt(2)) + 2
    3.4142135623?
    >>> Numeral(Sqrt(2)) + Numeral(Sqrt(3))
    3.1462643699?

    Z3 numerals can be used to perform computations with
    values in a Z3 model.

    >>> s = Solver()
    >>> x = Real('x')
    >>> s.add(x*x == 2)
    >>> s.add(x > 0)
    >>> s.check()
    sat
    >>> m = s.model()
    >>> m[x]
    1.4142135623?
    >>> m[x] + 1
    1.4142135623? + 1

    The previous result is a Z3 expression.

    >>> (m[x] + 1).sexpr()
    '(+ (root-obj (+ (^ x 2) (- 2)) 2) 1.0)'

    >>> Numeral(m[x]) + 1
    2.4142135623?
    >>> Numeral(m[x]).is_pos()
    True
    >>> Numeral(m[x])**2
    2

    We can also isolate the roots of polynomials.

    >>> x0, x1, x2 = RealVarVector(3)
    >>> r0 = isolate_roots(x0**5 - x0 - 1)
    >>> r0
    [1.1673039782?]

    In the following example, we are isolating the roots
    of a univariate polynomial (on x1) obtained after substituting
    x0 -> r0[0]

    >>> r1 = isolate_roots(x1**2 - x0 + 1, [ r0[0] ])
    >>> r1
    [-0.4090280898?, 0.4090280898?]

    Similarly, in the next example we isolate the roots of
    a univariate polynomial (on x2) obtained after substituting
    x0 -> r0[0] and x1 -> r1[0]

    >>> isolate_roots(x1*x2 + x0, [ r0[0], r1[0] ])
    [2.8538479564?]

    """

    def __init__(self, num, ctx=None):
        if isinstance(num, Ast):
            self.ast = num
            self.ctx = _get_ctx(ctx)
        elif isinstance(num, RatNumRef) or isinstance(num, AlgebraicNumRef):
            self.ast = num.ast
            self.ctx = num.ctx
        elif isinstance(num, ArithRef):
            r = simplify(num)
            self.ast = r.ast
            self.ctx = r.ctx
        else:
            v = RealVal(num, ctx)
            self.ast = v.ast
            self.ctx = v.ctx
        Z3_inc_ref(self.ctx_ref(), self.as_ast())
        assert Z3_algebraic_is_value(self.ctx_ref(), self.ast)

    def __del__(self):
        Z3_dec_ref(self.ctx_ref(), self.as_ast())

    def is_integer(self):
        """ Return True if the numeral is integer.

        >>> Numeral(2).is_integer()
        True
        >>> (Numeral(Sqrt(2)) * Numeral(Sqrt(2))).is_integer()
        True
        >>> Numeral(Sqrt(2)).is_integer()
        False
        >>> Numeral("2/3").is_integer()
        False
        """
        return self.is_rational() and self.denominator() == 1

    def is_rational(self):
        """ Return True if the numeral is rational.

        >>> Numeral(2).is_rational()
        True
        >>> Numeral("2/3").is_rational()
        True
        >>> Numeral(Sqrt(2)).is_rational()
        False

        """
        return Z3_get_ast_kind(self.ctx_ref(), self.as_ast()) == Z3_NUMERAL_AST

    def denominator(self):
        """ Return the denominator if `self` is rational.

        >>> Numeral("2/3").denominator()
        3
        """
        assert(self.is_rational())
        return Numeral(Z3_get_denominator(self.ctx_ref(), self.as_ast()), self.ctx)

    def numerator(self):
        """ Return the numerator if `self` is rational.

        >>> Numeral("2/3").numerator()
        2
        """
        assert(self.is_rational())
        return Numeral(Z3_get_numerator(self.ctx_ref(), self.as_ast()), self.ctx)

    def is_irrational(self):
        """ Return True if the numeral is irrational.

        >>> Numeral(2).is_irrational()
        False
        >>> Numeral("2/3").is_irrational()
        False
        >>> Numeral(Sqrt(2)).is_irrational()
        True
        """
        return not self.is_rational()

    def as_long(self):
        """ Return a numeral (that is an integer) as a Python long.

        """
        assert(self.is_integer())
        if sys.version_info.major >= 3:
            return int(Z3_get_numeral_string(self.ctx_ref(), self.as_ast()))
        else:
            return long(Z3_get_numeral_string(self.ctx_ref(), self.as_ast()))

    def as_fraction(self):
        """ Return a numeral (that is a rational) as a Python Fraction.
        >>> Numeral("1/5").as_fraction()
        Fraction(1, 5)
        """
        assert(self.is_rational())
        return Fraction(self.numerator().as_long(), self.denominator().as_long())

    def approx(self, precision=10):
        """Return a numeral that approximates the numeral `self`.
        The result `r` is such that |r - self| <= 1/10^precision

        If `self` is rational, then the result is `self`.

        >>> x = Numeral(2).root(2)
        >>> x.approx(20)
        6838717160008073720548335/4835703278458516698824704
        >>> x.approx(5)
        2965821/2097152
        >>> Numeral(2).approx(10)
        2
        """
        return self.upper(precision)

    def upper(self, precision=10):
        """Return a upper bound that approximates the numeral `self`.
        The result `r` is such that r - self <= 1/10^precision

        If `self` is rational, then the result is `self`.

        >>> x = Numeral(2).root(2)
        >>> x.upper(20)
        6838717160008073720548335/4835703278458516698824704
        >>> x.upper(5)
        2965821/2097152
        >>> Numeral(2).upper(10)
        2
        """
        if self.is_rational():
            return self
        else:
            return Numeral(Z3_get_algebraic_number_upper(self.ctx_ref(), self.as_ast(), precision), self.ctx)

    def lower(self, precision=10):
        """Return a lower bound that approximates the numeral `self`.
        The result `r` is such that self - r <= 1/10^precision

        If `self` is rational, then the result is `self`.

        >>> x = Numeral(2).root(2)
        >>> x.lower(20)
        1709679290002018430137083/1208925819614629174706176
        >>> Numeral("2/3").lower(10)
        2/3
        """
        if self.is_rational():
            return self
        else:
            return Numeral(Z3_get_algebraic_number_lower(self.ctx_ref(), self.as_ast(), precision), self.ctx)

    def sign(self):
        """ Return the sign of the numeral.

        >>> Numeral(2).sign()
        1
        >>> Numeral(-3).sign()
        -1
        >>> Numeral(0).sign()
        0
        """
        return Z3_algebraic_sign(self.ctx_ref(), self.ast)

    def is_pos(self):
        """ Return True if the numeral is positive.

        >>> Numeral(2).is_pos()
        True
        >>> Numeral(-3).is_pos()
        False
        >>> Numeral(0).is_pos()
        False
        """
        return Z3_algebraic_is_pos(self.ctx_ref(), self.ast)

    def is_neg(self):
        """ Return True if the numeral is negative.

        >>> Numeral(2).is_neg()
        False
        >>> Numeral(-3).is_neg()
        True
        >>> Numeral(0).is_neg()
        False
        """
        return Z3_algebraic_is_neg(self.ctx_ref(), self.ast)

    def is_zero(self):
        """ Return True if the numeral is zero.

        >>> Numeral(2).is_zero()
        False
        >>> Numeral(-3).is_zero()
        False
        >>> Numeral(0).is_zero()
        True
        >>> sqrt2 = Numeral(2).root(2)
        >>> sqrt2.is_zero()
        False
        >>> (sqrt2 - sqrt2).is_zero()
        True
        """
        return Z3_algebraic_is_zero(self.ctx_ref(), self.ast)

    def __add__(self, other):
        """ Return the numeral `self + other`.

        >>> Numeral(2) + 3
        5
        >>> Numeral(2) + Numeral(4)
        6
        >>> Numeral("2/3") + 1
        5/3
        """
        return Numeral(Z3_algebraic_add(self.ctx_ref(), self.ast, _to_numeral(other, self.ctx).ast), self.ctx)

    def __radd__(self, other):
        """ Return the numeral `other + self`.

        >>> 3 + Numeral(2)
        5
        """
        return Numeral(Z3_algebraic_add(self.ctx_ref(), self.ast, _to_numeral(other, self.ctx).ast), self.ctx)

    def __sub__(self, other):
        """ Return the numeral `self - other`.

        >>> Numeral(2) - 3
        -1
        """
        return Numeral(Z3_algebraic_sub(self.ctx_ref(), self.ast, _to_numeral(other, self.ctx).ast), self.ctx)

    def __rsub__(self, other):
        """ Return the numeral `other - self`.

        >>> 3 - Numeral(2)
        1
        """
        return Numeral(Z3_algebraic_sub(self.ctx_ref(), _to_numeral(other, self.ctx).ast, self.ast), self.ctx)

    def __mul__(self, other):
        """ Return the numeral `self * other`.
        >>> Numeral(2) * 3
        6
        """
        return Numeral(Z3_algebraic_mul(self.ctx_ref(), self.ast, _to_numeral(other, self.ctx).ast), self.ctx)

    def __rmul__(self, other):
        """ Return the numeral `other * mul`.
        >>> 3 * Numeral(2)
        6
        """
        return Numeral(Z3_algebraic_mul(self.ctx_ref(), self.ast, _to_numeral(other, self.ctx).ast), self.ctx)

    def __div__(self, other):
        """ Return the numeral `self / other`.
        >>> Numeral(2) / 3
        2/3
        >>> Numeral(2).root(2) / 3
        0.4714045207?
        >>> Numeral(Sqrt(2)) / Numeral(Sqrt(3))
        0.8164965809?
        """
        return Numeral(Z3_algebraic_div(self.ctx_ref(), self.ast, _to_numeral(other, self.ctx).ast), self.ctx)

    def __truediv__(self, other):
        return self.__div__(other)

    def __rdiv__(self, other):
        """ Return the numeral `other / self`.
        >>> 3 / Numeral(2)
        3/2
        >>> 3 / Numeral(2).root(2)
        2.1213203435?
        """
        return Numeral(Z3_algebraic_div(self.ctx_ref(), _to_numeral(other, self.ctx).ast, self.ast), self.ctx)

    def __rtruediv__(self, other):
        return self.__rdiv__(other)

    def root(self, k):
        """ Return the numeral `self^(1/k)`.

        >>> sqrt2 = Numeral(2).root(2)
        >>> sqrt2
        1.4142135623?
        >>> sqrt2 * sqrt2
        2
        >>> sqrt2 * 2 + 1
        3.8284271247?
        >>> (sqrt2 * 2 + 1).sexpr()
        '(root-obj (+ (^ x 2) (* (- 2) x) (- 7)) 2)'
        """
        return Numeral(Z3_algebraic_root(self.ctx_ref(), self.ast, k), self.ctx)

    def power(self, k):
        """ Return the numeral `self^k`.

        >>> sqrt3 = Numeral(3).root(2)
        >>> sqrt3
        1.7320508075?
        >>> sqrt3.power(2)
        3
        """
        return Numeral(Z3_algebraic_power(self.ctx_ref(), self.ast, k), self.ctx)

    def __pow__(self, k):
        """ Return the numeral `self^k`.

        >>> sqrt3 = Numeral(3).root(2)
        >>> sqrt3
        1.7320508075?
        >>> sqrt3**2
        3
        """
        return self.power(k)

    def __lt__(self, other):
        """ Return True if `self < other`.

        >>> Numeral(Sqrt(2)) < 2
        True
        >>> Numeral(Sqrt(3)) < Numeral(Sqrt(2))
        False
        >>> Numeral(Sqrt(2)) < Numeral(Sqrt(2))
        False
        """
        return Z3_algebraic_lt(self.ctx_ref(), self.ast, _to_numeral(other, self.ctx).ast)

    def __rlt__(self, other):
        """ Return True if `other < self`.

        >>> 2 < Numeral(Sqrt(2))
        False
        """
        return self > other

    def __gt__(self, other):
        """ Return True if `self > other`.

        >>> Numeral(Sqrt(2)) > 2
        False
        >>> Numeral(Sqrt(3)) > Numeral(Sqrt(2))
        True
        >>> Numeral(Sqrt(2)) > Numeral(Sqrt(2))
        False
        """
        return Z3_algebraic_gt(self.ctx_ref(), self.ast, _to_numeral(other, self.ctx).ast)

    def __rgt__(self, other):
        """ Return True if `other > self`.

        >>> 2 > Numeral(Sqrt(2))
        True
        """
        return self < other

    def __le__(self, other):
        """ Return True if `self <= other`.

        >>> Numeral(Sqrt(2)) <= 2
        True
        >>> Numeral(Sqrt(3)) <= Numeral(Sqrt(2))
        False
        >>> Numeral(Sqrt(2)) <= Numeral(Sqrt(2))
        True
        """
        return Z3_algebraic_le(self.ctx_ref(), self.ast, _to_numeral(other, self.ctx).ast)

    def __rle__(self, other):
        """ Return True if `other <= self`.

        >>> 2 <= Numeral(Sqrt(2))
        False
        """
        return self >= other

    def __ge__(self, other):
        """ Return True if `self >= other`.

        >>> Numeral(Sqrt(2)) >= 2
        False
        >>> Numeral(Sqrt(3)) >= Numeral(Sqrt(2))
        True
        >>> Numeral(Sqrt(2)) >= Numeral(Sqrt(2))
        True
        """
        return Z3_algebraic_ge(self.ctx_ref(), self.ast, _to_numeral(other, self.ctx).ast)

    def __rge__(self, other):
        """ Return True if `other >= self`.

        >>> 2 >= Numeral(Sqrt(2))
        True
        """
        return self <= other

    def __eq__(self, other):
        """ Return True if `self == other`.

        >>> Numeral(Sqrt(2)) == 2
        False
        >>> Numeral(Sqrt(3)) == Numeral(Sqrt(2))
        False
        >>> Numeral(Sqrt(2)) == Numeral(Sqrt(2))
        True
        """
        return Z3_algebraic_eq(self.ctx_ref(), self.ast, _to_numeral(other, self.ctx).ast)

    def __ne__(self, other):
        """ Return True if `self != other`.

        >>> Numeral(Sqrt(2)) != 2
        True
        >>> Numeral(Sqrt(3)) != Numeral(Sqrt(2))
        True
        >>> Numeral(Sqrt(2)) != Numeral(Sqrt(2))
        False
        """
        return Z3_algebraic_neq(self.ctx_ref(), self.ast, _to_numeral(other, self.ctx).ast)

    def __str__(self):
        if Z3_is_numeral_ast(self.ctx_ref(), self.ast):
            return str(RatNumRef(self.ast, self.ctx))
        else:
            return str(AlgebraicNumRef(self.ast, self.ctx))

    def __repr__(self):
        return self.__str__()

    def sexpr(self):
        return Z3_ast_to_string(self.ctx_ref(), self.as_ast())

    def as_ast(self):
        return self.ast

    def ctx_ref(self):
        return self.ctx.ref()


def eval_sign_at(p, vs):
    """
    Evaluate the sign of the polynomial `p` at `vs`.  `p` is a Z3
    Expression containing arithmetic operators: +, -, *, ^k where k is
    an integer; and free variables x that is_var(x) is True. Moreover,
    all variables must be real.

    The result is 1 if the polynomial is positive at the given point,
    -1 if negative, and 0 if zero.

    >>> x0, x1, x2 = RealVarVector(3)
    >>> eval_sign_at(x0**2 + x1*x2 + 1, (Numeral(0), Numeral(1), Numeral(2)))
    1
    >>> eval_sign_at(x0**2 - 2, [ Numeral(Sqrt(2)) ])
    0
    >>> eval_sign_at((x0 + x1)*(x0 + x2), (Numeral(0), Numeral(Sqrt(2)), Numeral(Sqrt(3))))
    1
    """
    num = len(vs)
    _vs = (Ast * num)()
    for i in range(num):
        _vs[i] = vs[i].ast
    return Z3_algebraic_eval(p.ctx_ref(), p.as_ast(), num, _vs)


def isolate_roots(p, vs=[]):
    """
    Given a multivariate polynomial p(x_0, ..., x_{n-1}, x_n), returns the
    roots of the univariate polynomial p(vs[0], ..., vs[len(vs)-1], x_n).

    Remarks:
    * p is a Z3 expression that contains only arithmetic terms and free variables.
    * forall i in [0, n) vs is a numeral.

    The result is a list of numerals

    >>> x0 = RealVar(0)
    >>> isolate_roots(x0**5 - x0 - 1)
    [1.1673039782?]
    >>> x1 = RealVar(1)
    >>> isolate_roots(x0**2 - x1**4 - 1, [ Numeral(Sqrt(3)) ])
    [-1.1892071150?, 1.1892071150?]
    >>> x2 = RealVar(2)
    >>> isolate_roots(x2**2 + x0 - x1, [ Numeral(Sqrt(3)), Numeral(Sqrt(2)) ])
    []
    """
    num = len(vs)
    _vs = (Ast * num)()
    for i in range(num):
        _vs[i] = vs[i].ast
    _roots = AstVector(Z3_algebraic_roots(p.ctx_ref(), p.as_ast(), num, _vs), p.ctx)
    return [Numeral(r) for r in _roots]
