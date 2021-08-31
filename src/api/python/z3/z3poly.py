############################################
# Copyright (c) 2012 Microsoft Corporation
#
# Z3 Python interface for Z3 polynomials
#
# Author: Leonardo de Moura (leonardo)
############################################

from .z3 import *


def subresultants(p, q, x):
    """
    Return the non-constant subresultants of 'p' and 'q' with respect to the "variable" 'x'.

    'p', 'q' and 'x' are Z3 expressions where 'p' and 'q' are arithmetic terms.
    Note that, any subterm that cannot be viewed as a polynomial is assumed to be a variable.
    Example: f(a) is a considered to be a variable b in the polynomial

    f(a)*f(a) + 2*f(a) + 1

    >>> x, y = Reals('x y')
    >>> subresultants(2*x + y, 3*x - 2*y + 2, x)
    [-7*y + 4]
    >>> r = subresultants(3*y*x**2 + y**3 + 1, 2*x**3 + y + 3, x)
    >>> r[0]
    4*y**9 + 12*y**6 + 27*y**5 + 162*y**4 + 255*y**3 + 4
    >>> r[1]
    -6*y**4 + -6*y
    """
    return AstVector(Z3_polynomial_subresultants(p.ctx_ref(), p.as_ast(), q.as_ast(), x.as_ast()), p.ctx)


if __name__ == "__main__":
    import doctest
    if doctest.testmod().failed:
        exit(1)
