############################################
# Copyright (c) 2012 Microsoft Corporation
#
# Z3 Python interface
#
# Authors: Leonardo de Moura (leonardo)
#          ThanhVu (Vu) Nguyen <tnguyen@cs.unm.edu>
############################################
"""
Usage:
import common_z3 as CM_Z3
"""

import ctypes
from .z3 import *


def vset(seq, idfun=None, as_list=True):
    # This functions preserves the order of arguments while removing duplicates.
    # This function is from https://code.google.com/p/common-python-vu/source/browse/vu_common.py
    # (Thanhu's personal code). It has been copied here to avoid a dependency on vu_common.py.
    """
    order preserving

    >>> vset([[11,2],1, [10,['9',1]],2, 1, [11,2],[3,3],[10,99],1,[10,['9',1]]],idfun=repr)
    [[11, 2], 1, [10, ['9', 1]], 2, [3, 3], [10, 99]]
    """

    def _uniq_normal(seq):
        d_ = {}
        for s in seq:
            if s not in d_:
                d_[s] = None
                yield s

    def _uniq_idfun(seq, idfun):
        d_ = {}
        for s in seq:
            h_ = idfun(s)
            if h_ not in d_:
                d_[h_] = None
                yield s

    if idfun is None:
        res = _uniq_normal(seq)
    else:
        res = _uniq_idfun(seq, idfun)

    return list(res) if as_list else res


def get_z3_version(as_str=False):
    major = ctypes.c_uint(0)
    minor = ctypes.c_uint(0)
    build = ctypes.c_uint(0)
    rev = ctypes.c_uint(0)
    Z3_get_version(major, minor, build, rev)
    rs = map(int, (major.value, minor.value, build.value, rev.value))
    if as_str:
        return "{}.{}.{}.{}".format(*rs)
    else:
        return rs


def ehash(v):
    """
    Returns a 'stronger' hash value than the default hash() method.
    The result from hash() is not enough to distinguish between 2
    z3 expressions in some cases.

    Note: the following doctests will fail with Python 2.x as the
    default formatting doesn't match that of 3.x.
    >>> x1 = Bool('x'); x2 = Bool('x'); x3 = Int('x')
    >>> print(x1.hash(), x2.hash(), x3.hash()) #BAD: all same hash values
    783810685 783810685 783810685
    >>> print(ehash(x1), ehash(x2), ehash(x3))
    x_783810685_1 x_783810685_1 x_783810685_2

    """
    if z3_debug():
        assert is_expr(v)

    return "{}_{}_{}".format(str(v), v.hash(), v.sort_kind())


"""
In Z3, variables are called *uninterpreted* consts and
variables are *interpreted* consts.
"""


def is_expr_var(v):
    """
    EXAMPLES:

    >>> is_expr_var(Int('7'))
    True
    >>> is_expr_var(IntVal('7'))
    False
    >>> is_expr_var(Bool('y'))
    True
    >>> is_expr_var(Int('x') + 7 == Int('y'))
    False
    >>> LOnOff, (On,Off) = EnumSort("LOnOff",['On','Off'])
    >>> Block,Reset,SafetyInjection=Consts("Block Reset SafetyInjection",LOnOff)
    >>> is_expr_var(LOnOff)
    False
    >>> is_expr_var(On)
    False
    >>> is_expr_var(Block)
    True
    >>> is_expr_var(SafetyInjection)
    True
    """

    return is_const(v) and v.decl().kind() == Z3_OP_UNINTERPRETED


def is_expr_val(v):
    """
    EXAMPLES:

    >>> is_expr_val(Int('7'))
    False
    >>> is_expr_val(IntVal('7'))
    True
    >>> is_expr_val(Bool('y'))
    False
    >>> is_expr_val(Int('x') + 7 == Int('y'))
    False
    >>> LOnOff, (On,Off) = EnumSort("LOnOff",['On','Off'])
    >>> Block,Reset,SafetyInjection=Consts("Block Reset SafetyInjection",LOnOff)
    >>> is_expr_val(LOnOff)
    False
    >>> is_expr_val(On)
    True
    >>> is_expr_val(Block)
    False
    >>> is_expr_val(SafetyInjection)
    False
    """
    return is_const(v) and v.decl().kind() != Z3_OP_UNINTERPRETED


def get_vars(f, rs=None):
    """
    >>> x,y = Ints('x y')
    >>> a,b = Bools('a b')
    >>> get_vars(Implies(And(x+y==0,x*2==10),Or(a,Implies(a,b==False))))
    [x, y, a, b]

    """
    if rs is None:
        rs = []

    if z3_debug():
        assert is_expr(f)

    if is_const(f):
        if is_expr_val(f):
            return rs
        else:  # variable
            return vset(rs + [f], str)

    else:
        for f_ in f.children():
            rs = get_vars(f_, rs)

        return vset(rs, str)


def mk_var(name, vsort):
    if vsort.kind() == Z3_INT_SORT:
        v = Int(name)
    elif vsort.kind() == Z3_REAL_SORT:
        v = Real(name)
    elif vsort.kind() == Z3_BOOL_SORT:
        v = Bool(name)
    elif vsort.kind() == Z3_DATATYPE_SORT:
        v = Const(name, vsort)
    else:
        raise TypeError("Cannot handle this sort (s: %sid: %d)" % (vsort, vsort.kind()))

    return v


def prove(claim, assume=None, verbose=0):
    """
    >>> r,m = prove(BoolVal(True),verbose=0); r,model_str(m,as_str=False)
    (True, None)

    #infinite counter example when proving contradiction
    >>> r,m = prove(BoolVal(False)); r,model_str(m,as_str=False)
    (False, [])

    >>> x,y,z=Bools('x y z')
    >>> r,m = prove(And(x,Not(x))); r,model_str(m,as_str=True)
    (False, '[]')

    >>> r,m = prove(True,assume=And(x,Not(x)),verbose=0)
    Traceback (most recent call last):
    ...
    AssertionError: Assumption is always False!

    >>> r,m = prove(Implies(x,x),assume=y,verbose=2); r,model_str(m,as_str=False)
    assume:
    y
    claim:
    Implies(x, x)
    to_prove:
    Implies(y, Implies(x, x))
    (True, None)

    >>> r,m = prove(And(x,True),assume=y,verbose=0); r,model_str(m,as_str=False)
    (False, [(x, False), (y, True)])

    >>> r,m = prove(And(x,y),assume=y,verbose=0)
    >>> print(r)
    False
    >>> print(model_str(m,as_str=True))
    x = False
    y = True

    >>> a,b = Ints('a b')
    >>> r,m = prove(a**b == b**a,assume=None,verbose=0)
    E: cannot solve !
    >>> r is None and m is None
    True

    """

    if z3_debug():
        assert not assume or is_expr(assume)

    to_prove = claim
    if assume:
        if z3_debug():
            is_proved, _ = prove(Not(assume))

            def _f():
                emsg = "Assumption is always False!"
                if verbose >= 2:
                    emsg = "{}\n{}".format(assume, emsg)
                return emsg

            assert is_proved is False, _f()

        to_prove = Implies(assume, to_prove)

    if verbose >= 2:
        print("assume: ")
        print(assume)
        print("claim: ")
        print(claim)
        print("to_prove: ")
        print(to_prove)

    f = Not(to_prove)

    models = get_models(f, k=1)
    if models is None:  # unknown
        print("E: cannot solve !")
        return None, None
    elif models is False:  # unsat
        return True, None
    else:  # sat
        if z3_debug():
            assert isinstance(models, list)

        if models:
            return False, models[0]  # the first counterexample
        else:
            return False, []  # infinite counterexample,models


def get_models(f, k):
    """
    Returns the first k models satisfying f.
    If f is not satisfiable, returns False.
    If f cannot be solved, returns None
    If f is satisfiable, returns the first k models
    Note that if f is a tautology, e.g.\\ True, then the result is []

    Based on http://stackoverflow.com/questions/11867611/z3py-checking-all-solutions-for-equation

    EXAMPLES:
    >>> x, y = Ints('x y')
    >>> len(get_models(And(0<=x,x <= 4),k=11))
    5
    >>> get_models(And(0<=x**y,x <= 1),k=2) is None
    True
    >>> get_models(And(0<=x,x <= -1),k=2)
    False
    >>> len(get_models(x+y==7,5))
    5
    >>> len(get_models(And(x<=5,x>=1),7))
    5
    >>> get_models(And(x<=0,x>=5),7)
    False

    >>> x = Bool('x')
    >>> get_models(And(x,Not(x)),k=1)
    False
    >>> get_models(Implies(x,x),k=1)
    []
    >>> get_models(BoolVal(True),k=1)
    []



    """

    if z3_debug():
        assert is_expr(f)
        assert k >= 1

    s = Solver()
    s.add(f)

    models = []
    i = 0
    while s.check() == sat and i < k:
        i = i + 1
        m = s.model()
        if not m:  # if m == []
            break
        models.append(m)

        # create new constraint to block the current model
        block = Not(And([v() == m[v] for v in m]))
        s.add(block)

    if s.check() == unknown:
        return None
    elif s.check() == unsat and i == 0:
        return False
    else:
        return models


def is_tautology(claim, verbose=0):
    """
    >>> is_tautology(Implies(Bool('x'),Bool('x')))
    True

    >>> is_tautology(Implies(Bool('x'),Bool('y')))
    False

    >>> is_tautology(BoolVal(True))
    True

    >>> is_tautology(BoolVal(False))
    False

    """
    return prove(claim=claim, assume=None, verbose=verbose)[0]


def is_contradiction(claim, verbose=0):
    """
    >>> x,y=Bools('x y')
    >>> is_contradiction(BoolVal(False))
    True

    >>> is_contradiction(BoolVal(True))
    False

    >>> is_contradiction(x)
    False

    >>> is_contradiction(Implies(x,y))
    False

    >>> is_contradiction(Implies(x,x))
    False

    >>> is_contradiction(And(x,Not(x)))
    True
    """

    return prove(claim=Not(claim), assume=None, verbose=verbose)[0]


def exact_one_model(f):
    """
    return True if f has exactly 1 model, False otherwise.

    EXAMPLES:

    >>> x, y = Ints('x y')
    >>> exact_one_model(And(0<=x**y,x <= 0))
    False

    >>> exact_one_model(And(0<=x,x <= 0))
    True

    >>> exact_one_model(And(0<=x,x <= 1))
    False

    >>> exact_one_model(And(0<=x,x <= -1))
    False
    """

    models = get_models(f, k=2)
    if isinstance(models, list):
        return len(models) == 1
    else:
        return False


def myBinOp(op, *L):
    """
    >>> myAnd(*[Bool('x'),Bool('y')])
    And(x, y)

    >>> myAnd(*[Bool('x'),None])
    x

    >>> myAnd(*[Bool('x')])
    x

    >>> myAnd(*[])

    >>> myAnd(Bool('x'),Bool('y'))
    And(x, y)

    >>> myAnd(*[Bool('x'),Bool('y')])
    And(x, y)

    >>> myAnd([Bool('x'),Bool('y')])
    And(x, y)

    >>> myAnd((Bool('x'),Bool('y')))
    And(x, y)

    >>> myAnd(*[Bool('x'),Bool('y'),True])
    Traceback (most recent call last):
    ...
    AssertionError
    """

    if z3_debug():
        assert op == Z3_OP_OR or op == Z3_OP_AND or op == Z3_OP_IMPLIES

    if len(L) == 1 and (isinstance(L[0], list) or isinstance(L[0], tuple)):
        L = L[0]

    if z3_debug():
        assert all(not isinstance(val, bool) for val in L)

    L = [val for val in L if is_expr(val)]
    if L:
        if len(L) == 1:
            return L[0]
        if op == Z3_OP_OR:
            return Or(L)
        if op == Z3_OP_AND:
            return And(L)
        return Implies(L[0], L[1])
    else:
        return None


def myAnd(*L):
    return myBinOp(Z3_OP_AND, *L)


def myOr(*L):
    return myBinOp(Z3_OP_OR, *L)


def myImplies(a, b):
    return myBinOp(Z3_OP_IMPLIES, [a, b])


def Iff(f):
    return And(Implies(f[0], f[1]), Implies(f[1], f[0]))


def model_str(m, as_str=True):
    """
    Returned a 'sorted' model (so that it's easier to see)
    The model is sorted by its key,
    e.g. if the model is y = 3 , x = 10, then the result is
    x = 10, y = 3

    EXAMPLES:
    see doctest examples from function prove()

    """
    if z3_debug():
        assert m is None or m == [] or isinstance(m, ModelRef)

    if m:
        vs = [(v, m[v]) for v in m]
        vs = sorted(vs, key=lambda a, _: str(a))
        if as_str:
            return "\n".join(["{} = {}".format(k, v) for (k, v) in vs])
        else:
            return vs
    else:
        return str(m) if as_str else m
