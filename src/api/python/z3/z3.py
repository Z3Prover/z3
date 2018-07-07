
############################################
# Copyright (c) 2012 Microsoft Corporation
#
# Z3 Python interface
#
# Author: Leonardo de Moura (leonardo)
############################################

"""Z3 is a high performance theorem prover developed at Microsoft Research. Z3 is used in many applications such as: software/hardware verification and testing, constraint solving, analysis of hybrid systems, security, biology (in silico analysis), and geometrical problems.

Several online tutorials for Z3Py are available at:
http://rise4fun.com/Z3Py/tutorial/guide

Please send feedback, comments and/or corrections on the Issue tracker for https://github.com/Z3prover/z3.git. Your comments are very valuable.

Small example:

>>> x = Int('x')
>>> y = Int('y')
>>> s = Solver()
>>> s.add(x > 0)
>>> s.add(x < 2)
>>> s.add(y == x + 1)
>>> s.check()
sat
>>> m = s.model()
>>> m[x]
1
>>> m[y]
2

Z3 exceptions:

>>> try:
...   x = BitVec('x', 32)
...   y = Bool('y')
...   # the expression x + y is type incorrect
...   n = x + y
... except Z3Exception as ex:
...   print("failed: %s" % ex)
failed: sort mismatch
"""
from . import z3core
from .z3core import *
from .z3types import *
from .z3consts import *
from .z3printer import *
from fractions import Fraction
import sys
import io
import math
import copy

if sys.version < '3':
    def _is_int(v):
        return isinstance(v, (int, long))    
else:
    def _is_int(v):
        return isinstance(v, int)

def enable_trace(msg):
    Z3_enable_trace(msg)

def disable_trace(msg):
    Z3_disable_trace(msg)

def get_version_string():
  major = ctypes.c_uint(0)
  minor = ctypes.c_uint(0)
  build = ctypes.c_uint(0)
  rev = ctypes.c_uint(0)
  Z3_get_version(major, minor, build, rev)
  return "%s.%s.%s" % (major.value, minor.value, build.value)

def get_version():
  major = ctypes.c_uint(0)
  minor = ctypes.c_uint(0)
  build = ctypes.c_uint(0)
  rev = ctypes.c_uint(0)
  Z3_get_version(major, minor, build, rev)
  return (major.value, minor.value, build.value, rev.value)

def get_full_version():
  return Z3_get_full_version()

# We use _z3_assert instead of the assert command because we want to
# produce nice error messages in Z3Py at rise4fun.com
def _z3_assert(cond, msg):
    if not cond:
        raise Z3Exception(msg)

def _z3_check_cint_overflow(n, name):
    _z3_assert(ctypes.c_int(n).value == n, name + " is too large")

def open_log(fname):
    """Log interaction to a file. This function must be invoked immediately after init(). """
    Z3_open_log(fname)

def append_log(s):
    """Append user-defined string to interaction log. """
    Z3_append_log(s)

def to_symbol(s, ctx=None):
    """Convert an integer or string into a Z3 symbol."""
    if _is_int(s):
        return Z3_mk_int_symbol(_get_ctx(ctx).ref(), s)
    else:
        return Z3_mk_string_symbol(_get_ctx(ctx).ref(), s)

def _symbol2py(ctx, s):
    """Convert a Z3 symbol back into a Python object. """
    if Z3_get_symbol_kind(ctx.ref(), s) == Z3_INT_SYMBOL:
        return "k!%s" % Z3_get_symbol_int(ctx.ref(), s)
    else:
        return Z3_get_symbol_string(ctx.ref(), s)

# Hack for having nary functions that can receive one argument that is the
# list of arguments.
# Use this when function takes a single list of arguments
def _get_args(args):
     try:
       if len(args) == 1 and (isinstance(args[0], tuple) or isinstance(args[0], list)):
            return args[0]
       elif len(args) == 1 and (isinstance(args[0], set) or isinstance(args[0], AstVector)):
            return [arg for arg in args[0]]
       else:
            return args
     except:  # len is not necessarily defined when args is not a sequence (use reflection?)
        return args

# Use this when function takes multiple arguments
def _get_args_ast_list(args):
    try:
        if isinstance(args, set) or isinstance(args, AstVector) or isinstance(args, tuple):
            return [arg for arg in args]
        else:
            return args
    except:
        return args

def _to_param_value(val):
    if isinstance(val, bool):
        if val == True:
            return "true"
        else:
            return "false"
    else:
        return str(val)

def z3_error_handler(c, e):
    # Do nothing error handler, just avoid exit(0)
    # The wrappers in z3core.py will raise a Z3Exception if an error is detected
    return

class Context:
    """A Context manages all other Z3 objects, global configuration options, etc.

    Z3Py uses a default global context. For most applications this is sufficient.
    An application may use multiple Z3 contexts. Objects created in one context
    cannot be used in another one. However, several objects may be "translated" from
    one context to another. It is not safe to access Z3 objects from multiple threads.
    The only exception is the method `interrupt()` that can be used to interrupt() a long
    computation.
    The initialization method receives global configuration options for the new context.
    """
    def __init__(self, *args, **kws):
        if __debug__:
            _z3_assert(len(args) % 2 == 0, "Argument list must have an even number of elements.")
        conf = Z3_mk_config()
        for key in kws:
            value = kws[key]
            Z3_set_param_value(conf, str(key).upper(), _to_param_value(value))
        prev = None
        for a in args:
            if prev is None:
                prev = a
            else:
                Z3_set_param_value(conf, str(prev), _to_param_value(a))
                prev = None
        self.ctx = Z3_mk_context_rc(conf)
        self.eh = Z3_set_error_handler(self.ctx, z3_error_handler)
        Z3_set_ast_print_mode(self.ctx, Z3_PRINT_SMTLIB2_COMPLIANT)
        Z3_del_config(conf)

    def __del__(self):
        Z3_del_context(self.ctx)        
        self.ctx = None
        self.eh = None

    def ref(self):
        """Return a reference to the actual C pointer to the Z3 context."""
        return self.ctx

    def interrupt(self):
        """Interrupt a solver performing a satisfiability test, a tactic processing a goal, or simplify functions.

        This method can be invoked from a thread different from the one executing the
        interruptible procedure.
        """
        Z3_interrupt(self.ref())


# Global Z3 context
_main_ctx = None
def main_ctx():
    """Return a reference to the global Z3 context.

    >>> x = Real('x')
    >>> x.ctx == main_ctx()
    True
    >>> c = Context()
    >>> c == main_ctx()
    False
    >>> x2 = Real('x', c)
    >>> x2.ctx == c
    True
    >>> eq(x, x2)
    False
    """
    global _main_ctx
    if _main_ctx is None:
        _main_ctx = Context()
    return _main_ctx

def _get_ctx(ctx):
    if ctx is None:
        return main_ctx()
    else:
        return ctx

def set_param(*args, **kws):
    """Set Z3 global (or module) parameters.

    >>> set_param(precision=10)
    """
    if __debug__:
        _z3_assert(len(args) % 2 == 0, "Argument list must have an even number of elements.")
    new_kws = {}
    for k in kws:
        v = kws[k]
        if not set_pp_option(k, v):
            new_kws[k] = v
    for key in new_kws:
        value = new_kws[key]
        Z3_global_param_set(str(key).upper(), _to_param_value(value))
    prev = None
    for a in args:
        if prev is None:
            prev = a
        else:
            Z3_global_param_set(str(prev), _to_param_value(a))
            prev = None

def reset_params():
    """Reset all global (or module) parameters.
    """
    Z3_global_param_reset_all()

def set_option(*args, **kws):
    """Alias for 'set_param' for backward compatibility.
    """
    return set_param(*args, **kws)

def get_param(name):
    """Return the value of a Z3 global (or module) parameter

    >>> get_param('nlsat.reorder')
    'true'
    """
    ptr = (ctypes.c_char_p * 1)()
    if Z3_global_param_get(str(name), ptr):
        r = z3core._to_pystr(ptr[0])
        return r
    raise Z3Exception("failed to retrieve value for '%s'" % name)

#########################################
#
# ASTs base class
#
#########################################

# Mark objects that use pretty printer
class Z3PPObject:
    """Superclass for all Z3 objects that have support for pretty printing."""
    def use_pp(self):
        return True

class AstRef(Z3PPObject):
    """AST are Direct Acyclic Graphs (DAGs) used to represent sorts, declarations and expressions."""
    def __init__(self, ast, ctx=None):
        self.ast  = ast
        self.ctx  = _get_ctx(ctx)
        Z3_inc_ref(self.ctx.ref(), self.as_ast())

    def __del__(self):
        if self.ctx.ref() is not None:
           Z3_dec_ref(self.ctx.ref(), self.as_ast())

    def __deepcopy__(self, memo={}):
        return _to_ast_ref(self.ast, self.ctx)

    def __str__(self):
        return obj_to_string(self)

    def __repr__(self):
        return obj_to_string(self)

    def __eq__(self, other):
        return self.eq(other)

    def __hash__(self):
        return self.hash()

    def __nonzero__(self):
        return self.__bool__()
        
    def __bool__(self):
        if is_true(self):
            return True
        elif is_false(self):
            return False
        elif is_eq(self) and self.num_args() == 2:
           return self.arg(0).eq(self.arg(1))
        else:
            raise Z3Exception("Symbolic expressions cannot be cast to concrete Boolean values.")

    def sexpr(self):
        """Return a string representing the AST node in s-expression notation.

        >>> x = Int('x')
        >>> ((x + 1)*x).sexpr()
        '(* (+ x 1) x)'
        """
        return Z3_ast_to_string(self.ctx_ref(), self.as_ast())

    def as_ast(self):
        """Return a pointer to the corresponding C Z3_ast object."""
        return self.ast

    def get_id(self):
        """Return unique identifier for object. It can be used for hash-tables and maps."""
        return Z3_get_ast_id(self.ctx_ref(), self.as_ast())

    def ctx_ref(self):
        """Return a reference to the C context where this AST node is stored."""
        return self.ctx.ref()

    def eq(self, other):
        """Return `True` if `self` and `other` are structurally identical.

        >>> x = Int('x')
        >>> n1 = x + 1
        >>> n2 = 1 + x
        >>> n1.eq(n2)
        False
        >>> n1 = simplify(n1)
        >>> n2 = simplify(n2)
        >>> n1.eq(n2)
        True
        """
        if __debug__:
            _z3_assert(is_ast(other), "Z3 AST expected")
        return Z3_is_eq_ast(self.ctx_ref(), self.as_ast(), other.as_ast())

    def translate(self, target):
        """Translate `self` to the context `target`. That is, return a copy of `self` in the context `target`.

        >>> c1 = Context()
        >>> c2 = Context()
        >>> x  = Int('x', c1)
        >>> y  = Int('y', c2)
        >>> # Nodes in different contexts can't be mixed.
        >>> # However, we can translate nodes from one context to another.
        >>> x.translate(c2) + y
        x + y
        """
        if __debug__:
            _z3_assert(isinstance(target, Context), "argument must be a Z3 context")
        return _to_ast_ref(Z3_translate(self.ctx.ref(), self.as_ast(), target.ref()), target)

    def __copy__(self):
        return self.translate(self.ctx)

    def hash(self):
        """Return a hashcode for the `self`.

        >>> n1 = simplify(Int('x') + 1)
        >>> n2 = simplify(2 + Int('x') - 1)
        >>> n1.hash() == n2.hash()
        True
        """
        return Z3_get_ast_hash(self.ctx_ref(), self.as_ast())

def is_ast(a):
    """Return `True` if `a` is an AST node.

    >>> is_ast(10)
    False
    >>> is_ast(IntVal(10))
    True
    >>> is_ast(Int('x'))
    True
    >>> is_ast(BoolSort())
    True
    >>> is_ast(Function('f', IntSort(), IntSort()))
    True
    >>> is_ast("x")
    False
    >>> is_ast(Solver())
    False
    """
    return isinstance(a, AstRef)

def eq(a, b):
    """Return `True` if `a` and `b` are structurally identical AST nodes.

    >>> x = Int('x')
    >>> y = Int('y')
    >>> eq(x, y)
    False
    >>> eq(x + 1, x + 1)
    True
    >>> eq(x + 1, 1 + x)
    False
    >>> eq(simplify(x + 1), simplify(1 + x))
    True
    """
    if __debug__:
        _z3_assert(is_ast(a) and is_ast(b), "Z3 ASTs expected")
    return a.eq(b)

def _ast_kind(ctx, a):
    if is_ast(a):
        a = a.as_ast()
    return Z3_get_ast_kind(ctx.ref(), a)

def _ctx_from_ast_arg_list(args, default_ctx=None):
    ctx = None
    for a in args:
        if is_ast(a) or is_probe(a):
            if ctx is None:
                ctx = a.ctx
            else:
                if __debug__:
                    _z3_assert(ctx == a.ctx, "Context mismatch")
    if ctx is None:
        ctx = default_ctx
    return ctx

def _ctx_from_ast_args(*args):
    return _ctx_from_ast_arg_list(args)

def _to_func_decl_array(args):
    sz = len(args)
    _args = (FuncDecl * sz)()
    for i in range(sz):
        _args[i] = args[i].as_func_decl()
    return _args, sz

def _to_ast_array(args):
    sz = len(args)
    _args = (Ast * sz)()
    for i in range(sz):
        _args[i] = args[i].as_ast()
    return _args, sz

def _to_ref_array(ref, args):
    sz = len(args)
    _args = (ref * sz)()
    for i in range(sz):
        _args[i] = args[i].as_ast()
    return _args, sz

def _to_ast_ref(a, ctx):
    k = _ast_kind(ctx, a)
    if k == Z3_SORT_AST:
        return _to_sort_ref(a, ctx)
    elif k == Z3_FUNC_DECL_AST:
        return _to_func_decl_ref(a, ctx)
    else:
        return _to_expr_ref(a, ctx)

#########################################
#
# Sorts
#
#########################################

def _sort_kind(ctx, s):
    return Z3_get_sort_kind(ctx.ref(), s)

class SortRef(AstRef):
    """A Sort is essentially a type. Every Z3 expression has a sort. A sort is an AST node."""
    def as_ast(self):
        return Z3_sort_to_ast(self.ctx_ref(), self.ast)

    def get_id(self):
        return Z3_get_ast_id(self.ctx_ref(), self.as_ast())

    def kind(self):
        """Return the Z3 internal kind of a sort. This method can be used to test if `self` is one of the Z3 builtin sorts.

        >>> b = BoolSort()
        >>> b.kind() == Z3_BOOL_SORT
        True
        >>> b.kind() == Z3_INT_SORT
        False
        >>> A = ArraySort(IntSort(), IntSort())
        >>> A.kind() == Z3_ARRAY_SORT
        True
        >>> A.kind() == Z3_INT_SORT
        False
        """
        return _sort_kind(self.ctx, self.ast)

    def subsort(self, other):
        """Return `True` if `self` is a subsort of `other`.

        >>> IntSort().subsort(RealSort())
        True
        """
        return False

    def cast(self, val):
        """Try to cast `val` as an element of sort `self`.

        This method is used in Z3Py to convert Python objects such as integers,
        floats, longs and strings into Z3 expressions.

        >>> x = Int('x')
        >>> RealSort().cast(x)
        ToReal(x)
        """
        if __debug__:
            _z3_assert(is_expr(val), "Z3 expression expected")
            _z3_assert(self.eq(val.sort()), "Sort mismatch")
        return val

    def name(self):
        """Return the name (string) of sort `self`.

        >>> BoolSort().name()
        'Bool'
        >>> ArraySort(IntSort(), IntSort()).name()
        'Array'
        """
        return _symbol2py(self.ctx, Z3_get_sort_name(self.ctx_ref(), self.ast))

    def __eq__(self, other):
        """Return `True` if `self` and `other` are the same Z3 sort.

        >>> p = Bool('p')
        >>> p.sort() == BoolSort()
        True
        >>> p.sort() == IntSort()
        False
        """
        if other is None:
            return False
        return Z3_is_eq_sort(self.ctx_ref(), self.ast, other.ast)

    def __ne__(self, other):
        """Return `True` if `self` and `other` are not the same Z3 sort.

        >>> p = Bool('p')
        >>> p.sort() != BoolSort()
        False
        >>> p.sort() != IntSort()
        True
        """
        return not Z3_is_eq_sort(self.ctx_ref(), self.ast, other.ast)

    def __hash__(self):
        """ Hash code. """
        return AstRef.__hash__(self)

def is_sort(s):
    """Return `True` if `s` is a Z3 sort.

    >>> is_sort(IntSort())
    True
    >>> is_sort(Int('x'))
    False
    >>> is_expr(Int('x'))
    True
    """
    return isinstance(s, SortRef)

def _to_sort_ref(s, ctx):
    if __debug__:
        _z3_assert(isinstance(s, Sort), "Z3 Sort expected")
    k = _sort_kind(ctx, s)
    if k == Z3_BOOL_SORT:
        return BoolSortRef(s, ctx)
    elif k == Z3_INT_SORT or k == Z3_REAL_SORT:
        return ArithSortRef(s, ctx)
    elif k == Z3_BV_SORT:
        return BitVecSortRef(s, ctx)
    elif k == Z3_ARRAY_SORT:
        return ArraySortRef(s, ctx)
    elif k == Z3_DATATYPE_SORT:
        return DatatypeSortRef(s, ctx)
    elif k == Z3_FINITE_DOMAIN_SORT:
        return FiniteDomainSortRef(s, ctx)
    elif k == Z3_FLOATING_POINT_SORT:
        return FPSortRef(s, ctx)
    elif k == Z3_ROUNDING_MODE_SORT:
        return FPRMSortRef(s, ctx)
    return SortRef(s, ctx)

def _sort(ctx, a):
    return _to_sort_ref(Z3_get_sort(ctx.ref(), a), ctx)

def DeclareSort(name, ctx=None):
    """Create a new uninterpreted sort named `name`.

    If `ctx=None`, then the new sort is declared in the global Z3Py context.

    >>> A = DeclareSort('A')
    >>> a = Const('a', A)
    >>> b = Const('b', A)
    >>> a.sort() == A
    True
    >>> b.sort() == A
    True
    >>> a == b
    a == b
    """
    ctx = _get_ctx(ctx)
    return SortRef(Z3_mk_uninterpreted_sort(ctx.ref(), to_symbol(name, ctx)), ctx)

#########################################
#
# Function Declarations
#
#########################################

class FuncDeclRef(AstRef):
    """Function declaration. Every constant and function have an associated declaration.

    The declaration assigns a name, a sort (i.e., type), and for function
    the sort (i.e., type) of each of its arguments. Note that, in Z3,
    a constant is a function with 0 arguments.
    """
    def as_ast(self):
        return Z3_func_decl_to_ast(self.ctx_ref(), self.ast)

    def get_id(self):
        return Z3_get_ast_id(self.ctx_ref(), self.as_ast())

    def as_func_decl(self):
        return self.ast

    def name(self):
        """Return the name of the function declaration `self`.

        >>> f = Function('f', IntSort(), IntSort())
        >>> f.name()
        'f'
        >>> isinstance(f.name(), str)
        True
        """
        return _symbol2py(self.ctx, Z3_get_decl_name(self.ctx_ref(), self.ast))

    def arity(self):
        """Return the number of arguments of a function declaration. If `self` is a constant, then `self.arity()` is 0.

        >>> f = Function('f', IntSort(), RealSort(), BoolSort())
        >>> f.arity()
        2
        """
        return int(Z3_get_arity(self.ctx_ref(), self.ast))

    def domain(self, i):
        """Return the sort of the argument `i` of a function declaration. This method assumes that `0 <= i < self.arity()`.

        >>> f = Function('f', IntSort(), RealSort(), BoolSort())
        >>> f.domain(0)
        Int
        >>> f.domain(1)
        Real
        """
        if __debug__:
            _z3_assert(i < self.arity(), "Index out of bounds")
        return _to_sort_ref(Z3_get_domain(self.ctx_ref(), self.ast, i), self.ctx)

    def range(self):
        """Return the sort of the range of a function declaration. For constants, this is the sort of the constant.

        >>> f = Function('f', IntSort(), RealSort(), BoolSort())
        >>> f.range()
        Bool
        """
        return _to_sort_ref(Z3_get_range(self.ctx_ref(), self.ast), self.ctx)

    def kind(self):
        """Return the internal kind of a function declaration. It can be used to identify Z3 built-in functions such as addition, multiplication, etc.

        >>> x = Int('x')
        >>> d = (x + 1).decl()
        >>> d.kind() == Z3_OP_ADD
        True
        >>> d.kind() == Z3_OP_MUL
        False
        """
        return Z3_get_decl_kind(self.ctx_ref(), self.ast)

    def params(self):
        ctx = self.ctx
        n = Z3_get_decl_num_parameters(self.ctx_ref(), self.ast)
        result = [ None for i in range(n) ]
        for i in range(n):
            k = Z3_get_decl_parameter_kind(self.ctx_ref(), self.ast, i)
            if k == Z3_PARAMETER_INT:
               result[i] = Z3_get_decl_int_parameter(self.ctx_ref(), self.ast, i)
            elif k == Z3_PARAMETER_DOUBLE:
               result[i] = Z3_get_decl_double_parameter(self.ctx_ref(), self.ast, i)               
            elif k == Z3_PARAMETER_RATIONAL:
               result[i] = Z3_get_decl_rational_parameter(self.ctx_ref(), self.ast, i)               
            elif k == Z3_PARAMETER_SYMBOL:
               result[i] = Z3_get_decl_symbol_parameter(self.ctx_ref(), self.ast, i)
            elif k == Z3_PARAMETER_SORT:
               result[i] = SortRef(Z3_get_decl_sort_parameter(self.ctx_ref(), self.ast, i), ctx)
            elif k == Z3_PARAMETER_AST:
               result[i] = ExprRef(Z3_get_decl_ast_parameter(self.ctx_ref(), self.ast, i), ctx)
            elif k == Z3_PARAMETER_FUNC_DECL:
               result[i] = FuncDeclRef(Z3_get_decl_func_decl_parameter(self.ctx_ref(), self.ast, i), ctx)
            else:
               assert(False)
        return result

    def __call__(self, *args):
        """Create a Z3 application expression using the function `self`, and the given arguments.

        The arguments must be Z3 expressions. This method assumes that
        the sorts of the elements in `args` match the sorts of the
        domain. Limited coercion is supported.  For example, if
        args[0] is a Python integer, and the function expects a Z3
        integer, then the argument is automatically converted into a
        Z3 integer.

        >>> f = Function('f', IntSort(), RealSort(), BoolSort())
        >>> x = Int('x')
        >>> y = Real('y')
        >>> f(x, y)
        f(x, y)
        >>> f(x, x)
        f(x, ToReal(x))
        """
        args = _get_args(args)
        num = len(args)
        if __debug__:
            _z3_assert(num == self.arity(), "Incorrect number of arguments to %s" % self)
        _args = (Ast * num)()
        saved = []
        for i in range(num):
            # self.domain(i).cast(args[i]) may create a new Z3 expression,
            # then we must save in 'saved' to prevent it from being garbage collected.
            tmp      = self.domain(i).cast(args[i])
            saved.append(tmp)
            _args[i] = tmp.as_ast()
        return _to_expr_ref(Z3_mk_app(self.ctx_ref(), self.ast, len(args), _args), self.ctx)

def is_func_decl(a):
    """Return `True` if `a` is a Z3 function declaration.

    >>> f = Function('f', IntSort(), IntSort())
    >>> is_func_decl(f)
    True
    >>> x = Real('x')
    >>> is_func_decl(x)
    False
    """
    return isinstance(a, FuncDeclRef)

def Function(name, *sig):
    """Create a new Z3 uninterpreted function with the given sorts.

    >>> f = Function('f', IntSort(), IntSort())
    >>> f(f(0))
    f(f(0))
    """
    sig = _get_args(sig)
    if __debug__:
        _z3_assert(len(sig) > 0, "At least two arguments expected")
    arity = len(sig) - 1
    rng   = sig[arity]
    if __debug__:
        _z3_assert(is_sort(rng), "Z3 sort expected")
    dom   = (Sort * arity)()
    for i in range(arity):
        if __debug__:
            _z3_assert(is_sort(sig[i]), "Z3 sort expected")
        dom[i] = sig[i].ast
    ctx = rng.ctx
    return FuncDeclRef(Z3_mk_func_decl(ctx.ref(), to_symbol(name, ctx), arity, dom, rng.ast), ctx)

def _to_func_decl_ref(a, ctx):
    return FuncDeclRef(a, ctx)

#########################################
#
# Expressions
#
#########################################

class ExprRef(AstRef):
    """Constraints, formulas and terms are expressions in Z3.

    Expressions are ASTs. Every expression has a sort.
    There are three main kinds of expressions:
    function applications, quantifiers and bounded variables.
    A constant is a function application with 0 arguments.
    For quantifier free problems, all expressions are
    function applications.
    """
    def as_ast(self):
        return self.ast

    def get_id(self):
        return Z3_get_ast_id(self.ctx_ref(), self.as_ast())

    def sort(self):
        """Return the sort of expression `self`.

        >>> x = Int('x')
        >>> (x + 1).sort()
        Int
        >>> y = Real('y')
        >>> (x + y).sort()
        Real
        """
        return _sort(self.ctx, self.as_ast())

    def sort_kind(self):
        """Shorthand for `self.sort().kind()`.

        >>> a = Array('a', IntSort(), IntSort())
        >>> a.sort_kind() == Z3_ARRAY_SORT
        True
        >>> a.sort_kind() == Z3_INT_SORT
        False
        """
        return self.sort().kind()

    def __eq__(self, other):
        """Return a Z3 expression that represents the constraint `self == other`.

        If `other` is `None`, then this method simply returns `False`.

        >>> a = Int('a')
        >>> b = Int('b')
        >>> a == b
        a == b
        >>> a is None
        False
        """
        if other is None:
            return False
        a, b = _coerce_exprs(self, other)
        return BoolRef(Z3_mk_eq(self.ctx_ref(), a.as_ast(), b.as_ast()), self.ctx)

    def __hash__(self):
        """ Hash code. """
        return AstRef.__hash__(self)

    def __ne__(self, other):
        """Return a Z3 expression that represents the constraint `self != other`.

        If `other` is `None`, then this method simply returns `True`.

        >>> a = Int('a')
        >>> b = Int('b')
        >>> a != b
        a != b
        >>> a is not None
        True
        """
        if other is None:
            return True
        a, b = _coerce_exprs(self, other)
        _args, sz = _to_ast_array((a, b))
        return BoolRef(Z3_mk_distinct(self.ctx_ref(), 2, _args), self.ctx)

    def params(self):
        return self.decl().params()

    def decl(self):
        """Return the Z3 function declaration associated with a Z3 application.

        >>> f = Function('f', IntSort(), IntSort())
        >>> a = Int('a')
        >>> t = f(a)
        >>> eq(t.decl(), f)
        True
        >>> (a + 1).decl()
        +
        """
        if __debug__:
            _z3_assert(is_app(self), "Z3 application expected")
        return FuncDeclRef(Z3_get_app_decl(self.ctx_ref(), self.as_ast()), self.ctx)

    def num_args(self):
        """Return the number of arguments of a Z3 application.

        >>> a = Int('a')
        >>> b = Int('b')
        >>> (a + b).num_args()
        2
        >>> f = Function('f', IntSort(), IntSort(), IntSort(), IntSort())
        >>> t = f(a, b, 0)
        >>> t.num_args()
        3
        """
        if __debug__:
            _z3_assert(is_app(self), "Z3 application expected")
        return int(Z3_get_app_num_args(self.ctx_ref(), self.as_ast()))

    def arg(self, idx):
        """Return argument `idx` of the application `self`.

        This method assumes that `self` is a function application with at least `idx+1` arguments.

        >>> a = Int('a')
        >>> b = Int('b')
        >>> f = Function('f', IntSort(), IntSort(), IntSort(), IntSort())
        >>> t = f(a, b, 0)
        >>> t.arg(0)
        a
        >>> t.arg(1)
        b
        >>> t.arg(2)
        0
        """
        if __debug__:
            _z3_assert(is_app(self), "Z3 application expected")
            _z3_assert(idx < self.num_args(), "Invalid argument index")
        return _to_expr_ref(Z3_get_app_arg(self.ctx_ref(), self.as_ast(), idx), self.ctx)

    def children(self):
        """Return a list containing the children of the given expression

        >>> a = Int('a')
        >>> b = Int('b')
        >>> f = Function('f', IntSort(), IntSort(), IntSort(), IntSort())
        >>> t = f(a, b, 0)
        >>> t.children()
        [a, b, 0]
        """
        if is_app(self):
            return [self.arg(i) for i in range(self.num_args())]
        else:
            return []

def _to_expr_ref(a, ctx):
    if isinstance(a, Pattern):
        return PatternRef(a, ctx)
    ctx_ref = ctx.ref()
    k = Z3_get_ast_kind(ctx_ref, a)
    if k == Z3_QUANTIFIER_AST:
        return QuantifierRef(a, ctx)
    sk = Z3_get_sort_kind(ctx_ref, Z3_get_sort(ctx_ref, a))
    if sk == Z3_BOOL_SORT:
        return BoolRef(a, ctx)
    if sk == Z3_INT_SORT:
        if k == Z3_NUMERAL_AST:
            return IntNumRef(a, ctx)
        return ArithRef(a, ctx)
    if sk == Z3_REAL_SORT:
        if k == Z3_NUMERAL_AST:
            return RatNumRef(a, ctx)
        if _is_algebraic(ctx, a):
            return AlgebraicNumRef(a, ctx)
        return ArithRef(a, ctx)
    if sk == Z3_BV_SORT:
        if k == Z3_NUMERAL_AST:
            return BitVecNumRef(a, ctx)
        else:
            return BitVecRef(a, ctx)
    if sk == Z3_ARRAY_SORT:
        return ArrayRef(a, ctx)
    if sk == Z3_DATATYPE_SORT:
        return DatatypeRef(a, ctx)
    if sk == Z3_FLOATING_POINT_SORT:
        if k == Z3_APP_AST and _is_numeral(ctx, a):
            return FPNumRef(a, ctx)
        else:
            return FPRef(a, ctx)
    if sk == Z3_FINITE_DOMAIN_SORT:
        if k == Z3_NUMERAL_AST:
            return FiniteDomainNumRef(a, ctx)
        else:
            return FiniteDomainRef(a, ctx)
    if sk == Z3_ROUNDING_MODE_SORT:
        return FPRMRef(a, ctx)
    if sk == Z3_SEQ_SORT:
        return SeqRef(a, ctx)
    if sk == Z3_RE_SORT:
        return ReRef(a, ctx)
    return ExprRef(a, ctx)

def _coerce_expr_merge(s, a):
    if is_expr(a):
        s1 = a.sort()
        if s is None:
            return s1
        if s1.eq(s):
            return s
        elif s.subsort(s1):
            return s1
        elif s1.subsort(s):
            return s
        else:
            if __debug__:
                _z3_assert(s1.ctx == s.ctx, "context mismatch")
                _z3_assert(False, "sort mismatch")
    else:
        return s

def _coerce_exprs(a, b, ctx=None):
    if not is_expr(a) and not is_expr(b):
        a = _py2expr(a, ctx)
        b = _py2expr(b, ctx)
    s = None
    s = _coerce_expr_merge(s, a)
    s = _coerce_expr_merge(s, b)
    a = s.cast(a)
    b = s.cast(b)
    return (a, b)


def _reduce(f, l, a):
    r = a
    for e in l:
        r = f(r, e)
    return r

def _coerce_expr_list(alist, ctx=None):
    has_expr = False
    for a in alist:
        if is_expr(a):
            has_expr = True
            break
    if not has_expr:
        alist = [ _py2expr(a, ctx) for a in alist ]
    s = _reduce(_coerce_expr_merge, alist, None)
    return [ s.cast(a) for a in alist ]

def is_expr(a):
    """Return `True` if `a` is a Z3 expression.

    >>> a = Int('a')
    >>> is_expr(a)
    True
    >>> is_expr(a + 1)
    True
    >>> is_expr(IntSort())
    False
    >>> is_expr(1)
    False
    >>> is_expr(IntVal(1))
    True
    >>> x = Int('x')
    >>> is_expr(ForAll(x, x >= 0))
    True
    >>> is_expr(FPVal(1.0))
    True
    """
    return isinstance(a, ExprRef)

def is_app(a):
    """Return `True` if `a` is a Z3 function application.

    Note that, constants are function applications with 0 arguments.

    >>> a = Int('a')
    >>> is_app(a)
    True
    >>> is_app(a + 1)
    True
    >>> is_app(IntSort())
    False
    >>> is_app(1)
    False
    >>> is_app(IntVal(1))
    True
    >>> x = Int('x')
    >>> is_app(ForAll(x, x >= 0))
    False
    """
    if not isinstance(a, ExprRef):
        return False
    k = _ast_kind(a.ctx, a)
    return k == Z3_NUMERAL_AST or k == Z3_APP_AST

def is_const(a):
    """Return `True` if `a` is Z3 constant/variable expression.

    >>> a = Int('a')
    >>> is_const(a)
    True
    >>> is_const(a + 1)
    False
    >>> is_const(1)
    False
    >>> is_const(IntVal(1))
    True
    >>> x = Int('x')
    >>> is_const(ForAll(x, x >= 0))
    False
    """
    return is_app(a) and a.num_args() == 0

def is_var(a):
    """Return `True` if `a` is variable.

    Z3 uses de-Bruijn indices for representing bound variables in
    quantifiers.

    >>> x = Int('x')
    >>> is_var(x)
    False
    >>> is_const(x)
    True
    >>> f = Function('f', IntSort(), IntSort())
    >>> # Z3 replaces x with bound variables when ForAll is executed.
    >>> q = ForAll(x, f(x) == x)
    >>> b = q.body()
    >>> b
    f(Var(0)) == Var(0)
    >>> b.arg(1)
    Var(0)
    >>> is_var(b.arg(1))
    True
    """
    return is_expr(a) and _ast_kind(a.ctx, a) == Z3_VAR_AST

def get_var_index(a):
    """Return the de-Bruijn index of the Z3 bounded variable `a`.

    >>> x = Int('x')
    >>> y = Int('y')
    >>> is_var(x)
    False
    >>> is_const(x)
    True
    >>> f = Function('f', IntSort(), IntSort(), IntSort())
    >>> # Z3 replaces x and y with bound variables when ForAll is executed.
    >>> q = ForAll([x, y], f(x, y) == x + y)
    >>> q.body()
    f(Var(1), Var(0)) == Var(1) + Var(0)
    >>> b = q.body()
    >>> b.arg(0)
    f(Var(1), Var(0))
    >>> v1 = b.arg(0).arg(0)
    >>> v2 = b.arg(0).arg(1)
    >>> v1
    Var(1)
    >>> v2
    Var(0)
    >>> get_var_index(v1)
    1
    >>> get_var_index(v2)
    0
    """
    if __debug__:
        _z3_assert(is_var(a), "Z3 bound variable expected")
    return int(Z3_get_index_value(a.ctx.ref(), a.as_ast()))

def is_app_of(a, k):
    """Return `True` if `a` is an application of the given kind `k`.

    >>> x = Int('x')
    >>> n = x + 1
    >>> is_app_of(n, Z3_OP_ADD)
    True
    >>> is_app_of(n, Z3_OP_MUL)
    False
    """
    return is_app(a) and a.decl().kind() == k

def If(a, b, c, ctx=None):
    """Create a Z3 if-then-else expression.

    >>> x = Int('x')
    >>> y = Int('y')
    >>> max = If(x > y, x, y)
    >>> max
    If(x > y, x, y)
    >>> simplify(max)
    If(x <= y, y, x)
    """
    if isinstance(a, Probe) or isinstance(b, Tactic) or isinstance(c, Tactic):
        return Cond(a, b, c, ctx)
    else:
        ctx = _get_ctx(_ctx_from_ast_arg_list([a, b, c], ctx))
        s = BoolSort(ctx)
        a = s.cast(a)
        b, c = _coerce_exprs(b, c, ctx)
        if __debug__:
            _z3_assert(a.ctx == b.ctx, "Context mismatch")
        return _to_expr_ref(Z3_mk_ite(ctx.ref(), a.as_ast(), b.as_ast(), c.as_ast()), ctx)

def Distinct(*args):
    """Create a Z3 distinct expression.

    >>> x = Int('x')
    >>> y = Int('y')
    >>> Distinct(x, y)
    x != y
    >>> z = Int('z')
    >>> Distinct(x, y, z)
    Distinct(x, y, z)
    >>> simplify(Distinct(x, y, z))
    Distinct(x, y, z)
    >>> simplify(Distinct(x, y, z), blast_distinct=True)
    And(Not(x == y), Not(x == z), Not(y == z))
    """
    args  = _get_args(args)
    ctx   = _ctx_from_ast_arg_list(args)
    if __debug__:
        _z3_assert(ctx is not None, "At least one of the arguments must be a Z3 expression")
    args  = _coerce_expr_list(args, ctx)
    _args, sz = _to_ast_array(args)
    return BoolRef(Z3_mk_distinct(ctx.ref(), sz, _args), ctx)

def _mk_bin(f, a, b):
    args = (Ast * 2)()
    if __debug__:
        _z3_assert(a.ctx == b.ctx, "Context mismatch")
    args[0] = a.as_ast()
    args[1] = b.as_ast()
    return f(a.ctx.ref(), 2, args)

def Const(name, sort):
    """Create a constant of the given sort.

    >>> Const('x', IntSort())
    x
    """
    if __debug__:
        _z3_assert(isinstance(sort, SortRef), "Z3 sort expected")
    ctx = sort.ctx
    return _to_expr_ref(Z3_mk_const(ctx.ref(), to_symbol(name, ctx), sort.ast), ctx)

def Consts(names, sort):
    """Create a several constants of the given sort.

    `names` is a string containing the names of all constants to be created.
    Blank spaces separate the names of different constants.

    >>> x, y, z = Consts('x y z', IntSort())
    >>> x + y + z
    x + y + z
    """
    if isinstance(names, str):
        names = names.split(" ")
    return [Const(name, sort) for name in names]

def Var(idx, s):
    """Create a Z3 free variable. Free variables are used to create quantified formulas.

    >>> Var(0, IntSort())
    Var(0)
    >>> eq(Var(0, IntSort()), Var(0, BoolSort()))
    False
    """
    if __debug__:
        _z3_assert(is_sort(s), "Z3 sort expected")
    return _to_expr_ref(Z3_mk_bound(s.ctx_ref(), idx, s.ast), s.ctx)

def RealVar(idx, ctx=None):
    """
    Create a real free variable. Free variables are used to create quantified formulas.
    They are also used to create polynomials.

    >>> RealVar(0)
    Var(0)
    """
    return Var(idx, RealSort(ctx))

def RealVarVector(n, ctx=None):
    """
    Create a list of Real free variables.
    The variables have ids: 0, 1, ..., n-1

    >>> x0, x1, x2, x3 = RealVarVector(4)
    >>> x2
    Var(2)
    """
    return [ RealVar(i, ctx) for i in range(n) ]

#########################################
#
# Booleans
#
#########################################

class BoolSortRef(SortRef):
    """Boolean sort."""
    def cast(self, val):
        """Try to cast `val` as a Boolean.

        >>> x = BoolSort().cast(True)
        >>> x
        True
        >>> is_expr(x)
        True
        >>> is_expr(True)
        False
        >>> x.sort()
        Bool
        """
        if isinstance(val, bool):
            return BoolVal(val, self.ctx)
        if __debug__:
            if not is_expr(val):
               _z3_assert(is_expr(val), "True, False or Z3 Boolean expression expected. Received %s" % val)
            if not self.eq(val.sort()):
               _z3_assert(self.eq(val.sort()), "Value cannot be converted into a Z3 Boolean value")
        return val

    def subsort(self, other):
        return isinstance(other, ArithSortRef)

    def is_int(self):
        return True

    def is_bool(self):
        return True


class BoolRef(ExprRef):
    """All Boolean expressions are instances of this class."""
    def sort(self):
        return BoolSortRef(Z3_get_sort(self.ctx_ref(), self.as_ast()), self.ctx)

    def __rmul__(self, other):
        return self * other
    
    def __mul__(self, other):
        """Create the Z3 expression `self * other`.
        """
        if other == 1:
            return self
        if other == 0:
            return 0        
        return If(self, other, 0)


def is_bool(a):
    """Return `True` if `a` is a Z3 Boolean expression.

    >>> p = Bool('p')
    >>> is_bool(p)
    True
    >>> q = Bool('q')
    >>> is_bool(And(p, q))
    True
    >>> x = Real('x')
    >>> is_bool(x)
    False
    >>> is_bool(x == 0)
    True
    """
    return isinstance(a, BoolRef)

def is_true(a):
    """Return `True` if `a` is the Z3 true expression.

    >>> p = Bool('p')
    >>> is_true(p)
    False
    >>> is_true(simplify(p == p))
    True
    >>> x = Real('x')
    >>> is_true(x == 0)
    False
    >>> # True is a Python Boolean expression
    >>> is_true(True)
    False
    """
    return is_app_of(a, Z3_OP_TRUE)

def is_false(a):
    """Return `True` if `a` is the Z3 false expression.

    >>> p = Bool('p')
    >>> is_false(p)
    False
    >>> is_false(False)
    False
    >>> is_false(BoolVal(False))
    True
    """
    return is_app_of(a, Z3_OP_FALSE)

def is_and(a):
    """Return `True` if `a` is a Z3 and expression.

    >>> p, q = Bools('p q')
    >>> is_and(And(p, q))
    True
    >>> is_and(Or(p, q))
    False
    """
    return is_app_of(a, Z3_OP_AND)

def is_or(a):
    """Return `True` if `a` is a Z3 or expression.

    >>> p, q = Bools('p q')
    >>> is_or(Or(p, q))
    True
    >>> is_or(And(p, q))
    False
    """
    return is_app_of(a, Z3_OP_OR)

def is_implies(a):
    """Return `True` if `a` is a Z3 implication expression.

    >>> p, q = Bools('p q')
    >>> is_implies(Implies(p, q))
    True
    >>> is_implies(And(p, q))
    False
    """
    return is_app_of(a, Z3_OP_IMPLIES)

def is_not(a):
    """Return `True` if `a` is a Z3 not expression.

    >>> p = Bool('p')
    >>> is_not(p)
    False
    >>> is_not(Not(p))
    True
    """
    return is_app_of(a, Z3_OP_NOT)

def is_eq(a):
    """Return `True` if `a` is a Z3 equality expression.

    >>> x, y = Ints('x y')
    >>> is_eq(x == y)
    True
    """
    return is_app_of(a, Z3_OP_EQ)

def is_distinct(a):
    """Return `True` if `a` is a Z3 distinct expression.

    >>> x, y, z = Ints('x y z')
    >>> is_distinct(x == y)
    False
    >>> is_distinct(Distinct(x, y, z))
    True
    """
    return is_app_of(a, Z3_OP_DISTINCT)

def BoolSort(ctx=None):
    """Return the Boolean Z3 sort. If `ctx=None`, then the global context is used.

    >>> BoolSort()
    Bool
    >>> p = Const('p', BoolSort())
    >>> is_bool(p)
    True
    >>> r = Function('r', IntSort(), IntSort(), BoolSort())
    >>> r(0, 1)
    r(0, 1)
    >>> is_bool(r(0, 1))
    True
    """
    ctx = _get_ctx(ctx)
    return BoolSortRef(Z3_mk_bool_sort(ctx.ref()), ctx)

def BoolVal(val, ctx=None):
    """Return the Boolean value `True` or `False`. If `ctx=None`, then the global context is used.

    >>> BoolVal(True)
    True
    >>> is_true(BoolVal(True))
    True
    >>> is_true(True)
    False
    >>> is_false(BoolVal(False))
    True
    """
    ctx = _get_ctx(ctx)
    if val == False:
        return BoolRef(Z3_mk_false(ctx.ref()), ctx)
    else:
        return BoolRef(Z3_mk_true(ctx.ref()), ctx)

def Bool(name, ctx=None):
    """Return a Boolean constant named `name`. If `ctx=None`, then the global context is used.

    >>> p = Bool('p')
    >>> q = Bool('q')
    >>> And(p, q)
    And(p, q)
    """
    ctx = _get_ctx(ctx)
    return BoolRef(Z3_mk_const(ctx.ref(), to_symbol(name, ctx), BoolSort(ctx).ast), ctx)

def Bools(names, ctx=None):
    """Return a tuple of Boolean constants.

    `names` is a single string containing all names separated by blank spaces.
    If `ctx=None`, then the global context is used.

    >>> p, q, r = Bools('p q r')
    >>> And(p, Or(q, r))
    And(p, Or(q, r))
    """
    ctx = _get_ctx(ctx)
    if isinstance(names, str):
        names = names.split(" ")
    return [Bool(name, ctx) for name in names]

def BoolVector(prefix, sz, ctx=None):
    """Return a list of Boolean constants of size `sz`.

    The constants are named using the given prefix.
    If `ctx=None`, then the global context is used.

    >>> P = BoolVector('p', 3)
    >>> P
    [p__0, p__1, p__2]
    >>> And(P)
    And(p__0, p__1, p__2)
    """
    return [ Bool('%s__%s' % (prefix, i)) for i in range(sz) ]

def FreshBool(prefix='b', ctx=None):
    """Return a fresh Boolean constant in the given context using the given prefix.

    If `ctx=None`, then the global context is used.

    >>> b1 = FreshBool()
    >>> b2 = FreshBool()
    >>> eq(b1, b2)
    False
    """
    ctx = _get_ctx(ctx)
    return BoolRef(Z3_mk_fresh_const(ctx.ref(), prefix, BoolSort(ctx).ast), ctx)

def Implies(a, b, ctx=None):
    """Create a Z3 implies expression.

    >>> p, q = Bools('p q')
    >>> Implies(p, q)
    Implies(p, q)
    >>> simplify(Implies(p, q))
    Or(Not(p), q)
    """
    ctx = _get_ctx(_ctx_from_ast_arg_list([a, b], ctx))
    s = BoolSort(ctx)
    a = s.cast(a)
    b = s.cast(b)
    return BoolRef(Z3_mk_implies(ctx.ref(), a.as_ast(), b.as_ast()), ctx)

def Xor(a, b, ctx=None):
    """Create a Z3 Xor expression.

    >>> p, q = Bools('p q')
    >>> Xor(p, q)
    Xor(p, q)
    >>> simplify(Xor(p, q))
    Not(p) == q
    """
    ctx = _get_ctx(_ctx_from_ast_arg_list([a, b], ctx))
    s = BoolSort(ctx)
    a = s.cast(a)
    b = s.cast(b)
    return BoolRef(Z3_mk_xor(ctx.ref(), a.as_ast(), b.as_ast()), ctx)

def Not(a, ctx=None):
    """Create a Z3 not expression or probe.

    >>> p = Bool('p')
    >>> Not(Not(p))
    Not(Not(p))
    >>> simplify(Not(Not(p)))
    p
    """
    ctx = _get_ctx(_ctx_from_ast_arg_list([a], ctx))
    if is_probe(a):
        # Not is also used to build probes
        return Probe(Z3_probe_not(ctx.ref(), a.probe), ctx)
    else:
        s = BoolSort(ctx)
        a = s.cast(a)
        return BoolRef(Z3_mk_not(ctx.ref(), a.as_ast()), ctx)

def _has_probe(args):
    """Return `True` if one of the elements of the given collection is a Z3 probe."""
    for arg in args:
        if is_probe(arg):
            return True
    return False

def And(*args):
    """Create a Z3 and-expression or and-probe.

    >>> p, q, r = Bools('p q r')
    >>> And(p, q, r)
    And(p, q, r)
    >>> P = BoolVector('p', 5)
    >>> And(P)
    And(p__0, p__1, p__2, p__3, p__4)
    """
    last_arg = None
    if len(args) > 0:
        last_arg = args[len(args)-1]
    if isinstance(last_arg, Context):
        ctx = args[len(args)-1]
        args = args[:len(args)-1]
    elif len(args) == 1 and isinstance(args[0], AstVector):
        ctx = args[0].ctx
        args = [a for a in args[0]]
    else:
        ctx = main_ctx()
    args = _get_args(args)
    ctx_args  = _ctx_from_ast_arg_list(args, ctx)
    if __debug__:
        _z3_assert(ctx_args is None or ctx_args == ctx, "context mismatch")
        _z3_assert(ctx is not None, "At least one of the arguments must be a Z3 expression or probe")
    if _has_probe(args):
        return _probe_and(args, ctx)
    else:
        args  = _coerce_expr_list(args, ctx)
        _args, sz = _to_ast_array(args)
        return BoolRef(Z3_mk_and(ctx.ref(), sz, _args), ctx)

def Or(*args):
    """Create a Z3 or-expression or or-probe.

    >>> p, q, r = Bools('p q r')
    >>> Or(p, q, r)
    Or(p, q, r)
    >>> P = BoolVector('p', 5)
    >>> Or(P)
    Or(p__0, p__1, p__2, p__3, p__4)
    """
    last_arg = None
    if len(args) > 0:
        last_arg = args[len(args)-1]
    if isinstance(last_arg, Context):
        ctx = args[len(args)-1]
        args = args[:len(args)-1]
    else:
        ctx = main_ctx()
    args = _get_args(args)
    ctx_args  = _ctx_from_ast_arg_list(args, ctx)
    if __debug__:
        _z3_assert(ctx_args is None or ctx_args == ctx, "context mismatch")
        _z3_assert(ctx is not None, "At least one of the arguments must be a Z3 expression or probe")
    if _has_probe(args):
        return _probe_or(args, ctx)
    else:
        args  = _coerce_expr_list(args, ctx)
        _args, sz = _to_ast_array(args)
        return BoolRef(Z3_mk_or(ctx.ref(), sz, _args), ctx)

#########################################
#
# Patterns
#
#########################################

class PatternRef(ExprRef):
    """Patterns are hints for quantifier instantiation.

    See http://rise4fun.com/Z3Py/tutorial/advanced for more details.
    """
    def as_ast(self):
        return Z3_pattern_to_ast(self.ctx_ref(), self.ast)

    def get_id(self):
        return Z3_get_ast_id(self.ctx_ref(), self.as_ast())

def is_pattern(a):
    """Return `True` if `a` is a Z3 pattern (hint for quantifier instantiation.

    See http://rise4fun.com/Z3Py/tutorial/advanced for more details.

    >>> f = Function('f', IntSort(), IntSort())
    >>> x = Int('x')
    >>> q = ForAll(x, f(x) == 0, patterns = [ f(x) ])
    >>> q
    ForAll(x, f(x) == 0)
    >>> q.num_patterns()
    1
    >>> is_pattern(q.pattern(0))
    True
    >>> q.pattern(0)
    f(Var(0))
    """
    return isinstance(a, PatternRef)

def MultiPattern(*args):
    """Create a Z3 multi-pattern using the given expressions `*args`

    See http://rise4fun.com/Z3Py/tutorial/advanced for more details.

    >>> f = Function('f', IntSort(), IntSort())
    >>> g = Function('g', IntSort(), IntSort())
    >>> x = Int('x')
    >>> q = ForAll(x, f(x) != g(x), patterns = [ MultiPattern(f(x), g(x)) ])
    >>> q
    ForAll(x, f(x) != g(x))
    >>> q.num_patterns()
    1
    >>> is_pattern(q.pattern(0))
    True
    >>> q.pattern(0)
    MultiPattern(f(Var(0)), g(Var(0)))
    """
    if __debug__:
        _z3_assert(len(args) > 0, "At least one argument expected")
        _z3_assert(all([ is_expr(a) for a in args ]), "Z3 expressions expected")
    ctx = args[0].ctx
    args, sz = _to_ast_array(args)
    return PatternRef(Z3_mk_pattern(ctx.ref(), sz, args), ctx)

def _to_pattern(arg):
    if is_pattern(arg):
        return arg
    else:
        return MultiPattern(arg)

#########################################
#
# Quantifiers
#
#########################################

class QuantifierRef(BoolRef):
    """Universally and Existentially quantified formulas."""

    def as_ast(self):
        return self.ast

    def get_id(self):
        return Z3_get_ast_id(self.ctx_ref(), self.as_ast())

    def sort(self):
        """Return the Boolean sort."""
        return BoolSort(self.ctx)

    def is_forall(self):
        """Return `True` if `self` is a universal quantifier.

        >>> f = Function('f', IntSort(), IntSort())
        >>> x = Int('x')
        >>> q = ForAll(x, f(x) == 0)
        >>> q.is_forall()
        True
        >>> q = Exists(x, f(x) != 0)
        >>> q.is_forall()
        False
        """
        return Z3_is_quantifier_forall(self.ctx_ref(), self.ast)

    def is_exists(self):
        """Return `True` if `self` is an existential quantifier.

        >>> f = Function('f', IntSort(), IntSort())
        >>> x = Int('x')
        >>> q = ForAll(x, f(x) == 0)
        >>> q.is_exists()
        False
        >>> q = Exists(x, f(x) != 0)
        >>> q.is_exists()
        True
        """
        return Z3_is_quantifier_exists(self.ctx_ref(), self.ast)

    def is_lambda(self):
        """Return `True` if `self` is a lambda expression.

        >>> f = Function('f', IntSort(), IntSort())
        >>> x = Int('x')
        >>> q = Lambda(x, f(x))
        >>> q.is_lambda()
        True
        >>> q = Exists(x, f(x) != 0)
        >>> q.is_lambda()
        False
        """
        return Z3_is_lambda(self.ctx_ref(), self.ast)

    def weight(self):
        """Return the weight annotation of `self`.

        >>> f = Function('f', IntSort(), IntSort())
        >>> x = Int('x')
        >>> q = ForAll(x, f(x) == 0)
        >>> q.weight()
        1
        >>> q = ForAll(x, f(x) == 0, weight=10)
        >>> q.weight()
        10
        """
        return int(Z3_get_quantifier_weight(self.ctx_ref(), self.ast))

    def num_patterns(self):
        """Return the number of patterns (i.e., quantifier instantiation hints) in `self`.

        >>> f = Function('f', IntSort(), IntSort())
        >>> g = Function('g', IntSort(), IntSort())
        >>> x = Int('x')
        >>> q = ForAll(x, f(x) != g(x), patterns = [ f(x), g(x) ])
        >>> q.num_patterns()
        2
        """
        return int(Z3_get_quantifier_num_patterns(self.ctx_ref(), self.ast))

    def pattern(self, idx):
        """Return a pattern (i.e., quantifier instantiation hints) in `self`.

        >>> f = Function('f', IntSort(), IntSort())
        >>> g = Function('g', IntSort(), IntSort())
        >>> x = Int('x')
        >>> q = ForAll(x, f(x) != g(x), patterns = [ f(x), g(x) ])
        >>> q.num_patterns()
        2
        >>> q.pattern(0)
        f(Var(0))
        >>> q.pattern(1)
        g(Var(0))
        """
        if __debug__:
            _z3_assert(idx < self.num_patterns(), "Invalid pattern idx")
        return PatternRef(Z3_get_quantifier_pattern_ast(self.ctx_ref(), self.ast, idx), self.ctx)

    def num_no_patterns(self):
        """Return the number of no-patterns."""
        return Z3_get_quantifier_num_no_patterns(self.ctx_ref(), self.ast)

    def no_pattern(self, idx):
        """Return a no-pattern."""
        if __debug__:
            _z3_assert(idx < self.num_no_patterns(), "Invalid no-pattern idx")
        return _to_expr_ref(Z3_get_quantifier_no_pattern_ast(self.ctx_ref(), self.ast, idx), self.ctx)

    def body(self):
        """Return the expression being quantified.

        >>> f = Function('f', IntSort(), IntSort())
        >>> x = Int('x')
        >>> q = ForAll(x, f(x) == 0)
        >>> q.body()
        f(Var(0)) == 0
        """
        return _to_expr_ref(Z3_get_quantifier_body(self.ctx_ref(), self.ast), self.ctx)

    def num_vars(self):
        """Return the number of variables bounded by this quantifier.

        >>> f = Function('f', IntSort(), IntSort(), IntSort())
        >>> x = Int('x')
        >>> y = Int('y')
        >>> q = ForAll([x, y], f(x, y) >= x)
        >>> q.num_vars()
        2
        """
        return int(Z3_get_quantifier_num_bound(self.ctx_ref(), self.ast))

    def var_name(self, idx):
        """Return a string representing a name used when displaying the quantifier.

        >>> f = Function('f', IntSort(), IntSort(), IntSort())
        >>> x = Int('x')
        >>> y = Int('y')
        >>> q = ForAll([x, y], f(x, y) >= x)
        >>> q.var_name(0)
        'x'
        >>> q.var_name(1)
        'y'
        """
        if __debug__:
            _z3_assert(idx < self.num_vars(), "Invalid variable idx")
        return _symbol2py(self.ctx, Z3_get_quantifier_bound_name(self.ctx_ref(), self.ast, idx))

    def var_sort(self, idx):
        """Return the sort of a bound variable.

        >>> f = Function('f', IntSort(), RealSort(), IntSort())
        >>> x = Int('x')
        >>> y = Real('y')
        >>> q = ForAll([x, y], f(x, y) >= x)
        >>> q.var_sort(0)
        Int
        >>> q.var_sort(1)
        Real
        """
        if __debug__:
            _z3_assert(idx < self.num_vars(), "Invalid variable idx")
        return _to_sort_ref(Z3_get_quantifier_bound_sort(self.ctx_ref(), self.ast, idx), self.ctx)

    def children(self):
        """Return a list containing a single element self.body()

        >>> f = Function('f', IntSort(), IntSort())
        >>> x = Int('x')
        >>> q = ForAll(x, f(x) == 0)
        >>> q.children()
        [f(Var(0)) == 0]
        """
        return [ self.body() ]

def is_quantifier(a):
    """Return `True` if `a` is a Z3 quantifier.

    >>> f = Function('f', IntSort(), IntSort())
    >>> x = Int('x')
    >>> q = ForAll(x, f(x) == 0)
    >>> is_quantifier(q)
    True
    >>> is_quantifier(f(x))
    False
    """
    return isinstance(a, QuantifierRef)

def _mk_quantifier(is_forall, vs, body, weight=1, qid="", skid="", patterns=[], no_patterns=[]):
    if __debug__:
        _z3_assert(is_bool(body) or is_app(vs) or (len(vs) > 0 and is_app(vs[0])), "Z3 expression expected")
        _z3_assert(is_const(vs) or (len(vs) > 0 and all([ is_const(v) for v in vs])), "Invalid bounded variable(s)")
        _z3_assert(all([is_pattern(a) or is_expr(a) for a in patterns]), "Z3 patterns expected")
        _z3_assert(all([is_expr(p) for p in no_patterns]), "no patterns are Z3 expressions")    
    if is_app(vs):
        ctx = vs.ctx
        vs = [vs]
    else:
        ctx = vs[0].ctx
    if not is_expr(body):
       body = BoolVal(body, ctx)
    num_vars = len(vs)
    if num_vars == 0:
        return body
    _vs = (Ast * num_vars)()
    for i in range(num_vars):
        ## TODO: Check if is constant
        _vs[i] = vs[i].as_ast()
    patterns = [ _to_pattern(p) for p in patterns ]
    num_pats = len(patterns)
    _pats = (Pattern * num_pats)()
    for i in range(num_pats):
        _pats[i] = patterns[i].ast
    _no_pats, num_no_pats = _to_ast_array(no_patterns)
    qid  = to_symbol(qid, ctx)
    skid = to_symbol(skid, ctx)
    return QuantifierRef(Z3_mk_quantifier_const_ex(ctx.ref(), is_forall, weight, qid, skid,
                                                   num_vars, _vs,
                                                   num_pats, _pats,
                                                   num_no_pats, _no_pats,
                                                   body.as_ast()), ctx)

def ForAll(vs, body, weight=1, qid="", skid="", patterns=[], no_patterns=[]):
    """Create a Z3 forall formula.

    The parameters `weight`, `qif`, `skid`, `patterns` and `no_patterns` are optional annotations.

    See http://rise4fun.com/Z3Py/tutorial/advanced for more details.

    >>> f = Function('f', IntSort(), IntSort(), IntSort())
    >>> x = Int('x')
    >>> y = Int('y')
    >>> ForAll([x, y], f(x, y) >= x)
    ForAll([x, y], f(x, y) >= x)
    >>> ForAll([x, y], f(x, y) >= x, patterns=[ f(x, y) ])
    ForAll([x, y], f(x, y) >= x)
    >>> ForAll([x, y], f(x, y) >= x, weight=10)
    ForAll([x, y], f(x, y) >= x)
    """
    return _mk_quantifier(True, vs, body, weight, qid, skid, patterns, no_patterns)

def Exists(vs, body, weight=1, qid="", skid="", patterns=[], no_patterns=[]):
    """Create a Z3 exists formula.

    The parameters `weight`, `qif`, `skid`, `patterns` and `no_patterns` are optional annotations.

    See http://rise4fun.com/Z3Py/tutorial/advanced for more details.

    >>> f = Function('f', IntSort(), IntSort(), IntSort())
    >>> x = Int('x')
    >>> y = Int('y')
    >>> q = Exists([x, y], f(x, y) >= x, skid="foo")
    >>> q
    Exists([x, y], f(x, y) >= x)
    >>> is_quantifier(q)
    True
    >>> r = Tactic('nnf')(q).as_expr()
    >>> is_quantifier(r)
    False
    """
    return _mk_quantifier(False, vs, body, weight, qid, skid, patterns, no_patterns)

def Lambda(vs, body):
    """Create a Z3 lambda expression.

    >>> f = Function('f', IntSort(), IntSort(), IntSort())
    >>> mem0 = Array('mem0', IntSort(), IntSort())
    >>> lo, hi, e, i = Ints('lo hi e i')
    >>> mem1 = Lambda([i], If(And(lo <= i, i <= hi), e, mem0[i]))
    >>> mem1
    Lambda(i, If(And(lo <= i, i <= hi), e, mem0[i]))
    """
    ctx = body.ctx
    if is_app(vs):
        vs = [vs]
    num_vars = len(vs)
    _vs = (Ast * num_vars)()
    for i in range(num_vars):
        ## TODO: Check if is constant
        _vs[i] = vs[i].as_ast()
    return QuantifierRef(Z3_mk_lambda_const(ctx.ref(), num_vars, _vs, body.as_ast()), ctx)

#########################################
#
# Arithmetic
#
#########################################

class ArithSortRef(SortRef):
    """Real and Integer sorts."""

    def is_real(self):
        """Return `True` if `self` is of the sort Real.

        >>> x = Real('x')
        >>> x.is_real()
        True
        >>> (x + 1).is_real()
        True
        >>> x = Int('x')
        >>> x.is_real()
        False
        """
        return self.kind() == Z3_REAL_SORT

    def is_int(self):
        """Return `True` if `self` is of the sort Integer.

        >>> x = Int('x')
        >>> x.is_int()
        True
        >>> (x + 1).is_int()
        True
        >>> x = Real('x')
        >>> x.is_int()
        False
        """
        return self.kind() == Z3_INT_SORT

    def subsort(self, other):
        """Return `True` if `self` is a subsort of `other`."""
        return self.is_int() and is_arith_sort(other) and other.is_real()

    def cast(self, val):
        """Try to cast `val` as an Integer or Real.

        >>> IntSort().cast(10)
        10
        >>> is_int(IntSort().cast(10))
        True
        >>> is_int(10)
        False
        >>> RealSort().cast(10)
        10
        >>> is_real(RealSort().cast(10))
        True
        """
        if is_expr(val):
            if __debug__:
                _z3_assert(self.ctx == val.ctx, "Context mismatch")
            val_s = val.sort()
            if self.eq(val_s):
                return val
            if val_s.is_int() and self.is_real():
                return ToReal(val)
            if val_s.is_bool() and self.is_int():
                return If(val, 1, 0)
            if val_s.is_bool() and self.is_real():
                return ToReal(If(val, 1, 0))
            if __debug__:
                _z3_assert(False, "Z3 Integer/Real expression expected" )
        else:
            if self.is_int():
                return IntVal(val, self.ctx)
            if self.is_real():
                return RealVal(val, self.ctx)
            if __debug__:
                _z3_assert(False, "int, long, float, string (numeral), or Z3 Integer/Real expression expected. Got %s" % self)

def is_arith_sort(s):
    """Return `True` if s is an arithmetical sort (type).

    >>> is_arith_sort(IntSort())
    True
    >>> is_arith_sort(RealSort())
    True
    >>> is_arith_sort(BoolSort())
    False
    >>> n = Int('x') + 1
    >>> is_arith_sort(n.sort())
    True
    """
    return isinstance(s, ArithSortRef)

class ArithRef(ExprRef):
    """Integer and Real expressions."""

    def sort(self):
        """Return the sort (type) of the arithmetical expression `self`.

        >>> Int('x').sort()
        Int
        >>> (Real('x') + 1).sort()
        Real
        """
        return ArithSortRef(Z3_get_sort(self.ctx_ref(), self.as_ast()), self.ctx)

    def is_int(self):
        """Return `True` if `self` is an integer expression.

        >>> x = Int('x')
        >>> x.is_int()
        True
        >>> (x + 1).is_int()
        True
        >>> y = Real('y')
        >>> (x + y).is_int()
        False
        """
        return self.sort().is_int()

    def is_real(self):
        """Return `True` if `self` is an real expression.

        >>> x = Real('x')
        >>> x.is_real()
        True
        >>> (x + 1).is_real()
        True
        """
        return self.sort().is_real()

    def __add__(self, other):
        """Create the Z3 expression `self + other`.

        >>> x = Int('x')
        >>> y = Int('y')
        >>> x + y
        x + y
        >>> (x + y).sort()
        Int
        """
        a, b = _coerce_exprs(self, other)
        return ArithRef(_mk_bin(Z3_mk_add, a, b), self.ctx)

    def __radd__(self, other):
        """Create the Z3 expression `other + self`.

        >>> x = Int('x')
        >>> 10 + x
        10 + x
        """
        a, b = _coerce_exprs(self, other)
        return ArithRef(_mk_bin(Z3_mk_add, b, a), self.ctx)

    def __mul__(self, other):
        """Create the Z3 expression `self * other`.

        >>> x = Real('x')
        >>> y = Real('y')
        >>> x * y
        x*y
        >>> (x * y).sort()
        Real
        """
        a, b = _coerce_exprs(self, other)
        return ArithRef(_mk_bin(Z3_mk_mul, a, b), self.ctx)

    def __rmul__(self, other):
        """Create the Z3 expression `other * self`.

        >>> x = Real('x')
        >>> 10 * x
        10*x
        """
        a, b = _coerce_exprs(self, other)
        return ArithRef(_mk_bin(Z3_mk_mul, b, a), self.ctx)

    def __sub__(self, other):
        """Create the Z3 expression `self - other`.

        >>> x = Int('x')
        >>> y = Int('y')
        >>> x - y
        x - y
        >>> (x - y).sort()
        Int
        """
        a, b = _coerce_exprs(self, other)
        return ArithRef(_mk_bin(Z3_mk_sub, a, b), self.ctx)

    def __rsub__(self, other):
        """Create the Z3 expression `other - self`.

        >>> x = Int('x')
        >>> 10 - x
        10 - x
        """
        a, b = _coerce_exprs(self, other)
        return ArithRef(_mk_bin(Z3_mk_sub, b, a), self.ctx)

    def __pow__(self, other):
        """Create the Z3 expression `self**other` (** is the power operator).

        >>> x = Real('x')
        >>> x**3
        x**3
        >>> (x**3).sort()
        Real
        >>> simplify(IntVal(2)**8)
        256
        """
        a, b = _coerce_exprs(self, other)
        return ArithRef(Z3_mk_power(self.ctx_ref(), a.as_ast(), b.as_ast()), self.ctx)

    def __rpow__(self, other):
        """Create the Z3 expression `other**self` (** is the power operator).

        >>> x = Real('x')
        >>> 2**x
        2**x
        >>> (2**x).sort()
        Real
        >>> simplify(2**IntVal(8))
        256
        """
        a, b = _coerce_exprs(self, other)
        return ArithRef(Z3_mk_power(self.ctx_ref(), b.as_ast(), a.as_ast()), self.ctx)

    def __div__(self, other):
        """Create the Z3 expression `other/self`.

        >>> x = Int('x')
        >>> y = Int('y')
        >>> x/y
        x/y
        >>> (x/y).sort()
        Int
        >>> (x/y).sexpr()
        '(div x y)'
        >>> x = Real('x')
        >>> y = Real('y')
        >>> x/y
        x/y
        >>> (x/y).sort()
        Real
        >>> (x/y).sexpr()
        '(/ x y)'
        """
        a, b = _coerce_exprs(self, other)
        return ArithRef(Z3_mk_div(self.ctx_ref(), a.as_ast(), b.as_ast()), self.ctx)

    def __truediv__(self, other):
        """Create the Z3 expression `other/self`."""
        return self.__div__(other)

    def __rdiv__(self, other):
        """Create the Z3 expression `other/self`.

        >>> x = Int('x')
        >>> 10/x
        10/x
        >>> (10/x).sexpr()
        '(div 10 x)'
        >>> x = Real('x')
        >>> 10/x
        10/x
        >>> (10/x).sexpr()
        '(/ 10.0 x)'
        """
        a, b = _coerce_exprs(self, other)
        return ArithRef(Z3_mk_div(self.ctx_ref(), b.as_ast(), a.as_ast()), self.ctx)

    def __rtruediv__(self, other):
        """Create the Z3 expression `other/self`."""
        return self.__rdiv__(other)

    def __mod__(self, other):
        """Create the Z3 expression `other%self`.

        >>> x = Int('x')
        >>> y = Int('y')
        >>> x % y
        x%y
        >>> simplify(IntVal(10) % IntVal(3))
        1
        """
        a, b = _coerce_exprs(self, other)
        if __debug__:
            _z3_assert(a.is_int(), "Z3 integer expression expected")
        return ArithRef(Z3_mk_mod(self.ctx_ref(), a.as_ast(), b.as_ast()), self.ctx)

    def __rmod__(self, other):
        """Create the Z3 expression `other%self`.

        >>> x = Int('x')
        >>> 10 % x
        10%x
        """
        a, b = _coerce_exprs(self, other)
        if __debug__:
            _z3_assert(a.is_int(), "Z3 integer expression expected")
        return ArithRef(Z3_mk_mod(self.ctx_ref(), b.as_ast(), a.as_ast()), self.ctx)

    def __neg__(self):
        """Return an expression representing `-self`.

        >>> x = Int('x')
        >>> -x
        -x
        >>> simplify(-(-x))
        x
        """
        return ArithRef(Z3_mk_unary_minus(self.ctx_ref(), self.as_ast()), self.ctx)

    def __pos__(self):
        """Return `self`.

        >>> x = Int('x')
        >>> +x
        x
        """
        return self

    def __le__(self, other):
        """Create the Z3 expression `other <= self`.

        >>> x, y = Ints('x y')
        >>> x <= y
        x <= y
        >>> y = Real('y')
        >>> x <= y
        ToReal(x) <= y
        """
        a, b = _coerce_exprs(self, other)
        return BoolRef(Z3_mk_le(self.ctx_ref(), a.as_ast(), b.as_ast()), self.ctx)

    def __lt__(self, other):
        """Create the Z3 expression `other < self`.

        >>> x, y = Ints('x y')
        >>> x < y
        x < y
        >>> y = Real('y')
        >>> x < y
        ToReal(x) < y
        """
        a, b = _coerce_exprs(self, other)
        return BoolRef(Z3_mk_lt(self.ctx_ref(), a.as_ast(), b.as_ast()), self.ctx)

    def __gt__(self, other):
        """Create the Z3 expression `other > self`.

        >>> x, y = Ints('x y')
        >>> x > y
        x > y
        >>> y = Real('y')
        >>> x > y
        ToReal(x) > y
        """
        a, b = _coerce_exprs(self, other)
        return BoolRef(Z3_mk_gt(self.ctx_ref(), a.as_ast(), b.as_ast()), self.ctx)

    def __ge__(self, other):
        """Create the Z3 expression `other >= self`.

        >>> x, y = Ints('x y')
        >>> x >= y
        x >= y
        >>> y = Real('y')
        >>> x >= y
        ToReal(x) >= y
        """
        a, b = _coerce_exprs(self, other)
        return BoolRef(Z3_mk_ge(self.ctx_ref(), a.as_ast(), b.as_ast()), self.ctx)

def is_arith(a):
    """Return `True` if `a` is an arithmetical expression.

    >>> x = Int('x')
    >>> is_arith(x)
    True
    >>> is_arith(x + 1)
    True
    >>> is_arith(1)
    False
    >>> is_arith(IntVal(1))
    True
    >>> y = Real('y')
    >>> is_arith(y)
    True
    >>> is_arith(y + 1)
    True
    """
    return isinstance(a, ArithRef)

def is_int(a):
    """Return `True` if `a` is an integer expression.

    >>> x = Int('x')
    >>> is_int(x + 1)
    True
    >>> is_int(1)
    False
    >>> is_int(IntVal(1))
    True
    >>> y = Real('y')
    >>> is_int(y)
    False
    >>> is_int(y + 1)
    False
    """
    return is_arith(a) and a.is_int()

def is_real(a):
    """Return `True` if `a` is a real expression.

    >>> x = Int('x')
    >>> is_real(x + 1)
    False
    >>> y = Real('y')
    >>> is_real(y)
    True
    >>> is_real(y + 1)
    True
    >>> is_real(1)
    False
    >>> is_real(RealVal(1))
    True
    """
    return is_arith(a) and a.is_real()

def _is_numeral(ctx, a):
    return Z3_is_numeral_ast(ctx.ref(), a)

def _is_algebraic(ctx, a):
    return Z3_is_algebraic_number(ctx.ref(), a)

def is_int_value(a):
    """Return `True` if `a` is an integer value of sort Int.

    >>> is_int_value(IntVal(1))
    True
    >>> is_int_value(1)
    False
    >>> is_int_value(Int('x'))
    False
    >>> n = Int('x') + 1
    >>> n
    x + 1
    >>> n.arg(1)
    1
    >>> is_int_value(n.arg(1))
    True
    >>> is_int_value(RealVal("1/3"))
    False
    >>> is_int_value(RealVal(1))
    False
    """
    return is_arith(a) and a.is_int() and _is_numeral(a.ctx, a.as_ast())

def is_rational_value(a):
    """Return `True` if `a` is rational value of sort Real.

    >>> is_rational_value(RealVal(1))
    True
    >>> is_rational_value(RealVal("3/5"))
    True
    >>> is_rational_value(IntVal(1))
    False
    >>> is_rational_value(1)
    False
    >>> n = Real('x') + 1
    >>> n.arg(1)
    1
    >>> is_rational_value(n.arg(1))
    True
    >>> is_rational_value(Real('x'))
    False
    """
    return is_arith(a) and a.is_real() and _is_numeral(a.ctx, a.as_ast())

def is_algebraic_value(a):
    """Return `True` if `a` is an algebraic value of sort Real.

    >>> is_algebraic_value(RealVal("3/5"))
    False
    >>> n = simplify(Sqrt(2))
    >>> n
    1.4142135623?
    >>> is_algebraic_value(n)
    True
    """
    return is_arith(a) and a.is_real() and _is_algebraic(a.ctx, a.as_ast())

def is_add(a):
    """Return `True` if `a` is an expression of the form b + c.

    >>> x, y = Ints('x y')
    >>> is_add(x + y)
    True
    >>> is_add(x - y)
    False
    """
    return is_app_of(a, Z3_OP_ADD)

def is_mul(a):
    """Return `True` if `a` is an expression of the form b * c.

    >>> x, y = Ints('x y')
    >>> is_mul(x * y)
    True
    >>> is_mul(x - y)
    False
    """
    return is_app_of(a, Z3_OP_MUL)

def is_sub(a):
    """Return `True` if `a` is an expression of the form b - c.

    >>> x, y = Ints('x y')
    >>> is_sub(x - y)
    True
    >>> is_sub(x + y)
    False
    """
    return is_app_of(a, Z3_OP_SUB)

def is_div(a):
    """Return `True` if `a` is an expression of the form b / c.

    >>> x, y = Reals('x y')
    >>> is_div(x / y)
    True
    >>> is_div(x + y)
    False
    >>> x, y = Ints('x y')
    >>> is_div(x / y)
    False
    >>> is_idiv(x / y)
    True
    """
    return is_app_of(a, Z3_OP_DIV)

def is_idiv(a):
    """Return `True` if `a` is an expression of the form b div c.

    >>> x, y = Ints('x y')
    >>> is_idiv(x / y)
    True
    >>> is_idiv(x + y)
    False
    """
    return is_app_of(a, Z3_OP_IDIV)

def is_mod(a):
    """Return `True` if `a` is an expression of the form b % c.

    >>> x, y = Ints('x y')
    >>> is_mod(x % y)
    True
    >>> is_mod(x + y)
    False
    """
    return is_app_of(a, Z3_OP_MOD)

def is_le(a):
    """Return `True` if `a` is an expression of the form b <= c.

    >>> x, y = Ints('x y')
    >>> is_le(x <= y)
    True
    >>> is_le(x < y)
    False
    """
    return is_app_of(a, Z3_OP_LE)

def is_lt(a):
    """Return `True` if `a` is an expression of the form b < c.

    >>> x, y = Ints('x y')
    >>> is_lt(x < y)
    True
    >>> is_lt(x == y)
    False
    """
    return is_app_of(a, Z3_OP_LT)

def is_ge(a):
    """Return `True` if `a` is an expression of the form b >= c.

    >>> x, y = Ints('x y')
    >>> is_ge(x >= y)
    True
    >>> is_ge(x == y)
    False
    """
    return is_app_of(a, Z3_OP_GE)

def is_gt(a):
    """Return `True` if `a` is an expression of the form b > c.

    >>> x, y = Ints('x y')
    >>> is_gt(x > y)
    True
    >>> is_gt(x == y)
    False
    """
    return is_app_of(a, Z3_OP_GT)

def is_is_int(a):
    """Return `True` if `a` is an expression of the form IsInt(b).

    >>> x = Real('x')
    >>> is_is_int(IsInt(x))
    True
    >>> is_is_int(x)
    False
    """
    return is_app_of(a, Z3_OP_IS_INT)

def is_to_real(a):
    """Return `True` if `a` is an expression of the form ToReal(b).

    >>> x = Int('x')
    >>> n = ToReal(x)
    >>> n
    ToReal(x)
    >>> is_to_real(n)
    True
    >>> is_to_real(x)
    False
    """
    return is_app_of(a, Z3_OP_TO_REAL)

def is_to_int(a):
    """Return `True` if `a` is an expression of the form ToInt(b).

    >>> x = Real('x')
    >>> n = ToInt(x)
    >>> n
    ToInt(x)
    >>> is_to_int(n)
    True
    >>> is_to_int(x)
    False
    """
    return is_app_of(a, Z3_OP_TO_INT)

class IntNumRef(ArithRef):
    """Integer values."""

    def as_long(self):
        """Return a Z3 integer numeral as a Python long (bignum) numeral.

        >>> v = IntVal(1)
        >>> v + 1
        1 + 1
        >>> v.as_long() + 1
        2
        """
        if __debug__:
            _z3_assert(self.is_int(), "Integer value expected")
        return int(self.as_string())

    def as_string(self):
        """Return a Z3 integer numeral as a Python string.
        >>> v = IntVal(100)
        >>> v.as_string()
        '100'
        """
        return Z3_get_numeral_string(self.ctx_ref(), self.as_ast())

class RatNumRef(ArithRef):
    """Rational values."""

    def numerator(self):
        """ Return the numerator of a Z3 rational numeral.

        >>> is_rational_value(RealVal("3/5"))
        True
        >>> n = RealVal("3/5")
        >>> n.numerator()
        3
        >>> is_rational_value(Q(3,5))
        True
        >>> Q(3,5).numerator()
        3
        """
        return IntNumRef(Z3_get_numerator(self.ctx_ref(), self.as_ast()), self.ctx)

    def denominator(self):
        """ Return the denominator of a Z3 rational numeral.

        >>> is_rational_value(Q(3,5))
        True
        >>> n = Q(3,5)
        >>> n.denominator()
        5
        """
        return IntNumRef(Z3_get_denominator(self.ctx_ref(), self.as_ast()), self.ctx)

    def numerator_as_long(self):
        """ Return the numerator as a Python long.

        >>> v = RealVal(10000000000)
        >>> v
        10000000000
        >>> v + 1
        10000000000 + 1
        >>> v.numerator_as_long() + 1 == 10000000001
        True
        """
        return self.numerator().as_long()

    def denominator_as_long(self):
        """ Return the denominator as a Python long.

        >>> v = RealVal("1/3")
        >>> v
        1/3
        >>> v.denominator_as_long()
        3
        """
        return self.denominator().as_long()

    def is_int(self):
        return False

    def is_real(self):
        return True

    def is_int_value(self):
        return self.denominator().is_int() and self.denominator_as_long() == 1

    def as_long(self):
        _z3_assert(self.is_int(), "Expected integer fraction")
        return self.numerator_as_long()

    def as_decimal(self, prec):
        """ Return a Z3 rational value as a string in decimal notation using at most `prec` decimal places.

        >>> v = RealVal("1/5")
        >>> v.as_decimal(3)
        '0.2'
        >>> v = RealVal("1/3")
        >>> v.as_decimal(3)
        '0.333?'
        """
        return Z3_get_numeral_decimal_string(self.ctx_ref(), self.as_ast(), prec)

    def as_string(self):
        """Return a Z3 rational numeral as a Python string.

        >>> v = Q(3,6)
        >>> v.as_string()
        '1/2'
        """
        return Z3_get_numeral_string(self.ctx_ref(), self.as_ast())

    def as_fraction(self):
        """Return a Z3 rational as a Python Fraction object.

        >>> v = RealVal("1/5")
        >>> v.as_fraction()
        Fraction(1, 5)
        """
        return Fraction(self.numerator_as_long(), self.denominator_as_long())

class AlgebraicNumRef(ArithRef):
    """Algebraic irrational values."""

    def approx(self, precision=10):
        """Return a Z3 rational number that approximates the algebraic number `self`.
        The result `r` is such that |r - self| <= 1/10^precision

        >>> x = simplify(Sqrt(2))
        >>> x.approx(20)
        6838717160008073720548335/4835703278458516698824704
        >>> x.approx(5)
        2965821/2097152
        """
        return RatNumRef(Z3_get_algebraic_number_upper(self.ctx_ref(), self.as_ast(), precision), self.ctx)
    def as_decimal(self, prec):
        """Return a string representation of the algebraic number `self` in decimal notation using `prec` decimal places

        >>> x = simplify(Sqrt(2))
        >>> x.as_decimal(10)
        '1.4142135623?'
        >>> x.as_decimal(20)
        '1.41421356237309504880?'
        """
        return Z3_get_numeral_decimal_string(self.ctx_ref(), self.as_ast(), prec)

def _py2expr(a, ctx=None):
    if isinstance(a, bool):
        return BoolVal(a, ctx)
    if _is_int(a):
        return IntVal(a, ctx)
    if isinstance(a, float):
        return RealVal(a, ctx)
    if is_expr(a):
        return a
    if __debug__:
        _z3_assert(False, "Python bool, int, long or float expected")

def IntSort(ctx=None):
    """Return the integer sort in the given context. If `ctx=None`, then the global context is used.

    >>> IntSort()
    Int
    >>> x = Const('x', IntSort())
    >>> is_int(x)
    True
    >>> x.sort() == IntSort()
    True
    >>> x.sort() == BoolSort()
    False
    """
    ctx = _get_ctx(ctx)
    return ArithSortRef(Z3_mk_int_sort(ctx.ref()), ctx)

def RealSort(ctx=None):
    """Return the real sort in the given context. If `ctx=None`, then the global context is used.

    >>> RealSort()
    Real
    >>> x = Const('x', RealSort())
    >>> is_real(x)
    True
    >>> is_int(x)
    False
    >>> x.sort() == RealSort()
    True
    """
    ctx = _get_ctx(ctx)
    return ArithSortRef(Z3_mk_real_sort(ctx.ref()), ctx)

def _to_int_str(val):
    if isinstance(val, float):
        return str(int(val))
    elif isinstance(val, bool):
        if val:
            return "1"
        else:
            return "0"
    elif _is_int(val):
        return str(val)
    elif isinstance(val, str):
        return val
    if __debug__:
        _z3_assert(False, "Python value cannot be used as a Z3 integer")

def IntVal(val, ctx=None):
    """Return a Z3 integer value. If `ctx=None`, then the global context is used.

    >>> IntVal(1)
    1
    >>> IntVal("100")
    100
    """
    ctx = _get_ctx(ctx)
    return IntNumRef(Z3_mk_numeral(ctx.ref(), _to_int_str(val), IntSort(ctx).ast), ctx)

def RealVal(val, ctx=None):
    """Return a Z3 real value.

    `val` may be a Python int, long, float or string representing a number in decimal or rational notation.
    If `ctx=None`, then the global context is used.

    >>> RealVal(1)
    1
    >>> RealVal(1).sort()
    Real
    >>> RealVal("3/5")
    3/5
    >>> RealVal("1.5")
    3/2
    """
    ctx = _get_ctx(ctx)
    return RatNumRef(Z3_mk_numeral(ctx.ref(), str(val), RealSort(ctx).ast), ctx)

def RatVal(a, b, ctx=None):
    """Return a Z3 rational a/b.

    If `ctx=None`, then the global context is used.

    >>> RatVal(3,5)
    3/5
    >>> RatVal(3,5).sort()
    Real
    """
    if __debug__:
        _z3_assert(_is_int(a) or isinstance(a, str), "First argument cannot be converted into an integer")
        _z3_assert(_is_int(b) or isinstance(b, str), "Second argument cannot be converted into an integer")
    return simplify(RealVal(a, ctx)/RealVal(b, ctx))

def Q(a, b, ctx=None):
    """Return a Z3 rational a/b.

    If `ctx=None`, then the global context is used.

    >>> Q(3,5)
    3/5
    >>> Q(3,5).sort()
    Real
    """
    return simplify(RatVal(a, b))

def Int(name, ctx=None):
    """Return an integer constant named `name`. If `ctx=None`, then the global context is used.

    >>> x = Int('x')
    >>> is_int(x)
    True
    >>> is_int(x + 1)
    True
    """
    ctx = _get_ctx(ctx)
    return ArithRef(Z3_mk_const(ctx.ref(), to_symbol(name, ctx), IntSort(ctx).ast), ctx)

def Ints(names, ctx=None):
    """Return a tuple of Integer constants.

    >>> x, y, z = Ints('x y z')
    >>> Sum(x, y, z)
    x + y + z
    """
    ctx = _get_ctx(ctx)
    if isinstance(names, str):
        names = names.split(" ")
    return [Int(name, ctx) for name in names]

def IntVector(prefix, sz, ctx=None):
    """Return a list of integer constants of size `sz`.

    >>> X = IntVector('x', 3)
    >>> X
    [x__0, x__1, x__2]
    >>> Sum(X)
    x__0 + x__1 + x__2
    """
    return [ Int('%s__%s' % (prefix, i)) for i in range(sz) ]

def FreshInt(prefix='x', ctx=None):
    """Return a fresh integer constant in the given context using the given prefix.

    >>> x = FreshInt()
    >>> y = FreshInt()
    >>> eq(x, y)
    False
    >>> x.sort()
    Int
    """
    ctx = _get_ctx(ctx)
    return ArithRef(Z3_mk_fresh_const(ctx.ref(), prefix, IntSort(ctx).ast), ctx)

def Real(name, ctx=None):
    """Return a real constant named `name`. If `ctx=None`, then the global context is used.

    >>> x = Real('x')
    >>> is_real(x)
    True
    >>> is_real(x + 1)
    True
    """
    ctx = _get_ctx(ctx)
    return ArithRef(Z3_mk_const(ctx.ref(), to_symbol(name, ctx), RealSort(ctx).ast), ctx)

def Reals(names, ctx=None):
    """Return a tuple of real constants.

    >>> x, y, z = Reals('x y z')
    >>> Sum(x, y, z)
    x + y + z
    >>> Sum(x, y, z).sort()
    Real
    """
    ctx = _get_ctx(ctx)
    if isinstance(names, str):
        names = names.split(" ")
    return [Real(name, ctx) for name in names]

def RealVector(prefix, sz, ctx=None):
    """Return a list of real constants of size `sz`.

    >>> X = RealVector('x', 3)
    >>> X
    [x__0, x__1, x__2]
    >>> Sum(X)
    x__0 + x__1 + x__2
    >>> Sum(X).sort()
    Real
    """
    return [ Real('%s__%s' % (prefix, i)) for i in range(sz) ]

def FreshReal(prefix='b', ctx=None):
    """Return a fresh real constant in the given context using the given prefix.

    >>> x = FreshReal()
    >>> y = FreshReal()
    >>> eq(x, y)
    False
    >>> x.sort()
    Real
    """
    ctx = _get_ctx(ctx)
    return ArithRef(Z3_mk_fresh_const(ctx.ref(), prefix, RealSort(ctx).ast), ctx)

def ToReal(a):
    """ Return the Z3 expression ToReal(a).

    >>> x = Int('x')
    >>> x.sort()
    Int
    >>> n = ToReal(x)
    >>> n
    ToReal(x)
    >>> n.sort()
    Real
    """
    if __debug__:
        _z3_assert(a.is_int(), "Z3 integer expression expected.")
    ctx = a.ctx
    return ArithRef(Z3_mk_int2real(ctx.ref(), a.as_ast()), ctx)

def ToInt(a):
    """ Return the Z3 expression ToInt(a).

    >>> x = Real('x')
    >>> x.sort()
    Real
    >>> n = ToInt(x)
    >>> n
    ToInt(x)
    >>> n.sort()
    Int
    """
    if __debug__:
        _z3_assert(a.is_real(), "Z3 real expression expected.")
    ctx = a.ctx
    return ArithRef(Z3_mk_real2int(ctx.ref(), a.as_ast()), ctx)

def IsInt(a):
    """ Return the Z3 predicate IsInt(a).

    >>> x = Real('x')
    >>> IsInt(x + "1/2")
    IsInt(x + 1/2)
    >>> solve(IsInt(x + "1/2"), x > 0, x < 1)
    [x = 1/2]
    >>> solve(IsInt(x + "1/2"), x > 0, x < 1, x != "1/2")
    no solution
    """
    if __debug__:
        _z3_assert(a.is_real(), "Z3 real expression expected.")
    ctx = a.ctx
    return BoolRef(Z3_mk_is_int(ctx.ref(), a.as_ast()), ctx)

def Sqrt(a, ctx=None):
    """ Return a Z3 expression which represents the square root of a.

    >>> x = Real('x')
    >>> Sqrt(x)
    x**(1/2)
    """
    if not is_expr(a):
        ctx = _get_ctx(ctx)
        a = RealVal(a, ctx)
    return a ** "1/2"

def Cbrt(a, ctx=None):
    """ Return a Z3 expression which represents the cubic root of a.

    >>> x = Real('x')
    >>> Cbrt(x)
    x**(1/3)
    """
    if not is_expr(a):
        ctx = _get_ctx(ctx)
        a = RealVal(a, ctx)
    return a ** "1/3"

#########################################
#
# Bit-Vectors
#
#########################################

class BitVecSortRef(SortRef):
    """Bit-vector sort."""

    def size(self):
        """Return the size (number of bits) of the bit-vector sort `self`.

        >>> b = BitVecSort(32)
        >>> b.size()
        32
        """
        return int(Z3_get_bv_sort_size(self.ctx_ref(), self.ast))

    def subsort(self, other):
        return is_bv_sort(other) and self.size() < other.size()

    def cast(self, val):
        """Try to cast `val` as a Bit-Vector.

        >>> b = BitVecSort(32)
        >>> b.cast(10)
        10
        >>> b.cast(10).sexpr()
        '#x0000000a'
        """
        if is_expr(val):
            if __debug__:
                _z3_assert(self.ctx == val.ctx, "Context mismatch")
            # Idea: use sign_extend if sort of val is a bitvector of smaller size
            return val
        else:
            return BitVecVal(val, self)

def is_bv_sort(s):
    """Return True if `s` is a Z3 bit-vector sort.

    >>> is_bv_sort(BitVecSort(32))
    True
    >>> is_bv_sort(IntSort())
    False
    """
    return isinstance(s, BitVecSortRef)

class BitVecRef(ExprRef):
    """Bit-vector expressions."""

    def sort(self):
        """Return the sort of the bit-vector expression `self`.

        >>> x = BitVec('x', 32)
        >>> x.sort()
        BitVec(32)
        >>> x.sort() == BitVecSort(32)
        True
        """
        return BitVecSortRef(Z3_get_sort(self.ctx_ref(), self.as_ast()), self.ctx)

    def size(self):
        """Return the number of bits of the bit-vector expression `self`.

        >>> x = BitVec('x', 32)
        >>> (x + 1).size()
        32
        >>> Concat(x, x).size()
        64
        """
        return self.sort().size()

    def __add__(self, other):
        """Create the Z3 expression `self + other`.

        >>> x = BitVec('x', 32)
        >>> y = BitVec('y', 32)
        >>> x + y
        x + y
        >>> (x + y).sort()
        BitVec(32)
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(Z3_mk_bvadd(self.ctx_ref(), a.as_ast(), b.as_ast()), self.ctx)

    def __radd__(self, other):
        """Create the Z3 expression `other + self`.

        >>> x = BitVec('x', 32)
        >>> 10 + x
        10 + x
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(Z3_mk_bvadd(self.ctx_ref(), b.as_ast(), a.as_ast()), self.ctx)

    def __mul__(self, other):
        """Create the Z3 expression `self * other`.

        >>> x = BitVec('x', 32)
        >>> y = BitVec('y', 32)
        >>> x * y
        x*y
        >>> (x * y).sort()
        BitVec(32)
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(Z3_mk_bvmul(self.ctx_ref(), a.as_ast(), b.as_ast()), self.ctx)

    def __rmul__(self, other):
        """Create the Z3 expression `other * self`.

        >>> x = BitVec('x', 32)
        >>> 10 * x
        10*x
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(Z3_mk_bvmul(self.ctx_ref(), b.as_ast(), a.as_ast()), self.ctx)

    def __sub__(self, other):
        """Create the Z3 expression `self - other`.

        >>> x = BitVec('x', 32)
        >>> y = BitVec('y', 32)
        >>> x - y
        x - y
        >>> (x - y).sort()
        BitVec(32)
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(Z3_mk_bvsub(self.ctx_ref(), a.as_ast(), b.as_ast()), self.ctx)

    def __rsub__(self, other):
        """Create the Z3 expression `other - self`.

        >>> x = BitVec('x', 32)
        >>> 10 - x
        10 - x
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(Z3_mk_bvsub(self.ctx_ref(), b.as_ast(), a.as_ast()), self.ctx)

    def __or__(self, other):
        """Create the Z3 expression bitwise-or `self | other`.

        >>> x = BitVec('x', 32)
        >>> y = BitVec('y', 32)
        >>> x | y
        x | y
        >>> (x | y).sort()
        BitVec(32)
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(Z3_mk_bvor(self.ctx_ref(), a.as_ast(), b.as_ast()), self.ctx)

    def __ror__(self, other):
        """Create the Z3 expression bitwise-or `other | self`.

        >>> x = BitVec('x', 32)
        >>> 10 | x
        10 | x
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(Z3_mk_bvor(self.ctx_ref(), b.as_ast(), a.as_ast()), self.ctx)

    def __and__(self, other):
        """Create the Z3 expression bitwise-and `self & other`.

        >>> x = BitVec('x', 32)
        >>> y = BitVec('y', 32)
        >>> x & y
        x & y
        >>> (x & y).sort()
        BitVec(32)
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(Z3_mk_bvand(self.ctx_ref(), a.as_ast(), b.as_ast()), self.ctx)

    def __rand__(self, other):
        """Create the Z3 expression bitwise-or `other & self`.

        >>> x = BitVec('x', 32)
        >>> 10 & x
        10 & x
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(Z3_mk_bvand(self.ctx_ref(), b.as_ast(), a.as_ast()), self.ctx)

    def __xor__(self, other):
        """Create the Z3 expression bitwise-xor `self ^ other`.

        >>> x = BitVec('x', 32)
        >>> y = BitVec('y', 32)
        >>> x ^ y
        x ^ y
        >>> (x ^ y).sort()
        BitVec(32)
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(Z3_mk_bvxor(self.ctx_ref(), a.as_ast(), b.as_ast()), self.ctx)

    def __rxor__(self, other):
        """Create the Z3 expression bitwise-xor `other ^ self`.

        >>> x = BitVec('x', 32)
        >>> 10 ^ x
        10 ^ x
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(Z3_mk_bvxor(self.ctx_ref(), b.as_ast(), a.as_ast()), self.ctx)

    def __pos__(self):
        """Return `self`.

        >>> x = BitVec('x', 32)
        >>> +x
        x
        """
        return self

    def __neg__(self):
        """Return an expression representing `-self`.

        >>> x = BitVec('x', 32)
        >>> -x
        -x
        >>> simplify(-(-x))
        x
        """
        return BitVecRef(Z3_mk_bvneg(self.ctx_ref(), self.as_ast()), self.ctx)

    def __invert__(self):
        """Create the Z3 expression bitwise-not `~self`.

        >>> x = BitVec('x', 32)
        >>> ~x
        ~x
        >>> simplify(~(~x))
        x
        """
        return BitVecRef(Z3_mk_bvnot(self.ctx_ref(), self.as_ast()), self.ctx)

    def __div__(self, other):
        """Create the Z3 expression (signed) division `self / other`.

        Use the function UDiv() for unsigned division.

        >>> x = BitVec('x', 32)
        >>> y = BitVec('y', 32)
        >>> x / y
        x/y
        >>> (x / y).sort()
        BitVec(32)
        >>> (x / y).sexpr()
        '(bvsdiv x y)'
        >>> UDiv(x, y).sexpr()
        '(bvudiv x y)'
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(Z3_mk_bvsdiv(self.ctx_ref(), a.as_ast(), b.as_ast()), self.ctx)

    def __truediv__(self, other):
        """Create the Z3 expression (signed) division `self / other`."""
        return self.__div__(other)

    def __rdiv__(self, other):
        """Create the Z3 expression (signed) division `other / self`.

        Use the function UDiv() for unsigned division.

        >>> x = BitVec('x', 32)
        >>> 10 / x
        10/x
        >>> (10 / x).sexpr()
        '(bvsdiv #x0000000a x)'
        >>> UDiv(10, x).sexpr()
        '(bvudiv #x0000000a x)'
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(Z3_mk_bvsdiv(self.ctx_ref(), b.as_ast(), a.as_ast()), self.ctx)

    def __rtruediv__(self, other):
        """Create the Z3 expression (signed) division `other / self`."""
        return self.__rdiv__(other)

    def __mod__(self, other):
        """Create the Z3 expression (signed) mod `self % other`.

        Use the function URem() for unsigned remainder, and SRem() for signed remainder.

        >>> x = BitVec('x', 32)
        >>> y = BitVec('y', 32)
        >>> x % y
        x%y
        >>> (x % y).sort()
        BitVec(32)
        >>> (x % y).sexpr()
        '(bvsmod x y)'
        >>> URem(x, y).sexpr()
        '(bvurem x y)'
        >>> SRem(x, y).sexpr()
        '(bvsrem x y)'
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(Z3_mk_bvsmod(self.ctx_ref(), a.as_ast(), b.as_ast()), self.ctx)

    def __rmod__(self, other):
        """Create the Z3 expression (signed) mod `other % self`.

        Use the function URem() for unsigned remainder, and SRem() for signed remainder.

        >>> x = BitVec('x', 32)
        >>> 10 % x
        10%x
        >>> (10 % x).sexpr()
        '(bvsmod #x0000000a x)'
        >>> URem(10, x).sexpr()
        '(bvurem #x0000000a x)'
        >>> SRem(10, x).sexpr()
        '(bvsrem #x0000000a x)'
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(Z3_mk_bvsmod(self.ctx_ref(), b.as_ast(), a.as_ast()), self.ctx)

    def __le__(self, other):
        """Create the Z3 expression (signed) `other <= self`.

        Use the function ULE() for unsigned less than or equal to.

        >>> x, y = BitVecs('x y', 32)
        >>> x <= y
        x <= y
        >>> (x <= y).sexpr()
        '(bvsle x y)'
        >>> ULE(x, y).sexpr()
        '(bvule x y)'
        """
        a, b = _coerce_exprs(self, other)
        return BoolRef(Z3_mk_bvsle(self.ctx_ref(), a.as_ast(), b.as_ast()), self.ctx)

    def __lt__(self, other):
        """Create the Z3 expression (signed) `other < self`.

        Use the function ULT() for unsigned less than.

        >>> x, y = BitVecs('x y', 32)
        >>> x < y
        x < y
        >>> (x < y).sexpr()
        '(bvslt x y)'
        >>> ULT(x, y).sexpr()
        '(bvult x y)'
        """
        a, b = _coerce_exprs(self, other)
        return BoolRef(Z3_mk_bvslt(self.ctx_ref(), a.as_ast(), b.as_ast()), self.ctx)

    def __gt__(self, other):
        """Create the Z3 expression (signed) `other > self`.

        Use the function UGT() for unsigned greater than.

        >>> x, y = BitVecs('x y', 32)
        >>> x > y
        x > y
        >>> (x > y).sexpr()
        '(bvsgt x y)'
        >>> UGT(x, y).sexpr()
        '(bvugt x y)'
        """
        a, b = _coerce_exprs(self, other)
        return BoolRef(Z3_mk_bvsgt(self.ctx_ref(), a.as_ast(), b.as_ast()), self.ctx)

    def __ge__(self, other):
        """Create the Z3 expression (signed) `other >= self`.

        Use the function UGE() for unsigned greater than or equal to.

        >>> x, y = BitVecs('x y', 32)
        >>> x >= y
        x >= y
        >>> (x >= y).sexpr()
        '(bvsge x y)'
        >>> UGE(x, y).sexpr()
        '(bvuge x y)'
        """
        a, b = _coerce_exprs(self, other)
        return BoolRef(Z3_mk_bvsge(self.ctx_ref(), a.as_ast(), b.as_ast()), self.ctx)

    def __rshift__(self, other):
        """Create the Z3 expression (arithmetical) right shift `self >> other`

        Use the function LShR() for the right logical shift

        >>> x, y = BitVecs('x y', 32)
        >>> x >> y
        x >> y
        >>> (x >> y).sexpr()
        '(bvashr x y)'
        >>> LShR(x, y).sexpr()
        '(bvlshr x y)'
        >>> BitVecVal(4, 3)
        4
        >>> BitVecVal(4, 3).as_signed_long()
        -4
        >>> simplify(BitVecVal(4, 3) >> 1).as_signed_long()
        -2
        >>> simplify(BitVecVal(4, 3) >> 1)
        6
        >>> simplify(LShR(BitVecVal(4, 3), 1))
        2
        >>> simplify(BitVecVal(2, 3) >> 1)
        1
        >>> simplify(LShR(BitVecVal(2, 3), 1))
        1
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(Z3_mk_bvashr(self.ctx_ref(), a.as_ast(), b.as_ast()), self.ctx)

    def __lshift__(self, other):
        """Create the Z3 expression left shift `self << other`

        >>> x, y = BitVecs('x y', 32)
        >>> x << y
        x << y
        >>> (x << y).sexpr()
        '(bvshl x y)'
        >>> simplify(BitVecVal(2, 3) << 1)
        4
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(Z3_mk_bvshl(self.ctx_ref(), a.as_ast(), b.as_ast()), self.ctx)

    def __rrshift__(self, other):
        """Create the Z3 expression (arithmetical) right shift `other` >> `self`.

        Use the function LShR() for the right logical shift

        >>> x = BitVec('x', 32)
        >>> 10 >> x
        10 >> x
        >>> (10 >> x).sexpr()
        '(bvashr #x0000000a x)'
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(Z3_mk_bvashr(self.ctx_ref(), b.as_ast(), a.as_ast()), self.ctx)

    def __rlshift__(self, other):
        """Create the Z3 expression left shift `other << self`.

        Use the function LShR() for the right logical shift

        >>> x = BitVec('x', 32)
        >>> 10 << x
        10 << x
        >>> (10 << x).sexpr()
        '(bvshl #x0000000a x)'
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(Z3_mk_bvshl(self.ctx_ref(), b.as_ast(), a.as_ast()), self.ctx)

class BitVecNumRef(BitVecRef):
    """Bit-vector values."""

    def as_long(self):
        """Return a Z3 bit-vector numeral as a Python long (bignum) numeral.

        >>> v = BitVecVal(0xbadc0de, 32)
        >>> v
        195936478
        >>> print("0x%.8x" % v.as_long())
        0x0badc0de
        """
        return int(self.as_string())

    def as_signed_long(self):
        """Return a Z3 bit-vector numeral as a Python long (bignum) numeral. The most significant bit is assumed to be the sign.

        >>> BitVecVal(4, 3).as_signed_long()
        -4
        >>> BitVecVal(7, 3).as_signed_long()
        -1
        >>> BitVecVal(3, 3).as_signed_long()
        3
        >>> BitVecVal(2**32 - 1, 32).as_signed_long()
        -1
        >>> BitVecVal(2**64 - 1, 64).as_signed_long()
        -1
        """
        sz = self.size()
        val = self.as_long()
        if val >= 2**(sz - 1):
            val = val - 2**sz
        if val < -2**(sz - 1):
            val = val + 2**sz
        return int(val)

    def as_string(self):
        return Z3_get_numeral_string(self.ctx_ref(), self.as_ast())

def is_bv(a):
    """Return `True` if `a` is a Z3 bit-vector expression.

    >>> b = BitVec('b', 32)
    >>> is_bv(b)
    True
    >>> is_bv(b + 10)
    True
    >>> is_bv(Int('x'))
    False
    """
    return isinstance(a, BitVecRef)

def is_bv_value(a):
    """Return `True` if `a` is a Z3 bit-vector numeral value.

    >>> b = BitVec('b', 32)
    >>> is_bv_value(b)
    False
    >>> b = BitVecVal(10, 32)
    >>> b
    10
    >>> is_bv_value(b)
    True
    """
    return is_bv(a) and _is_numeral(a.ctx, a.as_ast())

def BV2Int(a, is_signed=False):
    """Return the Z3 expression BV2Int(a).

    >>> b = BitVec('b', 3)
    >>> BV2Int(b).sort()
    Int
    >>> x = Int('x')
    >>> x > BV2Int(b)
    x > BV2Int(b)
    >>> x > BV2Int(b, is_signed=False)
    x > BV2Int(b)
    >>> x > BV2Int(b, is_signed=True)
    x > If(b < 0, BV2Int(b) - 8, BV2Int(b))
    >>> solve(x > BV2Int(b), b == 1, x < 3)
    [b = 1, x = 2]
    """
    if __debug__:
        _z3_assert(is_bv(a), "Z3 bit-vector expression expected")
    ctx = a.ctx
    ## investigate problem with bv2int
    return ArithRef(Z3_mk_bv2int(ctx.ref(), a.as_ast(), is_signed), ctx)

def Int2BV(a, num_bits):
    """Return the z3 expression Int2BV(a, num_bits).
    It is a bit-vector of width num_bits and represents the
    modulo of a by 2^num_bits
    """
    ctx = a.ctx
    return BitVecRef(Z3_mk_int2bv(ctx.ref(), num_bits, a.as_ast()), ctx)

def BitVecSort(sz, ctx=None):
    """Return a Z3 bit-vector sort of the given size. If `ctx=None`, then the global context is used.

    >>> Byte = BitVecSort(8)
    >>> Word = BitVecSort(16)
    >>> Byte
    BitVec(8)
    >>> x = Const('x', Byte)
    >>> eq(x, BitVec('x', 8))
    True
    """
    ctx = _get_ctx(ctx)
    return BitVecSortRef(Z3_mk_bv_sort(ctx.ref(), sz), ctx)

def BitVecVal(val, bv, ctx=None):
    """Return a bit-vector value with the given number of bits. If `ctx=None`, then the global context is used.

    >>> v = BitVecVal(10, 32)
    >>> v
    10
    >>> print("0x%.8x" % v.as_long())
    0x0000000a
    """
    if is_bv_sort(bv):
        ctx = bv.ctx
        return BitVecNumRef(Z3_mk_numeral(ctx.ref(), _to_int_str(val), bv.ast), ctx)
    else:
        ctx = _get_ctx(ctx)
        return BitVecNumRef(Z3_mk_numeral(ctx.ref(), _to_int_str(val), BitVecSort(bv, ctx).ast), ctx)

def BitVec(name, bv, ctx=None):
    """Return a bit-vector constant named `name`. `bv` may be the number of bits of a bit-vector sort.
    If `ctx=None`, then the global context is used.

    >>> x  = BitVec('x', 16)
    >>> is_bv(x)
    True
    >>> x.size()
    16
    >>> x.sort()
    BitVec(16)
    >>> word = BitVecSort(16)
    >>> x2 = BitVec('x', word)
    >>> eq(x, x2)
    True
    """
    if isinstance(bv, BitVecSortRef):
        ctx = bv.ctx
    else:
        ctx = _get_ctx(ctx)
        bv = BitVecSort(bv, ctx)
    return BitVecRef(Z3_mk_const(ctx.ref(), to_symbol(name, ctx), bv.ast), ctx)

def BitVecs(names, bv, ctx=None):
    """Return a tuple of bit-vector constants of size bv.

    >>> x, y, z = BitVecs('x y z', 16)
    >>> x.size()
    16
    >>> x.sort()
    BitVec(16)
    >>> Sum(x, y, z)
    0 + x + y + z
    >>> Product(x, y, z)
    1*x*y*z
    >>> simplify(Product(x, y, z))
    x*y*z
    """
    ctx = _get_ctx(ctx)
    if isinstance(names, str):
        names = names.split(" ")
    return [BitVec(name, bv, ctx) for name in names]

def Concat(*args):
    """Create a Z3 bit-vector concatenation expression.

    >>> v = BitVecVal(1, 4)
    >>> Concat(v, v+1, v)
    Concat(Concat(1, 1 + 1), 1)
    >>> simplify(Concat(v, v+1, v))
    289
    >>> print("%.3x" % simplify(Concat(v, v+1, v)).as_long())
    121
    """
    args = _get_args(args)
    sz = len(args)
    if __debug__:
        _z3_assert(sz >= 2, "At least two arguments expected.")

    ctx = None
    for a in args:
        if is_expr(a):
            ctx = a.ctx
            break
    if is_seq(args[0]) or isinstance(args[0], str):
        args = [_coerce_seq(s, ctx) for s in args]
        if __debug__:
            _z3_assert(all([is_seq(a) for a in args]), "All arguments must be sequence expressions.")
        v = (Ast * sz)()
        for i in range(sz):
            v[i] = args[i].as_ast()
        return SeqRef(Z3_mk_seq_concat(ctx.ref(), sz, v), ctx)

    if is_re(args[0]):
       if __debug__:
           _z3_assert(all([is_re(a) for a in args]), "All arguments must be regular expressions.")
       v = (Ast * sz)()
       for i in range(sz):
           v[i] = args[i].as_ast()
       return ReRef(Z3_mk_re_concat(ctx.ref(), sz, v), ctx)

    if __debug__:
        _z3_assert(all([is_bv(a) for a in args]), "All arguments must be Z3 bit-vector expressions.")
    r   = args[0]
    for i in range(sz - 1):
        r = BitVecRef(Z3_mk_concat(ctx.ref(), r.as_ast(), args[i+1].as_ast()), ctx)
    return r

def Extract(high, low, a):
    """Create a Z3 bit-vector extraction expression, or create a string extraction expression.

    >>> x = BitVec('x', 8)
    >>> Extract(6, 2, x)
    Extract(6, 2, x)
    >>> Extract(6, 2, x).sort()
    BitVec(5)
    >>> simplify(Extract(StringVal("abcd"),2,1))
    "c"
    """
    if isinstance(high, str):
        high = StringVal(high)
    if is_seq(high):
        s = high
        offset, length = _coerce_exprs(low, a, s.ctx)
        return SeqRef(Z3_mk_seq_extract(s.ctx_ref(), s.as_ast(), offset.as_ast(), length.as_ast()), s.ctx)
    if __debug__:
        _z3_assert(low <= high, "First argument must be greater than or equal to second argument")
        _z3_assert(_is_int(high) and high >= 0 and _is_int(low) and low >= 0, "First and second arguments must be non negative integers")
        _z3_assert(is_bv(a), "Third argument must be a Z3 Bitvector expression")
    return BitVecRef(Z3_mk_extract(a.ctx_ref(), high, low, a.as_ast()), a.ctx)

def _check_bv_args(a, b):
    if __debug__:
        _z3_assert(is_bv(a) or is_bv(b), "At least one of the arguments must be a Z3 bit-vector expression")

def ULE(a, b):
    """Create the Z3 expression (unsigned) `other <= self`.

    Use the operator <= for signed less than or equal to.

    >>> x, y = BitVecs('x y', 32)
    >>> ULE(x, y)
    ULE(x, y)
    >>> (x <= y).sexpr()
    '(bvsle x y)'
    >>> ULE(x, y).sexpr()
    '(bvule x y)'
    """
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BoolRef(Z3_mk_bvule(a.ctx_ref(), a.as_ast(), b.as_ast()), a.ctx)

def ULT(a, b):
    """Create the Z3 expression (unsigned) `other < self`.

    Use the operator < for signed less than.

    >>> x, y = BitVecs('x y', 32)
    >>> ULT(x, y)
    ULT(x, y)
    >>> (x < y).sexpr()
    '(bvslt x y)'
    >>> ULT(x, y).sexpr()
    '(bvult x y)'
    """
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BoolRef(Z3_mk_bvult(a.ctx_ref(), a.as_ast(), b.as_ast()), a.ctx)

def UGE(a, b):
    """Create the Z3 expression (unsigned) `other >= self`.

    Use the operator >= for signed greater than or equal to.

    >>> x, y = BitVecs('x y', 32)
    >>> UGE(x, y)
    UGE(x, y)
    >>> (x >= y).sexpr()
    '(bvsge x y)'
    >>> UGE(x, y).sexpr()
    '(bvuge x y)'
    """
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BoolRef(Z3_mk_bvuge(a.ctx_ref(), a.as_ast(), b.as_ast()), a.ctx)

def UGT(a, b):
    """Create the Z3 expression (unsigned) `other > self`.

    Use the operator > for signed greater than.

    >>> x, y = BitVecs('x y', 32)
    >>> UGT(x, y)
    UGT(x, y)
    >>> (x > y).sexpr()
    '(bvsgt x y)'
    >>> UGT(x, y).sexpr()
    '(bvugt x y)'
    """
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BoolRef(Z3_mk_bvugt(a.ctx_ref(), a.as_ast(), b.as_ast()), a.ctx)

def UDiv(a, b):
    """Create the Z3 expression (unsigned) division `self / other`.

    Use the operator / for signed division.

    >>> x = BitVec('x', 32)
    >>> y = BitVec('y', 32)
    >>> UDiv(x, y)
    UDiv(x, y)
    >>> UDiv(x, y).sort()
    BitVec(32)
    >>> (x / y).sexpr()
    '(bvsdiv x y)'
    >>> UDiv(x, y).sexpr()
    '(bvudiv x y)'
    """
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BitVecRef(Z3_mk_bvudiv(a.ctx_ref(), a.as_ast(), b.as_ast()), a.ctx)

def URem(a, b):
    """Create the Z3 expression (unsigned) remainder `self % other`.

    Use the operator % for signed modulus, and SRem() for signed remainder.

    >>> x = BitVec('x', 32)
    >>> y = BitVec('y', 32)
    >>> URem(x, y)
    URem(x, y)
    >>> URem(x, y).sort()
    BitVec(32)
    >>> (x % y).sexpr()
    '(bvsmod x y)'
    >>> URem(x, y).sexpr()
    '(bvurem x y)'
    """
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BitVecRef(Z3_mk_bvurem(a.ctx_ref(), a.as_ast(), b.as_ast()), a.ctx)

def SRem(a, b):
    """Create the Z3 expression signed remainder.

    Use the operator % for signed modulus, and URem() for unsigned remainder.

    >>> x = BitVec('x', 32)
    >>> y = BitVec('y', 32)
    >>> SRem(x, y)
    SRem(x, y)
    >>> SRem(x, y).sort()
    BitVec(32)
    >>> (x % y).sexpr()
    '(bvsmod x y)'
    >>> SRem(x, y).sexpr()
    '(bvsrem x y)'
    """
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BitVecRef(Z3_mk_bvsrem(a.ctx_ref(), a.as_ast(), b.as_ast()), a.ctx)

def LShR(a, b):
    """Create the Z3 expression logical right shift.

    Use the operator >> for the arithmetical right shift.

    >>> x, y = BitVecs('x y', 32)
    >>> LShR(x, y)
    LShR(x, y)
    >>> (x >> y).sexpr()
    '(bvashr x y)'
    >>> LShR(x, y).sexpr()
    '(bvlshr x y)'
    >>> BitVecVal(4, 3)
    4
    >>> BitVecVal(4, 3).as_signed_long()
    -4
    >>> simplify(BitVecVal(4, 3) >> 1).as_signed_long()
    -2
    >>> simplify(BitVecVal(4, 3) >> 1)
    6
    >>> simplify(LShR(BitVecVal(4, 3), 1))
    2
    >>> simplify(BitVecVal(2, 3) >> 1)
    1
    >>> simplify(LShR(BitVecVal(2, 3), 1))
    1
    """
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BitVecRef(Z3_mk_bvlshr(a.ctx_ref(), a.as_ast(), b.as_ast()), a.ctx)

def RotateLeft(a, b):
    """Return an expression representing `a` rotated to the left `b` times.

    >>> a, b = BitVecs('a b', 16)
    >>> RotateLeft(a, b)
    RotateLeft(a, b)
    >>> simplify(RotateLeft(a, 0))
    a
    >>> simplify(RotateLeft(a, 16))
    a
    """
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BitVecRef(Z3_mk_ext_rotate_left(a.ctx_ref(), a.as_ast(), b.as_ast()), a.ctx)

def RotateRight(a, b):
    """Return an expression representing `a` rotated to the right `b` times.

    >>> a, b = BitVecs('a b', 16)
    >>> RotateRight(a, b)
    RotateRight(a, b)
    >>> simplify(RotateRight(a, 0))
    a
    >>> simplify(RotateRight(a, 16))
    a
    """
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BitVecRef(Z3_mk_ext_rotate_right(a.ctx_ref(), a.as_ast(), b.as_ast()), a.ctx)

def SignExt(n, a):
    """Return a bit-vector expression with `n` extra sign-bits.

    >>> x = BitVec('x', 16)
    >>> n = SignExt(8, x)
    >>> n.size()
    24
    >>> n
    SignExt(8, x)
    >>> n.sort()
    BitVec(24)
    >>> v0 = BitVecVal(2, 2)
    >>> v0
    2
    >>> v0.size()
    2
    >>> v  = simplify(SignExt(6, v0))
    >>> v
    254
    >>> v.size()
    8
    >>> print("%.x" % v.as_long())
    fe
    """
    if __debug__:
        _z3_assert(_is_int(n), "First argument must be an integer")
        _z3_assert(is_bv(a), "Second argument must be a Z3 Bitvector expression")
    return BitVecRef(Z3_mk_sign_ext(a.ctx_ref(), n, a.as_ast()), a.ctx)

def ZeroExt(n, a):
    """Return a bit-vector expression with `n` extra zero-bits.

    >>> x = BitVec('x', 16)
    >>> n = ZeroExt(8, x)
    >>> n.size()
    24
    >>> n
    ZeroExt(8, x)
    >>> n.sort()
    BitVec(24)
    >>> v0 = BitVecVal(2, 2)
    >>> v0
    2
    >>> v0.size()
    2
    >>> v  = simplify(ZeroExt(6, v0))
    >>> v
    2
    >>> v.size()
    8
    """
    if __debug__:
        _z3_assert(_is_int(n), "First argument must be an integer")
        _z3_assert(is_bv(a), "Second argument must be a Z3 Bitvector expression")
    return BitVecRef(Z3_mk_zero_ext(a.ctx_ref(), n, a.as_ast()), a.ctx)

def RepeatBitVec(n, a):
    """Return an expression representing `n` copies of `a`.

    >>> x = BitVec('x', 8)
    >>> n = RepeatBitVec(4, x)
    >>> n
    RepeatBitVec(4, x)
    >>> n.size()
    32
    >>> v0 = BitVecVal(10, 4)
    >>> print("%.x" % v0.as_long())
    a
    >>> v = simplify(RepeatBitVec(4, v0))
    >>> v.size()
    16
    >>> print("%.x" % v.as_long())
    aaaa
    """
    if __debug__:
        _z3_assert(_is_int(n), "First argument must be an integer")
        _z3_assert(is_bv(a), "Second argument must be a Z3 Bitvector expression")
    return BitVecRef(Z3_mk_repeat(a.ctx_ref(), n, a.as_ast()), a.ctx)

def BVRedAnd(a):
    """Return the reduction-and expression of `a`."""
    if __debug__:
        _z3_assert(is_bv(a), "First argument must be a Z3 Bitvector expression")
    return BitVecRef(Z3_mk_bvredand(a.ctx_ref(), a.as_ast()), a.ctx)

def BVRedOr(a):
    """Return the reduction-or expression of `a`."""
    if __debug__:
        _z3_assert(is_bv(a), "First argument must be a Z3 Bitvector expression")
    return BitVecRef(Z3_mk_bvredor(a.ctx_ref(), a.as_ast()), a.ctx)

def BVAddNoOverflow(a, b, signed):
    """A predicate the determines that bit-vector addition does not overflow"""
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BoolRef(Z3_mk_bvadd_no_overflow(a.ctx_ref(), a.as_ast(), b.as_ast(), signed), a.ctx)

def BVAddNoUnderflow(a, b):
    """A predicate the determines that signed bit-vector addition does not underflow"""
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BoolRef(Z3_mk_bvadd_no_underflow(a.ctx_ref(), a.as_ast(), b.as_ast()), a.ctx)

def BVSubNoOverflow(a, b):
    """A predicate the determines that bit-vector subtraction does not overflow"""
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BoolRef(Z3_mk_bvsub_no_overflow(a.ctx_ref(), a.as_ast(), b.as_ast()), a.ctx)
    

def BVSubNoUnderflow(a, b, signed):
    """A predicate the determines that bit-vector subtraction does not underflow"""
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BoolRef(Z3_mk_bvsub_no_underflow(a.ctx_ref(), a.as_ast(), b.as_ast(), signed), a.ctx)

def BVSDivNoOverflow(a, b):
    """A predicate the determines that bit-vector signed division does not overflow"""
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BoolRef(Z3_mk_bvsdiv_no_overflow(a.ctx_ref(), a.as_ast(), b.as_ast()), a.ctx)

def BVSNegNoOverflow(a):
    """A predicate the determines that bit-vector unary negation does not overflow"""
    if __debug__:
        _z3_assert(is_bv(a), "Argument should be a bit-vector")
    return BoolRef(Z3_mk_bvneg_no_overflow(a.ctx_ref(), a.as_ast()), a.ctx)

def BVMulNoOverflow(a, b, signed):
    """A predicate the determines that bit-vector multiplication does not overflow"""
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BoolRef(Z3_mk_bvmul_no_overflow(a.ctx_ref(), a.as_ast(), b.as_ast(), signed), a.ctx)


def BVMulNoUnderflow(a, b):
    """A predicate the determines that bit-vector signed multiplication does not underflow"""
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BoolRef(Z3_mk_bvmul_no_underflow(a.ctx_ref(), a.as_ast(), b.as_ast()), a.ctx)



#########################################
#
# Arrays
#
#########################################

class ArraySortRef(SortRef):
    """Array sorts."""

    def domain(self):
        """Return the domain of the array sort `self`.

        >>> A = ArraySort(IntSort(), BoolSort())
        >>> A.domain()
        Int
        """
        return _to_sort_ref(Z3_get_array_sort_domain(self.ctx_ref(), self.ast), self.ctx)

    def range(self):
        """Return the range of the array sort `self`.

        >>> A = ArraySort(IntSort(), BoolSort())
        >>> A.range()
        Bool
        """
        return _to_sort_ref(Z3_get_array_sort_range(self.ctx_ref(), self.ast), self.ctx)    

class ArrayRef(ExprRef):
    """Array expressions. """

    def sort(self):
        """Return the array sort of the array expression `self`.

        >>> a = Array('a', IntSort(), BoolSort())
        >>> a.sort()
        Array(Int, Bool)
        """
        return ArraySortRef(Z3_get_sort(self.ctx_ref(), self.as_ast()), self.ctx)

    def domain(self):
        """Shorthand for `self.sort().domain()`.

        >>> a = Array('a', IntSort(), BoolSort())
        >>> a.domain()
        Int
        """
        return self.sort().domain()

    def range(self):
        """Shorthand for `self.sort().range()`.

        >>> a = Array('a', IntSort(), BoolSort())
        >>> a.range()
        Bool
        """
        return self.sort().range()

    def __getitem__(self, arg):
        """Return the Z3 expression `self[arg]`.

        >>> a = Array('a', IntSort(), BoolSort())
        >>> i = Int('i')
        >>> a[i]
        a[i]
        >>> a[i].sexpr()
        '(select a i)'
        """
        arg = self.domain().cast(arg)
        return _to_expr_ref(Z3_mk_select(self.ctx_ref(), self.as_ast(), arg.as_ast()), self.ctx)

    def default(self):
        return _to_expr_ref(Z3_mk_array_default(self.ctx_ref(), self.as_ast()), self.ctx)


def is_array(a):
    """Return `True` if `a` is a Z3 array expression.

    >>> a = Array('a', IntSort(), IntSort())
    >>> is_array(a)
    True
    >>> is_array(Store(a, 0, 1))
    True
    >>> is_array(a[0])
    False
    """
    return isinstance(a, ArrayRef)

def is_const_array(a):
    """Return `True` if `a` is a Z3 constant array.

    >>> a = K(IntSort(), 10)
    >>> is_const_array(a)
    True
    >>> a = Array('a', IntSort(), IntSort())
    >>> is_const_array(a)
    False
    """
    return is_app_of(a, Z3_OP_CONST_ARRAY)

def is_K(a):
    """Return `True` if `a` is a Z3 constant array.

    >>> a = K(IntSort(), 10)
    >>> is_K(a)
    True
    >>> a = Array('a', IntSort(), IntSort())
    >>> is_K(a)
    False
    """
    return is_app_of(a, Z3_OP_CONST_ARRAY)

def is_map(a):
    """Return `True` if `a` is a Z3 map array expression.

    >>> f = Function('f', IntSort(), IntSort())
    >>> b = Array('b', IntSort(), IntSort())
    >>> a  = Map(f, b)
    >>> a
    Map(f, b)
    >>> is_map(a)
    True
    >>> is_map(b)
    False
    """
    return is_app_of(a, Z3_OP_ARRAY_MAP)

def is_default(a):
    """Return `True` if `a` is a Z3 default array expression.
    >>> d = Default(K(IntSort(), 10))
    >>> is_default(d)
    True
    """
    return is_app_of(a, Z3_OP_ARRAY_DEFAULT)

def get_map_func(a):
    """Return the function declaration associated with a Z3 map array expression.

    >>> f = Function('f', IntSort(), IntSort())
    >>> b = Array('b', IntSort(), IntSort())
    >>> a  = Map(f, b)
    >>> eq(f, get_map_func(a))
    True
    >>> get_map_func(a)
    f
    >>> get_map_func(a)(0)
    f(0)
    """
    if __debug__:
        _z3_assert(is_map(a), "Z3 array map expression expected.")
    return FuncDeclRef(Z3_to_func_decl(a.ctx_ref(), Z3_get_decl_ast_parameter(a.ctx_ref(), a.decl().ast, 0)), a.ctx)

def ArraySort(d, r):
    """Return the Z3 array sort with the given domain and range sorts.

    >>> A = ArraySort(IntSort(), BoolSort())
    >>> A
    Array(Int, Bool)
    >>> A.domain()
    Int
    >>> A.range()
    Bool
    >>> AA = ArraySort(IntSort(), A)
    >>> AA
    Array(Int, Array(Int, Bool))
    """
    if __debug__:
        _z3_assert(is_sort(d), "Z3 sort expected")
        _z3_assert(is_sort(r), "Z3 sort expected")
        _z3_assert(d.ctx == r.ctx, "Context mismatch")
    ctx = d.ctx
    return ArraySortRef(Z3_mk_array_sort(ctx.ref(), d.ast, r.ast), ctx)

def Array(name, dom, rng):
    """Return an array constant named `name` with the given domain and range sorts.

    >>> a = Array('a', IntSort(), IntSort())
    >>> a.sort()
    Array(Int, Int)
    >>> a[0]
    a[0]
    """
    s = ArraySort(dom, rng)
    ctx = s.ctx
    return ArrayRef(Z3_mk_const(ctx.ref(), to_symbol(name, ctx), s.ast), ctx)

def Update(a, i, v):
    """Return a Z3 store array expression.

    >>> a    = Array('a', IntSort(), IntSort())
    >>> i, v = Ints('i v')
    >>> s    = Update(a, i, v)
    >>> s.sort()
    Array(Int, Int)
    >>> prove(s[i] == v)
    proved
    >>> j    = Int('j')
    >>> prove(Implies(i != j, s[j] == a[j]))
    proved
    """
    if __debug__:
        _z3_assert(is_array(a), "First argument must be a Z3 array expression")
    i = a.domain().cast(i)
    v = a.range().cast(v)
    ctx = a.ctx
    return _to_expr_ref(Z3_mk_store(ctx.ref(), a.as_ast(), i.as_ast(), v.as_ast()), ctx)

def Default(a):
    """ Return a default value for array expression.
    >>> b = K(IntSort(), 1)
    >>> prove(Default(b) == 1)
    proved
    """
    if __debug__:
        _z3_assert(is_array(a), "First argument must be a Z3 array expression")
    return a.default()


def Store(a, i, v):
    """Return a Z3 store array expression.

    >>> a    = Array('a', IntSort(), IntSort())
    >>> i, v = Ints('i v')
    >>> s    = Store(a, i, v)
    >>> s.sort()
    Array(Int, Int)
    >>> prove(s[i] == v)
    proved
    >>> j    = Int('j')
    >>> prove(Implies(i != j, s[j] == a[j]))
    proved
    """
    return Update(a, i, v)

def Select(a, i):
    """Return a Z3 select array expression.

    >>> a = Array('a', IntSort(), IntSort())
    >>> i = Int('i')
    >>> Select(a, i)
    a[i]
    >>> eq(Select(a, i), a[i])
    True
    """
    if __debug__:
        _z3_assert(is_array(a), "First argument must be a Z3 array expression")
    return a[i]

    
def Map(f, *args):
    """Return a Z3 map array expression.

    >>> f = Function('f', IntSort(), IntSort(), IntSort())
    >>> a1 = Array('a1', IntSort(), IntSort())
    >>> a2 = Array('a2', IntSort(), IntSort())
    >>> b  = Map(f, a1, a2)
    >>> b
    Map(f, a1, a2)
    >>> prove(b[0] == f(a1[0], a2[0]))
    proved
    """
    args = _get_args(args)
    if __debug__:
        _z3_assert(len(args) > 0, "At least one Z3 array expression expected")
        _z3_assert(is_func_decl(f), "First argument must be a Z3 function declaration")
        _z3_assert(all([is_array(a) for a in args]), "Z3 array expected expected")
        _z3_assert(len(args) == f.arity(), "Number of arguments mismatch")
    _args, sz = _to_ast_array(args)
    ctx = f.ctx
    return ArrayRef(Z3_mk_map(ctx.ref(), f.ast, sz, _args), ctx)

def K(dom, v):
    """Return a Z3 constant array expression.

    >>> a = K(IntSort(), 10)
    >>> a
    K(Int, 10)
    >>> a.sort()
    Array(Int, Int)
    >>> i = Int('i')
    >>> a[i]
    K(Int, 10)[i]
    >>> simplify(a[i])
    10
    """
    if __debug__:
        _z3_assert(is_sort(dom), "Z3 sort expected")
    ctx = dom.ctx
    if not is_expr(v):
        v = _py2expr(v, ctx)
    return ArrayRef(Z3_mk_const_array(ctx.ref(), dom.ast, v.as_ast()), ctx)

def Ext(a, b):
    """Return extensionality index for arrays.
    """
    if __debug__:
        _z3_assert(is_array(a) and is_array(b))
    return _to_expr_ref(Z3_mk_array_ext(ctx.ref(), a.as_ast(), b.as_ast()));

def is_select(a):
    """Return `True` if `a` is a Z3 array select application.

    >>> a = Array('a', IntSort(), IntSort())
    >>> is_select(a)
    False
    >>> i = Int('i')
    >>> is_select(a[i])
    True
    """
    return is_app_of(a, Z3_OP_SELECT)

def is_store(a):
    """Return `True` if `a` is a Z3 array store application.

    >>> a = Array('a', IntSort(), IntSort())
    >>> is_store(a)
    False
    >>> is_store(Store(a, 0, 1))
    True
    """
    return is_app_of(a, Z3_OP_STORE)

#########################################
#
# Sets
#
#########################################


def SetSort(s):
    """ Create a set sort over element sort s"""
    return ArraySort(s, BoolSort())

def EmptySet(s):
    """Create the empty set
    >>> EmptySet(IntSort())
    K(Int, False)
    """
    ctx = s.ctx
    return ArrayRef(Z3_mk_empty_set(ctx.ref(), s.ast), ctx)

def FullSet(s):
    """Create the full set
    >>> FullSet(IntSort())
    K(Int, True)
    """
    ctx = s.ctx
    return ArrayRef(Z3_mk_full_set(ctx.ref(), s.ast), ctx)

def SetUnion(*args):
    """ Take the union of sets
    >>> a = Const('a', SetSort(IntSort()))
    >>> b = Const('b', SetSort(IntSort()))
    >>> SetUnion(a, b)
    union(a, b)
    """
    args = _get_args(args)
    ctx = _ctx_from_ast_arg_list(args)
    _args, sz = _to_ast_array(args)
    return ArrayRef(Z3_mk_set_union(ctx.ref(), sz, _args), ctx)

def SetIntersect(*args):
    """ Take the union of sets
    >>> a = Const('a', SetSort(IntSort()))
    >>> b = Const('b', SetSort(IntSort()))
    >>> SetIntersect(a, b)
    intersect(a, b)
    """
    args = _get_args(args)
    ctx = _ctx_from_ast_arg_list(args)
    _args, sz = _to_ast_array(args)
    return ArrayRef(Z3_mk_set_intersect(ctx.ref(), sz, _args), ctx)

def SetAdd(s, e):
    """ Add element e to set s
    >>> a = Const('a', SetSort(IntSort()))
    >>> SetAdd(a, 1)
    Store(a, 1, True)
    """
    ctx = _ctx_from_ast_arg_list([s,e])
    e = _py2expr(e, ctx)
    return ArrayRef(Z3_mk_set_add(ctx.ref(), s.as_ast(), e.as_ast()), ctx)

def SetDel(s, e):
    """ Remove element e to set s
    >>> a = Const('a', SetSort(IntSort()))
    >>> SetDel(a, 1)
    Store(a, 1, False)
    """
    ctx = _ctx_from_ast_arg_list([s,e])
    e = _py2expr(e, ctx)
    return ArrayRef(Z3_mk_set_del(ctx.ref(), s.as_ast(), e.as_ast()), ctx)

def SetComplement(s):
    """ The complement of set s
    >>> a = Const('a', SetSort(IntSort()))
    >>> SetComplement(a)
    complement(a)
    """
    ctx = s.ctx
    return ArrayRef(Z3_mk_set_complement(ctx.ref(), s.as_ast()), ctx)

def SetDifference(a, b):
    """ The set difference of a and b
    >>> a = Const('a', SetSort(IntSort()))
    >>> b = Const('b', SetSort(IntSort()))
    >>> SetDifference(a, b)
    difference(a, b)
    """
    ctx = _ctx_from_ast_arg_list([a, b])
    return ArrayRef(Z3_mk_set_difference(ctx.ref(), a.as_ast(), b.as_ast()), ctx)
      
def IsMember(e, s):
    """ Check if e is a member of set s
    >>> a = Const('a', SetSort(IntSort()))
    >>> IsMember(1, a)
    a[1]
    """
    ctx = _ctx_from_ast_arg_list([s,e])
    e = _py2expr(e, ctx)
    return BoolRef(Z3_mk_set_member(ctx.ref(), e.as_ast(), s.as_ast()), ctx)
    
def IsSubset(a, b):
    """ Check if a is a subset of b
    >>> a = Const('a', SetSort(IntSort()))
    >>> b = Const('b', SetSort(IntSort()))
    >>> IsSubset(a, b)
    subset(a, b)
    """
    ctx = _ctx_from_ast_arg_list([a, b])
    return BoolRef(Z3_mk_set_subset(ctx.ref(), a.as_ast(), b.as_ast()), ctx)


#########################################
#
# Datatypes
#
#########################################

def _valid_accessor(acc):
    """Return `True` if acc is pair of the form (String, Datatype or Sort). """
    return isinstance(acc, tuple) and len(acc) == 2 and isinstance(acc[0], str) and (isinstance(acc[1], Datatype) or is_sort(acc[1]))

class Datatype:
    """Helper class for declaring Z3 datatypes.

    >>> List = Datatype('List')
    >>> List.declare('cons', ('car', IntSort()), ('cdr', List))
    >>> List.declare('nil')
    >>> List = List.create()
    >>> # List is now a Z3 declaration
    >>> List.nil
    nil
    >>> List.cons(10, List.nil)
    cons(10, nil)
    >>> List.cons(10, List.nil).sort()
    List
    >>> cons = List.cons
    >>> nil  = List.nil
    >>> car  = List.car
    >>> cdr  = List.cdr
    >>> n = cons(1, cons(0, nil))
    >>> n
    cons(1, cons(0, nil))
    >>> simplify(cdr(n))
    cons(0, nil)
    >>> simplify(car(n))
    1
    """
    def __init__(self, name, ctx=None):
        self.ctx          = _get_ctx(ctx)
        self.name         = name
        self.constructors = []

    def __deepcopy__(self, memo={}):
        r = Datatype(self.name, self.ctx)
        r.constructors = copy.deepcopy(self.constructors)
        return r

    def declare_core(self, name, rec_name, *args):
        if __debug__:
            _z3_assert(isinstance(name, str), "String expected")
            _z3_assert(isinstance(rec_name, str), "String expected")
            _z3_assert(all([_valid_accessor(a) for a in args]), "Valid list of accessors expected. An accessor is a pair of the form (String, Datatype|Sort)")
        self.constructors.append((name, rec_name, args))

    def declare(self, name, *args):
        """Declare constructor named `name` with the given accessors `args`.
        Each accessor is a pair `(name, sort)`, where `name` is a string and `sort` a Z3 sort or a reference to the datatypes being declared.

        In the following example `List.declare('cons', ('car', IntSort()), ('cdr', List))`
        declares the constructor named `cons` that builds a new List using an integer and a List.
        It also declares the accessors `car` and `cdr`. The accessor `car` extracts the integer of a `cons` cell,
        and `cdr` the list of a `cons` cell. After all constructors were declared, we use the method create() to create
        the actual datatype in Z3.

        >>> List = Datatype('List')
        >>> List.declare('cons', ('car', IntSort()), ('cdr', List))
        >>> List.declare('nil')
        >>> List = List.create()
        """
        if __debug__:
            _z3_assert(isinstance(name, str), "String expected")
            _z3_assert(name != "", "Constructor name cannot be empty")
        return self.declare_core(name, "is-" + name, *args)

    def __repr__(self):
        return "Datatype(%s, %s)" % (self.name, self.constructors)

    def create(self):
        """Create a Z3 datatype based on the constructors declared using the method `declare()`.

        The function `CreateDatatypes()` must be used to define mutually recursive datatypes.

        >>> List = Datatype('List')
        >>> List.declare('cons', ('car', IntSort()), ('cdr', List))
        >>> List.declare('nil')
        >>> List = List.create()
        >>> List.nil
        nil
        >>> List.cons(10, List.nil)
        cons(10, nil)
        """
        return CreateDatatypes([self])[0]

class ScopedConstructor:
    """Auxiliary object used to create Z3 datatypes."""
    def __init__(self, c, ctx):
        self.c   = c
        self.ctx = ctx
    def __del__(self):
        if self.ctx.ref() is not None:
           Z3_del_constructor(self.ctx.ref(), self.c)

class ScopedConstructorList:
    """Auxiliary object used to create Z3 datatypes."""
    def __init__(self, c, ctx):
        self.c   = c
        self.ctx = ctx
    def __del__(self):
        if self.ctx.ref() is not None: 
           Z3_del_constructor_list(self.ctx.ref(), self.c)

def CreateDatatypes(*ds):
    """Create mutually recursive Z3 datatypes using 1 or more Datatype helper objects.

    In the following example we define a Tree-List using two mutually recursive datatypes.

    >>> TreeList = Datatype('TreeList')
    >>> Tree     = Datatype('Tree')
    >>> # Tree has two constructors: leaf and node
    >>> Tree.declare('leaf', ('val', IntSort()))
    >>> # a node contains a list of trees
    >>> Tree.declare('node', ('children', TreeList))
    >>> TreeList.declare('nil')
    >>> TreeList.declare('cons', ('car', Tree), ('cdr', TreeList))
    >>> Tree, TreeList = CreateDatatypes(Tree, TreeList)
    >>> Tree.val(Tree.leaf(10))
    val(leaf(10))
    >>> simplify(Tree.val(Tree.leaf(10)))
    10
    >>> n1 = Tree.node(TreeList.cons(Tree.leaf(10), TreeList.cons(Tree.leaf(20), TreeList.nil)))
    >>> n1
    node(cons(leaf(10), cons(leaf(20), nil)))
    >>> n2 = Tree.node(TreeList.cons(n1, TreeList.nil))
    >>> simplify(n2 == n1)
    False
    >>> simplify(TreeList.car(Tree.children(n2)) == n1)
    True
    """
    ds = _get_args(ds)
    if __debug__:
        _z3_assert(len(ds) > 0, "At least one Datatype must be specified")
        _z3_assert(all([isinstance(d, Datatype) for d in ds]), "Arguments must be Datatypes")
        _z3_assert(all([d.ctx == ds[0].ctx for d in  ds]), "Context mismatch")
        _z3_assert(all([d.constructors != [] for d in ds]), "Non-empty Datatypes expected")
    ctx = ds[0].ctx
    num    = len(ds)
    names  = (Symbol * num)()
    out    = (Sort * num)()
    clists = (ConstructorList * num)()
    to_delete = []
    for i in range(num):
        d        = ds[i]
        names[i] = to_symbol(d.name, ctx)
        num_cs   = len(d.constructors)
        cs       = (Constructor * num_cs)()
        for j in range(num_cs):
            c      = d.constructors[j]
            cname  = to_symbol(c[0], ctx)
            rname  = to_symbol(c[1], ctx)
            fs     = c[2]
            num_fs = len(fs)
            fnames = (Symbol * num_fs)()
            sorts  = (Sort   * num_fs)()
            refs   = (ctypes.c_uint * num_fs)()
            for k in range(num_fs):
                fname = fs[k][0]
                ftype = fs[k][1]
                fnames[k] = to_symbol(fname, ctx)
                if isinstance(ftype, Datatype):
                    if __debug__:
                        _z3_assert(ds.count(ftype) == 1, "One and only one occurrence of each datatype is expected")
                    sorts[k] = None
                    refs[k]  = ds.index(ftype)
                else:
                    if __debug__:
                        _z3_assert(is_sort(ftype), "Z3 sort expected")
                    sorts[k] = ftype.ast
                    refs[k]  = 0
            cs[j] = Z3_mk_constructor(ctx.ref(), cname, rname, num_fs, fnames, sorts, refs)
            to_delete.append(ScopedConstructor(cs[j], ctx))
        clists[i] = Z3_mk_constructor_list(ctx.ref(), num_cs, cs)
        to_delete.append(ScopedConstructorList(clists[i], ctx))
    Z3_mk_datatypes(ctx.ref(), num, names, out, clists)
    result = []
    ## Create a field for every constructor, recognizer and accessor
    for i in range(num):
        dref = DatatypeSortRef(out[i], ctx)
        num_cs = dref.num_constructors()
        for j in range(num_cs):
            cref       = dref.constructor(j)
            cref_name  = cref.name()
            cref_arity = cref.arity()
            if cref.arity() == 0:
                cref = cref()
            setattr(dref, cref_name, cref)
            rref  = dref.recognizer(j)
            setattr(dref, "is_" + cref_name, rref)
            for k in range(cref_arity):
                aref = dref.accessor(j, k)
                setattr(dref, aref.name(), aref)
        result.append(dref)
    return tuple(result)

class DatatypeSortRef(SortRef):
    """Datatype sorts."""
    def num_constructors(self):
        """Return the number of constructors in the given Z3 datatype.

        >>> List = Datatype('List')
        >>> List.declare('cons', ('car', IntSort()), ('cdr', List))
        >>> List.declare('nil')
        >>> List = List.create()
        >>> # List is now a Z3 declaration
        >>> List.num_constructors()
        2
        """
        return int(Z3_get_datatype_sort_num_constructors(self.ctx_ref(), self.ast))

    def constructor(self, idx):
        """Return a constructor of the datatype `self`.

        >>> List = Datatype('List')
        >>> List.declare('cons', ('car', IntSort()), ('cdr', List))
        >>> List.declare('nil')
        >>> List = List.create()
        >>> # List is now a Z3 declaration
        >>> List.num_constructors()
        2
        >>> List.constructor(0)
        cons
        >>> List.constructor(1)
        nil
        """
        if __debug__:
            _z3_assert(idx < self.num_constructors(), "Invalid constructor index")
        return FuncDeclRef(Z3_get_datatype_sort_constructor(self.ctx_ref(), self.ast, idx), self.ctx)

    def recognizer(self, idx):
        """In Z3, each constructor has an associated recognizer predicate.

        If the constructor is named `name`, then the recognizer `is_name`.

        >>> List = Datatype('List')
        >>> List.declare('cons', ('car', IntSort()), ('cdr', List))
        >>> List.declare('nil')
        >>> List = List.create()
        >>> # List is now a Z3 declaration
        >>> List.num_constructors()
        2
        >>> List.recognizer(0)
        is(cons)
        >>> List.recognizer(1)
        is(nil)
        >>> simplify(List.is_nil(List.cons(10, List.nil)))
        False
        >>> simplify(List.is_cons(List.cons(10, List.nil)))
        True
        >>> l = Const('l', List)
        >>> simplify(List.is_cons(l))
        is(cons, l)
        """
        if __debug__:
            _z3_assert(idx < self.num_constructors(), "Invalid recognizer index")
        return FuncDeclRef(Z3_get_datatype_sort_recognizer(self.ctx_ref(), self.ast, idx), self.ctx)

    def accessor(self, i, j):
        """In Z3, each constructor has 0 or more accessor. The number of accessors is equal to the arity of the constructor.

        >>> List = Datatype('List')
        >>> List.declare('cons', ('car', IntSort()), ('cdr', List))
        >>> List.declare('nil')
        >>> List = List.create()
        >>> List.num_constructors()
        2
        >>> List.constructor(0)
        cons
        >>> num_accs = List.constructor(0).arity()
        >>> num_accs
        2
        >>> List.accessor(0, 0)
        car
        >>> List.accessor(0, 1)
        cdr
        >>> List.constructor(1)
        nil
        >>> num_accs = List.constructor(1).arity()
        >>> num_accs
        0
        """
        if __debug__:
            _z3_assert(i < self.num_constructors(), "Invalid constructor index")
            _z3_assert(j < self.constructor(i).arity(), "Invalid accessor index")
        return FuncDeclRef(Z3_get_datatype_sort_constructor_accessor(self.ctx_ref(), self.ast, i, j), self.ctx)

class DatatypeRef(ExprRef):
    """Datatype expressions."""
    def sort(self):
        """Return the datatype sort of the datatype expression `self`."""
        return DatatypeSortRef(Z3_get_sort(self.ctx_ref(), self.as_ast()), self.ctx)

def EnumSort(name, values, ctx=None):
    """Return a new enumeration sort named `name` containing the given values.

    The result is a pair (sort, list of constants).
    Example:
        >>> Color, (red, green, blue) = EnumSort('Color', ['red', 'green', 'blue'])
    """
    if __debug__:
        _z3_assert(isinstance(name, str), "Name must be a string")
        _z3_assert(all([isinstance(v, str) for v in values]), "Eumeration sort values must be strings")
        _z3_assert(len(values) > 0, "At least one value expected")
    ctx = _get_ctx(ctx)
    num = len(values)
    _val_names   = (Symbol * num)()
    for i in range(num):
        _val_names[i] = to_symbol(values[i])
    _values  = (FuncDecl * num)()
    _testers = (FuncDecl * num)()
    name = to_symbol(name)
    S = DatatypeSortRef(Z3_mk_enumeration_sort(ctx.ref(), name, num, _val_names, _values, _testers), ctx)
    V = []
    for i in range(num):
        V.append(FuncDeclRef(_values[i], ctx))
    V = [a() for a in V]
    return S, V

#########################################
#
# Parameter Sets
#
#########################################

class ParamsRef:
    """Set of parameters used to configure Solvers, Tactics and Simplifiers in Z3.

    Consider using the function `args2params` to create instances of this object.
    """
    def __init__(self, ctx=None, params=None):
        self.ctx    = _get_ctx(ctx)
        if params is None:
            self.params = Z3_mk_params(self.ctx.ref())
        else:
            self.params = params
        Z3_params_inc_ref(self.ctx.ref(), self.params)

    def __deepcopy__(self, memo={}):
        return ParamsRef(self.ctx, self.params)

    def __del__(self):
        if self.ctx.ref() is not None:
           Z3_params_dec_ref(self.ctx.ref(), self.params)

    def set(self, name, val):
        """Set parameter name with value val."""
        if __debug__:
            _z3_assert(isinstance(name, str), "parameter name must be a string")
        name_sym = to_symbol(name, self.ctx)
        if isinstance(val, bool):
            Z3_params_set_bool(self.ctx.ref(), self.params, name_sym, val)
        elif _is_int(val):
            Z3_params_set_uint(self.ctx.ref(), self.params, name_sym, val)
        elif isinstance(val, float):
            Z3_params_set_double(self.ctx.ref(), self.params, name_sym, val)
        elif isinstance(val, str):
            Z3_params_set_symbol(self.ctx.ref(), self.params, name_sym, to_symbol(val, self.ctx))
        else:
            if __debug__:
                _z3_assert(False, "invalid parameter value")

    def __repr__(self):
        return Z3_params_to_string(self.ctx.ref(), self.params)

    def validate(self, ds):
        _z3_assert(isinstance(ds, ParamDescrsRef), "parameter description set expected")
        Z3_params_validate(self.ctx.ref(), self.params, ds.descr)

def args2params(arguments, keywords, ctx=None):
    """Convert python arguments into a Z3_params object.
    A ':' is added to the keywords, and '_' is replaced with '-'

    >>> args2params(['model', True, 'relevancy', 2], {'elim_and' : True})
    (params model true relevancy 2 elim_and true)
    """
    if __debug__:
        _z3_assert(len(arguments) % 2 == 0, "Argument list must have an even number of elements.")
    prev = None
    r    = ParamsRef(ctx)
    for a in arguments:
        if prev is None:
            prev = a
        else:
            r.set(prev, a)
            prev = None
    for k in keywords:
        v = keywords[k]
        r.set(k, v)
    return r

class ParamDescrsRef:
    """Set of parameter descriptions for Solvers, Tactics and Simplifiers in Z3.
    """
    def __init__(self, descr, ctx=None):
        _z3_assert(isinstance(descr, ParamDescrs), "parameter description object expected")
        self.ctx    = _get_ctx(ctx)
        self.descr  = descr
        Z3_param_descrs_inc_ref(self.ctx.ref(), self.descr)

    def __deepcopy__(self, memo={}):
        return ParamsDescrsRef(self.descr, self.ctx)

    def __del__(self):
        if self.ctx.ref() is not None:
           Z3_param_descrs_dec_ref(self.ctx.ref(), self.descr)

    def size(self):
        """Return the size of in the parameter description `self`.
        """
        return int(Z3_param_descrs_size(self.ctx.ref(), self.descr))

    def __len__(self):
        """Return the size of in the parameter description `self`.
        """
        return self.size()

    def get_name(self, i):
        """Return the i-th parameter name in the parameter description `self`.
        """
        return _symbol2py(self.ctx, Z3_param_descrs_get_name(self.ctx.ref(), self.descr, i))

    def get_kind(self, n):
        """Return the kind of the parameter named `n`.
        """
        return Z3_param_descrs_get_kind(self.ctx.ref(), self.descr, to_symbol(n, self.ctx))

    def get_documentation(self, n):
        """Return the documentation string of the parameter named `n`.
        """
        return Z3_param_descrs_get_documentation(self.ctx.ref(), self.descr, to_symbol(n, self.ctx))

    def __getitem__(self, arg):
        if _is_int(arg):
            return self.get_name(arg)
        else:
            return self.get_kind(arg)

    def __repr__(self):
        return Z3_param_descrs_to_string(self.ctx.ref(), self.descr)

#########################################
#
# Goals
#
#########################################

class Goal(Z3PPObject):
    """Goal is a collection of constraints we want to find a solution or show to be unsatisfiable (infeasible).

    Goals are processed using Tactics. A Tactic transforms a goal into a set of subgoals.
    A goal has a solution if one of its subgoals has a solution.
    A goal is unsatisfiable if all subgoals are unsatisfiable.
    """

    def __init__(self, models=True, unsat_cores=False, proofs=False, ctx=None, goal=None):
        if __debug__:
            _z3_assert(goal is None or ctx is not None, "If goal is different from None, then ctx must be also different from None")
        self.ctx    = _get_ctx(ctx)
        self.goal   = goal
        if self.goal is None:
            self.goal   = Z3_mk_goal(self.ctx.ref(), models, unsat_cores, proofs)
        Z3_goal_inc_ref(self.ctx.ref(), self.goal)

    def __deepcopy__(self, memo={}):
        return Goal(False, False, False, self.ctx, self.goal)

    def __del__(self):
        if self.goal is not None and self.ctx.ref() is not None:
            Z3_goal_dec_ref(self.ctx.ref(), self.goal)

    def depth(self):
        """Return the depth of the goal `self`. The depth corresponds to the number of tactics applied to `self`.

        >>> x, y = Ints('x y')
        >>> g = Goal()
        >>> g.add(x == 0, y >= x + 1)
        >>> g.depth()
        0
        >>> r = Then('simplify', 'solve-eqs')(g)
        >>> # r has 1 subgoal
        >>> len(r)
        1
        >>> r[0].depth()
        2
        """
        return int(Z3_goal_depth(self.ctx.ref(), self.goal))

    def inconsistent(self):
        """Return `True` if `self` contains the `False` constraints.

        >>> x, y = Ints('x y')
        >>> g = Goal()
        >>> g.inconsistent()
        False
        >>> g.add(x == 0, x == 1)
        >>> g
        [x == 0, x == 1]
        >>> g.inconsistent()
        False
        >>> g2 = Tactic('propagate-values')(g)[0]
        >>> g2.inconsistent()
        True
        """
        return Z3_goal_inconsistent(self.ctx.ref(), self.goal)

    def prec(self):
        """Return the precision (under-approximation, over-approximation, or precise) of the goal `self`.

        >>> g = Goal()
        >>> g.prec() == Z3_GOAL_PRECISE
        True
        >>> x, y = Ints('x y')
        >>> g.add(x == y + 1)
        >>> g.prec() == Z3_GOAL_PRECISE
        True
        >>> t  = With(Tactic('add-bounds'), add_bound_lower=0, add_bound_upper=10)
        >>> g2 = t(g)[0]
        >>> g2
        [x == y + 1, x <= 10, x >= 0, y <= 10, y >= 0]
        >>> g2.prec() == Z3_GOAL_PRECISE
        False
        >>> g2.prec() == Z3_GOAL_UNDER
        True
        """
        return Z3_goal_precision(self.ctx.ref(), self.goal)

    def precision(self):
        """Alias for `prec()`.

        >>> g = Goal()
        >>> g.precision() == Z3_GOAL_PRECISE
        True
        """
        return self.prec()

    def size(self):
        """Return the number of constraints in the goal `self`.

        >>> g = Goal()
        >>> g.size()
        0
        >>> x, y = Ints('x y')
        >>> g.add(x == 0, y > x)
        >>> g.size()
        2
        """
        return int(Z3_goal_size(self.ctx.ref(), self.goal))

    def __len__(self):
        """Return the number of constraints in the goal `self`.

        >>> g = Goal()
        >>> len(g)
        0
        >>> x, y = Ints('x y')
        >>> g.add(x == 0, y > x)
        >>> len(g)
        2
        """
        return self.size()

    def get(self, i):
        """Return a constraint in the goal `self`.

        >>> g = Goal()
        >>> x, y = Ints('x y')
        >>> g.add(x == 0, y > x)
        >>> g.get(0)
        x == 0
        >>> g.get(1)
        y > x
        """
        return _to_expr_ref(Z3_goal_formula(self.ctx.ref(), self.goal, i), self.ctx)

    def __getitem__(self, arg):
        """Return a constraint in the goal `self`.

        >>> g = Goal()
        >>> x, y = Ints('x y')
        >>> g.add(x == 0, y > x)
        >>> g[0]
        x == 0
        >>> g[1]
        y > x
        """
        if arg >= len(self):
            raise IndexError
        return self.get(arg)

    def assert_exprs(self, *args):
        """Assert constraints into the goal.

        >>> x = Int('x')
        >>> g = Goal()
        >>> g.assert_exprs(x > 0, x < 2)
        >>> g
        [x > 0, x < 2]
        """
        args = _get_args(args)
        s    = BoolSort(self.ctx)
        for arg in args:
            arg = s.cast(arg)
            Z3_goal_assert(self.ctx.ref(), self.goal, arg.as_ast())

    def append(self, *args):
        """Add constraints.

        >>> x = Int('x')
        >>> g = Goal()
        >>> g.append(x > 0, x < 2)
        >>> g
        [x > 0, x < 2]
        """
        self.assert_exprs(*args)

    def insert(self, *args):
        """Add constraints.

        >>> x = Int('x')
        >>> g = Goal()
        >>> g.insert(x > 0, x < 2)
        >>> g
        [x > 0, x < 2]
        """
        self.assert_exprs(*args)

    def add(self, *args):
        """Add constraints.

        >>> x = Int('x')
        >>> g = Goal()
        >>> g.add(x > 0, x < 2)
        >>> g
        [x > 0, x < 2]
        """
        self.assert_exprs(*args)

    def convert_model(self, model):
        """Retrieve model from a satisfiable goal
        >>> a, b = Ints('a b')
        >>> g = Goal()
        >>> g.add(Or(a == 0, a == 1), Or(b == 0, b == 1), a > b)
        >>> t = Then(Tactic('split-clause'), Tactic('solve-eqs'))
        >>> r = t(g)
        >>> r[0]
        [Or(b == 0, b == 1), Not(0 <= b)]
        >>> r[1]
        [Or(b == 0, b == 1), Not(1 <= b)]
        >>> # Remark: the subgoal r[0] is unsatisfiable
        >>> # Creating a solver for solving the second subgoal
        >>> s = Solver()
        >>> s.add(r[1])
        >>> s.check()
        sat
        >>> s.model()
        [b = 0]
        >>> # Model s.model() does not assign a value to `a`
        >>> # It is a model for subgoal `r[1]`, but not for goal `g`
        >>> # The method convert_model creates a model for `g` from a model for `r[1]`.
        >>> r[1].convert_model(s.model())
        [b = 0, a = 1]
        """
        if __debug__:
            _z3_assert(isinstance(model, ModelRef), "Z3 Model expected")
        return ModelRef(Z3_goal_convert_model(self.ctx.ref(), self.goal, model.model), self.ctx)

    def __repr__(self):
        return obj_to_string(self)

    def sexpr(self):
        """Return a textual representation of the s-expression representing the goal."""
        return Z3_goal_to_string(self.ctx.ref(), self.goal)

    def dimacs(self):
        """Return a textual representation of the goal in DIMACS format."""
        return Z3_goal_to_dimacs_string(self.ctx.ref(), self.goal)

    def translate(self, target):
        """Copy goal `self` to context `target`.

        >>> x = Int('x')
        >>> g = Goal()
        >>> g.add(x > 10)
        >>> g
        [x > 10]
        >>> c2 = Context()
        >>> g2 = g.translate(c2)
        >>> g2
        [x > 10]
        >>> g.ctx == main_ctx()
        True
        >>> g2.ctx == c2
        True
        >>> g2.ctx == main_ctx()
        False
        """
        if __debug__:
            _z3_assert(isinstance(target, Context), "target must be a context")
        return Goal(goal=Z3_goal_translate(self.ctx.ref(), self.goal, target.ref()), ctx=target)

    def __copy__(self):
        return self.translate(self.ctx)

    def __deepcopy__(self):
        return self.translate(self.ctx)

    def simplify(self, *arguments, **keywords):
        """Return a new simplified goal.

        This method is essentially invoking the simplify tactic.

        >>> g = Goal()
        >>> x = Int('x')
        >>> g.add(x + 1 >= 2)
        >>> g
        [x + 1 >= 2]
        >>> g2 = g.simplify()
        >>> g2
        [x >= 1]
        >>> # g was not modified
        >>> g
        [x + 1 >= 2]
        """
        t = Tactic('simplify')
        return t.apply(self, *arguments, **keywords)[0]

    def as_expr(self):
        """Return goal `self` as a single Z3 expression.

        >>> x = Int('x')
        >>> g = Goal()
        >>> g.as_expr()
        True
        >>> g.add(x > 1)
        >>> g.as_expr()
        x > 1
        >>> g.add(x < 10)
        >>> g.as_expr()
        And(x > 1, x < 10)
        """
        sz = len(self)
        if sz == 0:
            return BoolVal(True, self.ctx)
        elif sz == 1:
            return self.get(0)
        else:
            return And([ self.get(i) for i in range(len(self)) ], self.ctx)

#########################################
#
# AST Vector
#
#########################################
class AstVector(Z3PPObject):
    """A collection (vector) of ASTs."""

    def __init__(self, v=None, ctx=None):
        self.vector = None
        if v is None:
            self.ctx = _get_ctx(ctx)
            self.vector = Z3_mk_ast_vector(self.ctx.ref())
        else:
            self.vector = v
            assert ctx is not None
            self.ctx    = ctx
        Z3_ast_vector_inc_ref(self.ctx.ref(), self.vector)

    def __deepcopy__(self, memo={}):
        return AstVector(self.vector, self.ctx)

    def __del__(self):
        if self.vector is not None and self.ctx.ref() is not None:
            Z3_ast_vector_dec_ref(self.ctx.ref(), self.vector)

    def __len__(self):
        """Return the size of the vector `self`.

        >>> A = AstVector()
        >>> len(A)
        0
        >>> A.push(Int('x'))
        >>> A.push(Int('x'))
        >>> len(A)
        2
        """
        return int(Z3_ast_vector_size(self.ctx.ref(), self.vector))

    def __getitem__(self, i):
        """Return the AST at position `i`.

        >>> A = AstVector()
        >>> A.push(Int('x') + 1)
        >>> A.push(Int('y'))
        >>> A[0]
        x + 1
        >>> A[1]
        y
        """

        if isinstance(i, int):
            if i < 0:
                i += self.__len__()

            if i >= self.__len__():
                raise IndexError
            return _to_ast_ref(Z3_ast_vector_get(self.ctx.ref(), self.vector, i), self.ctx)

        elif isinstance(i, slice):
            return [_to_ast_ref(Z3_ast_vector_get(self.ctx.ref(), self.vector, ii), self.ctx) for ii in range(*i.indices(self.__len__()))]


    def __setitem__(self, i, v):
        """Update AST at position `i`.

        >>> A = AstVector()
        >>> A.push(Int('x') + 1)
        >>> A.push(Int('y'))
        >>> A[0]
        x + 1
        >>> A[0] = Int('x')
        >>> A[0]
        x
        """
        if i >= self.__len__():
            raise IndexError
        Z3_ast_vector_set(self.ctx.ref(), self.vector, i, v.as_ast())

    def push(self, v):
        """Add `v` in the end of the vector.

        >>> A = AstVector()
        >>> len(A)
        0
        >>> A.push(Int('x'))
        >>> len(A)
        1
        """
        Z3_ast_vector_push(self.ctx.ref(), self.vector, v.as_ast())

    def resize(self, sz):
        """Resize the vector to `sz` elements.

        >>> A = AstVector()
        >>> A.resize(10)
        >>> len(A)
        10
        >>> for i in range(10): A[i] = Int('x')
        >>> A[5]
        x
        """
        Z3_ast_vector_resize(self.ctx.ref(), self.vector, sz)

    def __contains__(self, item):
        """Return `True` if the vector contains `item`.

        >>> x = Int('x')
        >>> A = AstVector()
        >>> x in A
        False
        >>> A.push(x)
        >>> x in A
        True
        >>> (x+1) in A
        False
        >>> A.push(x+1)
        >>> (x+1) in A
        True
        >>> A
        [x, x + 1]
        """
        for elem in self:
            if elem.eq(item):
                return True
        return False

    def translate(self, other_ctx):
        """Copy vector `self` to context `other_ctx`.

        >>> x = Int('x')
        >>> A = AstVector()
        >>> A.push(x)
        >>> c2 = Context()
        >>> B = A.translate(c2)
        >>> B
        [x]
        """
        return AstVector(Z3_ast_vector_translate(self.ctx.ref(), self.vector, other_ctx.ref()), other_ctx)

    def __copy__(self):
        return self.translate(self.ctx)

    def __deepcopy__(self):
        return self.translate(self.ctx)

    def __repr__(self):
        return obj_to_string(self)

    def sexpr(self):
        """Return a textual representation of the s-expression representing the vector."""
        return Z3_ast_vector_to_string(self.ctx.ref(), self.vector)

#########################################
#
# AST Map
#
#########################################
class AstMap:
    """A mapping from ASTs to ASTs."""

    def __init__(self, m=None, ctx=None):
        self.map = None
        if m is None:
            self.ctx = _get_ctx(ctx)
            self.map = Z3_mk_ast_map(self.ctx.ref())
        else:
            self.map = m
            assert ctx is not None
            self.ctx    = ctx
        Z3_ast_map_inc_ref(self.ctx.ref(), self.map)

    def __deepcopy__(self, memo={}):
        return AstMap(self.map, self.ctx)

    def __del__(self):
        if self.map is not None and self.ctx.ref() is not None:
            Z3_ast_map_dec_ref(self.ctx.ref(), self.map)

    def __len__(self):
        """Return the size of the map.

        >>> M = AstMap()
        >>> len(M)
        0
        >>> x = Int('x')
        >>> M[x] = IntVal(1)
        >>> len(M)
        1
        """
        return int(Z3_ast_map_size(self.ctx.ref(), self.map))

    def __contains__(self, key):
        """Return `True` if the map contains key `key`.

        >>> M = AstMap()
        >>> x = Int('x')
        >>> M[x] = x + 1
        >>> x in M
        True
        >>> x+1 in M
        False
        """
        return Z3_ast_map_contains(self.ctx.ref(), self.map, key.as_ast())

    def __getitem__(self, key):
        """Retrieve the value associated with key `key`.

        >>> M = AstMap()
        >>> x = Int('x')
        >>> M[x] = x + 1
        >>> M[x]
        x + 1
        """
        return _to_ast_ref(Z3_ast_map_find(self.ctx.ref(), self.map, key.as_ast()), self.ctx)

    def __setitem__(self, k, v):
        """Add/Update key `k` with value `v`.

        >>> M = AstMap()
        >>> x = Int('x')
        >>> M[x] = x + 1
        >>> len(M)
        1
        >>> M[x]
        x + 1
        >>> M[x] = IntVal(1)
        >>> M[x]
        1
        """
        Z3_ast_map_insert(self.ctx.ref(), self.map, k.as_ast(), v.as_ast())

    def __repr__(self):
        return Z3_ast_map_to_string(self.ctx.ref(), self.map)

    def erase(self, k):
        """Remove the entry associated with key `k`.

        >>> M = AstMap()
        >>> x = Int('x')
        >>> M[x] = x + 1
        >>> len(M)
        1
        >>> M.erase(x)
        >>> len(M)
        0
        """
        Z3_ast_map_erase(self.ctx.ref(), self.map, k.as_ast())

    def reset(self):
        """Remove all entries from the map.

        >>> M = AstMap()
        >>> x = Int('x')
        >>> M[x]   = x + 1
        >>> M[x+x] = IntVal(1)
        >>> len(M)
        2
        >>> M.reset()
        >>> len(M)
        0
        """
        Z3_ast_map_reset(self.ctx.ref(), self.map)

    def keys(self):
        """Return an AstVector containing all keys in the map.

        >>> M = AstMap()
        >>> x = Int('x')
        >>> M[x]   = x + 1
        >>> M[x+x] = IntVal(1)
        >>> M.keys()
        [x, x + x]
        """
        return AstVector(Z3_ast_map_keys(self.ctx.ref(), self.map), self.ctx)

#########################################
#
# Model
#
#########################################

class FuncEntry:
    """Store the value of the interpretation of a function in a particular point."""

    def __init__(self, entry, ctx):
        self.entry = entry
        self.ctx   = ctx
        Z3_func_entry_inc_ref(self.ctx.ref(), self.entry)

    def __deepcopy__(self, memo={}):
        return FuncEntry(self.entry, self.ctx)

    def __del__(self):
        if self.ctx.ref() is not None:
           Z3_func_entry_dec_ref(self.ctx.ref(), self.entry)

    def num_args(self):
        """Return the number of arguments in the given entry.

        >>> f = Function('f', IntSort(), IntSort(), IntSort())
        >>> s = Solver()
        >>> s.add(f(0, 1) == 10, f(1, 2) == 20, f(1, 0) == 10)
        >>> s.check()
        sat
        >>> m = s.model()
        >>> f_i = m[f]
        >>> f_i.num_entries()
        1
        >>> e = f_i.entry(0)
        >>> e.num_args()
        2
        """
        return int(Z3_func_entry_get_num_args(self.ctx.ref(), self.entry))

    def arg_value(self, idx):
        """Return the value of argument `idx`.

        >>> f = Function('f', IntSort(), IntSort(), IntSort())
        >>> s = Solver()
        >>> s.add(f(0, 1) == 10, f(1, 2) == 20, f(1, 0) == 10)
        >>> s.check()
        sat
        >>> m = s.model()
        >>> f_i = m[f]
        >>> f_i.num_entries()
        1
        >>> e = f_i.entry(0)
        >>> e
        [1, 2, 20]
        >>> e.num_args()
        2
        >>> e.arg_value(0)
        1
        >>> e.arg_value(1)
        2
        >>> try:
        ...   e.arg_value(2)
        ... except IndexError:
        ...   print("index error")
        index error
        """
        if idx >= self.num_args():
            raise IndexError
        return _to_expr_ref(Z3_func_entry_get_arg(self.ctx.ref(), self.entry, idx), self.ctx)

    def value(self):
        """Return the value of the function at point `self`.

        >>> f = Function('f', IntSort(), IntSort(), IntSort())
        >>> s = Solver()
        >>> s.add(f(0, 1) == 10, f(1, 2) == 20, f(1, 0) == 10)
        >>> s.check()
        sat
        >>> m = s.model()
        >>> f_i = m[f]
        >>> f_i.num_entries()
        1
        >>> e = f_i.entry(0)
        >>> e
        [1, 2, 20]
        >>> e.num_args()
        2
        >>> e.value()
        20
        """
        return _to_expr_ref(Z3_func_entry_get_value(self.ctx.ref(), self.entry), self.ctx)

    def as_list(self):
        """Return entry `self` as a Python list.
        >>> f = Function('f', IntSort(), IntSort(), IntSort())
        >>> s = Solver()
        >>> s.add(f(0, 1) == 10, f(1, 2) == 20, f(1, 0) == 10)
        >>> s.check()
        sat
        >>> m = s.model()
        >>> f_i = m[f]
        >>> f_i.num_entries()
        1
        >>> e = f_i.entry(0)
        >>> e.as_list()
        [1, 2, 20]
        """
        args = [ self.arg_value(i) for i in range(self.num_args())]
        args.append(self.value())
        return args

    def __repr__(self):
        return repr(self.as_list())

class FuncInterp(Z3PPObject):
    """Stores the interpretation of a function in a Z3 model."""

    def __init__(self, f, ctx):
        self.f   = f
        self.ctx = ctx
        if self.f is not None:
            Z3_func_interp_inc_ref(self.ctx.ref(), self.f)

    def __deepcopy__(self, memo={}):
        return FuncInterp(self.f, self.ctx)

    def __del__(self):
        if self.f is not None and self.ctx.ref() is not None:
            Z3_func_interp_dec_ref(self.ctx.ref(), self.f)

    def else_value(self):
        """
        Return the `else` value for a function interpretation.
        Return None if Z3 did not specify the `else` value for
        this object.

        >>> f = Function('f', IntSort(), IntSort())
        >>> s = Solver()
        >>> s.add(f(0) == 1, f(1) == 1, f(2) == 0)
        >>> s.check()
        sat
        >>> m = s.model()
        >>> m[f]
        [2 -> 0, else -> 1]
        >>> m[f].else_value()
        1
        """
        r = Z3_func_interp_get_else(self.ctx.ref(), self.f)
        if r:
            return _to_expr_ref(r, self.ctx)
        else:
            return None

    def num_entries(self):
        """Return the number of entries/points in the function interpretation `self`.

        >>> f = Function('f', IntSort(), IntSort())
        >>> s = Solver()
        >>> s.add(f(0) == 1, f(1) == 1, f(2) == 0)
        >>> s.check()
        sat
        >>> m = s.model()
        >>> m[f]
        [2 -> 0, else -> 1]
        >>> m[f].num_entries()
        1
        """
        return int(Z3_func_interp_get_num_entries(self.ctx.ref(), self.f))

    def arity(self):
        """Return the number of arguments for each entry in the function interpretation `self`.

        >>> f = Function('f', IntSort(), IntSort())
        >>> s = Solver()
        >>> s.add(f(0) == 1, f(1) == 1, f(2) == 0)
        >>> s.check()
        sat
        >>> m = s.model()
        >>> m[f].arity()
        1
        """
        return int(Z3_func_interp_get_arity(self.ctx.ref(), self.f))

    def entry(self, idx):
        """Return an entry at position `idx < self.num_entries()` in the function interpretation `self`.

        >>> f = Function('f', IntSort(), IntSort())
        >>> s = Solver()
        >>> s.add(f(0) == 1, f(1) == 1, f(2) == 0)
        >>> s.check()
        sat
        >>> m = s.model()
        >>> m[f]
        [2 -> 0, else -> 1]
        >>> m[f].num_entries()
        1
        >>> m[f].entry(0)
        [2, 0]
        """
        if idx >= self.num_entries():
            raise IndexError
        return FuncEntry(Z3_func_interp_get_entry(self.ctx.ref(), self.f, idx), self.ctx)

    def translate(self, other_ctx):
        """Copy model 'self' to context 'other_ctx'.
        """
        return ModelRef(Z3_model_translate(self.ctx.ref(), self.model, other_ctx.ref()), other_ctx)

    def __copy__(self):
        return self.translate(self.ctx)

    def __deepcopy__(self):
        return self.translate(self.ctx)

    def as_list(self):
        """Return the function interpretation as a Python list.
        >>> f = Function('f', IntSort(), IntSort())
        >>> s = Solver()
        >>> s.add(f(0) == 1, f(1) == 1, f(2) == 0)
        >>> s.check()
        sat
        >>> m = s.model()
        >>> m[f]
        [2 -> 0, else -> 1]
        >>> m[f].as_list()
        [[2, 0], 1]
        """
        r = [ self.entry(i).as_list() for i in range(self.num_entries())]
        r.append(self.else_value())
        return r

    def __repr__(self):
        return obj_to_string(self)

class ModelRef(Z3PPObject):
    """Model/Solution of a satisfiability problem (aka system of constraints)."""

    def __init__(self, m, ctx):
        assert ctx is not None
        self.model = m
        self.ctx   = ctx
        Z3_model_inc_ref(self.ctx.ref(), self.model)

    def __del__(self):
        if self.ctx.ref() is not None:
           Z3_model_dec_ref(self.ctx.ref(), self.model)

    def __repr__(self):
        return obj_to_string(self)

    def sexpr(self):
        """Return a textual representation of the s-expression representing the model."""
        return Z3_model_to_string(self.ctx.ref(), self.model)

    def eval(self, t, model_completion=False):
        """Evaluate the expression `t` in the model `self`. If `model_completion` is enabled, then a default interpretation is automatically added for symbols that do not have an interpretation in the model `self`.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0, x < 2)
        >>> s.check()
        sat
        >>> m = s.model()
        >>> m.eval(x + 1)
        2
        >>> m.eval(x == 1)
        True
        >>> y = Int('y')
        >>> m.eval(y + x)
        1 + y
        >>> m.eval(y)
        y
        >>> m.eval(y, model_completion=True)
        0
        >>> # Now, m contains an interpretation for y
        >>> m.eval(y + x)
        1
        """
        r = (Ast * 1)()
        if Z3_model_eval(self.ctx.ref(), self.model, t.as_ast(), model_completion, r):
            return _to_expr_ref(r[0], self.ctx)
        raise Z3Exception("failed to evaluate expression in the model")

    def evaluate(self, t, model_completion=False):
        """Alias for `eval`.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0, x < 2)
        >>> s.check()
        sat
        >>> m = s.model()
        >>> m.evaluate(x + 1)
        2
        >>> m.evaluate(x == 1)
        True
        >>> y = Int('y')
        >>> m.evaluate(y + x)
        1 + y
        >>> m.evaluate(y)
        y
        >>> m.evaluate(y, model_completion=True)
        0
        >>> # Now, m contains an interpretation for y
        >>> m.evaluate(y + x)
        1
        """
        return self.eval(t, model_completion)

    def __len__(self):
        """Return the number of constant and function declarations in the model `self`.

        >>> f = Function('f', IntSort(), IntSort())
        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0, f(x) != x)
        >>> s.check()
        sat
        >>> m = s.model()
        >>> len(m)
        2
        """
        return int(Z3_model_get_num_consts(self.ctx.ref(), self.model)) + int(Z3_model_get_num_funcs(self.ctx.ref(), self.model))

    def get_interp(self, decl):
        """Return the interpretation for a given declaration or constant.

        >>> f = Function('f', IntSort(), IntSort())
        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0, x < 2, f(x) == 0)
        >>> s.check()
        sat
        >>> m = s.model()
        >>> m[x]
        1
        >>> m[f]
        [else -> 0]
        """
        if __debug__:
            _z3_assert(isinstance(decl, FuncDeclRef) or is_const(decl), "Z3 declaration expected")
        if is_const(decl):
            decl = decl.decl()
        try:
            if decl.arity() == 0:
                _r = Z3_model_get_const_interp(self.ctx.ref(), self.model, decl.ast)
                if _r.value is None:
                    return None
                r = _to_expr_ref(_r, self.ctx)
                if is_as_array(r):
                    return self.get_interp(get_as_array_func(r))
                else:
                    return r
            else:
                return FuncInterp(Z3_model_get_func_interp(self.ctx.ref(), self.model, decl.ast), self.ctx)
        except Z3Exception:
            return None

    def num_sorts(self):
        """Return the number of uninterpreted sorts that contain an interpretation in the model `self`.

        >>> A = DeclareSort('A')
        >>> a, b = Consts('a b', A)
        >>> s = Solver()
        >>> s.add(a != b)
        >>> s.check()
        sat
        >>> m = s.model()
        >>> m.num_sorts()
        1
        """
        return int(Z3_model_get_num_sorts(self.ctx.ref(), self.model))

    def get_sort(self, idx):
        """Return the uninterpreted sort at position `idx` < self.num_sorts().

        >>> A = DeclareSort('A')
        >>> B = DeclareSort('B')
        >>> a1, a2 = Consts('a1 a2', A)
        >>> b1, b2 = Consts('b1 b2', B)
        >>> s = Solver()
        >>> s.add(a1 != a2, b1 != b2)
        >>> s.check()
        sat
        >>> m = s.model()
        >>> m.num_sorts()
        2
        >>> m.get_sort(0)
        A
        >>> m.get_sort(1)
        B
        """
        if idx >= self.num_sorts():
            raise IndexError
        return _to_sort_ref(Z3_model_get_sort(self.ctx.ref(), self.model, idx), self.ctx)

    def sorts(self):
        """Return all uninterpreted sorts that have an interpretation in the model `self`.

        >>> A = DeclareSort('A')
        >>> B = DeclareSort('B')
        >>> a1, a2 = Consts('a1 a2', A)
        >>> b1, b2 = Consts('b1 b2', B)
        >>> s = Solver()
        >>> s.add(a1 != a2, b1 != b2)
        >>> s.check()
        sat
        >>> m = s.model()
        >>> m.sorts()
        [A, B]
        """
        return [ self.get_sort(i) for i in range(self.num_sorts()) ]

    def get_universe(self, s):
        """Return the interpretation for the uninterpreted sort `s` in the model `self`.

        >>> A = DeclareSort('A')
        >>> a, b = Consts('a b', A)
        >>> s = Solver()
        >>> s.add(a != b)
        >>> s.check()
        sat
        >>> m = s.model()
        >>> m.get_universe(A)
        [A!val!0, A!val!1]
        """
        if __debug__:
            _z3_assert(isinstance(s, SortRef), "Z3 sort expected")
        try:
            return AstVector(Z3_model_get_sort_universe(self.ctx.ref(), self.model, s.ast), self.ctx)
        except Z3Exception:
            return None

    def __getitem__(self, idx):
        """If `idx` is an integer, then the declaration at position `idx` in the model `self` is returned. If `idx` is a declaration, then the actual interpretation is returned.

        The elements can be retrieved using position or the actual declaration.

        >>> f = Function('f', IntSort(), IntSort())
        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0, x < 2, f(x) == 0)
        >>> s.check()
        sat
        >>> m = s.model()
        >>> len(m)
        2
        >>> m[0]
        x
        >>> m[1]
        f
        >>> m[x]
        1
        >>> m[f]
        [else -> 0]
        >>> for d in m: print("%s -> %s" % (d, m[d]))
        x -> 1
        f -> [else -> 0]
        """
        if _is_int(idx):
            if idx >= len(self):
                raise IndexError
            num_consts = Z3_model_get_num_consts(self.ctx.ref(), self.model)
            if (idx < num_consts):
                return FuncDeclRef(Z3_model_get_const_decl(self.ctx.ref(), self.model, idx), self.ctx)
            else:
                return FuncDeclRef(Z3_model_get_func_decl(self.ctx.ref(), self.model, idx - num_consts), self.ctx)
        if isinstance(idx, FuncDeclRef):
            return self.get_interp(idx)
        if is_const(idx):
            return self.get_interp(idx.decl())
        if isinstance(idx, SortRef):
            return self.get_universe(idx)
        if __debug__:
            _z3_assert(False, "Integer, Z3 declaration, or Z3 constant expected")
        return None

    def decls(self):
        """Return a list with all symbols that have an interpretation in the model `self`.
        >>> f = Function('f', IntSort(), IntSort())
        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0, x < 2, f(x) == 0)
        >>> s.check()
        sat
        >>> m = s.model()
        >>> m.decls()
        [x, f]
        """
        r = []
        for i in range(Z3_model_get_num_consts(self.ctx.ref(), self.model)):
            r.append(FuncDeclRef(Z3_model_get_const_decl(self.ctx.ref(), self.model, i), self.ctx))
        for i in range(Z3_model_get_num_funcs(self.ctx.ref(), self.model)):
            r.append(FuncDeclRef(Z3_model_get_func_decl(self.ctx.ref(), self.model, i), self.ctx))
        return r

    def translate(self, target):
        """Translate `self` to the context `target`. That is, return a copy of `self` in the context `target`.
        """
        if __debug__:
            _z3_assert(isinstance(target, Context), "argument must be a Z3 context")
        model = Z3_model_translate(self.ctx.ref(), self.model, target.ref())
        return Model(model, target)

    def __copy__(self):
        return self.translate(self.ctx)

    def __deepcopy__(self):
        return self.translate(self.ctx)

def is_as_array(n):
    """Return true if n is a Z3 expression of the form (_ as-array f)."""
    return isinstance(n, ExprRef) and Z3_is_as_array(n.ctx.ref(), n.as_ast())

def get_as_array_func(n):
    """Return the function declaration f associated with a Z3 expression of the form (_ as-array f)."""
    if __debug__:
        _z3_assert(is_as_array(n), "as-array Z3 expression expected.")
    return FuncDeclRef(Z3_get_as_array_func_decl(n.ctx.ref(), n.as_ast()), n.ctx)

#########################################
#
# Statistics
#
#########################################
class Statistics:
    """Statistics for `Solver.check()`."""

    def __init__(self, stats, ctx):
        self.stats = stats
        self.ctx   = ctx
        Z3_stats_inc_ref(self.ctx.ref(), self.stats)

    def __deepcopy__(self, memo={}):
        return Statistics(self.stats, self.ctx)

    def __del__(self):
        if self.ctx.ref() is not None:
           Z3_stats_dec_ref(self.ctx.ref(), self.stats)

    def __repr__(self):
        if in_html_mode():
            out = io.StringIO()
            even = True
            out.write(u('<table border="1" cellpadding="2" cellspacing="0">'))
            for k, v in self:
                if even:
                    out.write(u('<tr style="background-color:#CFCFCF">'))
                    even = False
                else:
                    out.write(u('<tr>'))
                    even = True
                out.write(u('<td>%s</td><td>%s</td></tr>' % (k, v)))
            out.write(u('</table>'))
            return out.getvalue()
        else:
            return Z3_stats_to_string(self.ctx.ref(), self.stats)

    def __len__(self):
        """Return the number of statistical counters.

        >>> x = Int('x')
        >>> s = Then('simplify', 'nlsat').solver()
        >>> s.add(x > 0)
        >>> s.check()
        sat
        >>> st = s.statistics()
        >>> len(st)
        6
        """
        return int(Z3_stats_size(self.ctx.ref(), self.stats))

    def __getitem__(self, idx):
        """Return the value of statistical counter at position `idx`. The result is a pair (key, value).

        >>> x = Int('x')
        >>> s = Then('simplify', 'nlsat').solver()
        >>> s.add(x > 0)
        >>> s.check()
        sat
        >>> st = s.statistics()
        >>> len(st)
        6
        >>> st[0]
        ('nlsat propagations', 2)
        >>> st[1]
        ('nlsat stages', 2)
        """
        if idx >= len(self):
            raise IndexError
        if Z3_stats_is_uint(self.ctx.ref(), self.stats, idx):
            val = int(Z3_stats_get_uint_value(self.ctx.ref(), self.stats, idx))
        else:
            val = Z3_stats_get_double_value(self.ctx.ref(), self.stats, idx)
        return (Z3_stats_get_key(self.ctx.ref(), self.stats, idx), val)

    def keys(self):
        """Return the list of statistical counters.

        >>> x = Int('x')
        >>> s = Then('simplify', 'nlsat').solver()
        >>> s.add(x > 0)
        >>> s.check()
        sat
        >>> st = s.statistics()
        """
        return [Z3_stats_get_key(self.ctx.ref(), self.stats, idx) for idx in range(len(self))]

    def get_key_value(self, key):
        """Return the value of a particular statistical counter.

        >>> x = Int('x')
        >>> s = Then('simplify', 'nlsat').solver()
        >>> s.add(x > 0)
        >>> s.check()
        sat
        >>> st = s.statistics()
        >>> st.get_key_value('nlsat propagations')
        2
        """
        for idx in range(len(self)):
            if key == Z3_stats_get_key(self.ctx.ref(), self.stats, idx):
                if Z3_stats_is_uint(self.ctx.ref(), self.stats, idx):
                    return int(Z3_stats_get_uint_value(self.ctx.ref(), self.stats, idx))
                else:
                    return Z3_stats_get_double_value(self.ctx.ref(), self.stats, idx)
        raise Z3Exception("unknown key")

    def __getattr__(self, name):
        """Access the value of statistical using attributes.

        Remark: to access a counter containing blank spaces (e.g., 'nlsat propagations'),
        we should use '_' (e.g., 'nlsat_propagations').

        >>> x = Int('x')
        >>> s = Then('simplify', 'nlsat').solver()
        >>> s.add(x > 0)
        >>> s.check()
        sat
        >>> st = s.statistics()
        >>> st.nlsat_propagations
        2
        >>> st.nlsat_stages
        2
        """
        key = name.replace('_', ' ')
        try:
            return self.get_key_value(key)
        except Z3Exception:
            raise AttributeError

#########################################
#
# Solver
#
#########################################
class CheckSatResult:
    """Represents the result of a satisfiability check: sat, unsat, unknown.

    >>> s = Solver()
    >>> s.check()
    sat
    >>> r = s.check()
    >>> isinstance(r, CheckSatResult)
    True
    """

    def __init__(self, r):
        self.r = r

    def __deepcopy__(self, memo={}):
        return CheckSatResult(self.r)

    def __eq__(self, other):
        return isinstance(other, CheckSatResult) and self.r == other.r

    def __ne__(self, other):
        return not self.__eq__(other)

    def __repr__(self):
        if in_html_mode():
            if self.r == Z3_L_TRUE:
                return "<b>sat</b>"
            elif self.r == Z3_L_FALSE:
                return "<b>unsat</b>"
            else:
                return "<b>unknown</b>"
        else:
            if self.r == Z3_L_TRUE:
                return "sat"
            elif self.r == Z3_L_FALSE:
                return "unsat"
            else:
                return "unknown"

sat     = CheckSatResult(Z3_L_TRUE)
unsat   = CheckSatResult(Z3_L_FALSE)
unknown = CheckSatResult(Z3_L_UNDEF)

class Solver(Z3PPObject):
    """Solver API provides methods for implementing the main SMT 2.0 commands: push, pop, check, get-model, etc."""

    def __init__(self, solver=None, ctx=None):
        assert solver is None or ctx is not None
        self.ctx    = _get_ctx(ctx)
        self.backtrack_level = 4000000000
        self.solver = None
        if solver is None:
            self.solver = Z3_mk_solver(self.ctx.ref())
        else:
            self.solver = solver
        Z3_solver_inc_ref(self.ctx.ref(), self.solver)

    def __del__(self):
        if self.solver is not None and self.ctx.ref() is not None:
            Z3_solver_dec_ref(self.ctx.ref(), self.solver)

    def set(self, *args, **keys):
        """Set a configuration option. The method `help()` return a string containing all available options.

        >>> s = Solver()
        >>> # The option MBQI can be set using three different approaches.
        >>> s.set(mbqi=True)
        >>> s.set('MBQI', True)
        >>> s.set(':mbqi', True)
        """
        p = args2params(args, keys, self.ctx)
        Z3_solver_set_params(self.ctx.ref(), self.solver, p.params)

    def push(self):
        """Create a backtracking point.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0)
        >>> s
        [x > 0]
        >>> s.push()
        >>> s.add(x < 1)
        >>> s
        [x > 0, x < 1]
        >>> s.check()
        unsat
        >>> s.pop()
        >>> s.check()
        sat
        >>> s
        [x > 0]
        """
        Z3_solver_push(self.ctx.ref(), self.solver)

    def pop(self, num=1):
        """Backtrack \c num backtracking points.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0)
        >>> s
        [x > 0]
        >>> s.push()
        >>> s.add(x < 1)
        >>> s
        [x > 0, x < 1]
        >>> s.check()
        unsat
        >>> s.pop()
        >>> s.check()
        sat
        >>> s
        [x > 0]
        """
        Z3_solver_pop(self.ctx.ref(), self.solver, num)

    def num_scopes(self):
        """Return the current number of backtracking points.

        >>> s = Solver()
        >>> s.num_scopes()
        0L
        >>> s.push()
        >>> s.num_scopes()
        1L
        >>> s.push()
        >>> s.num_scopes()
        2L
        >>> s.pop()
        >>> s.num_scopes()
        1L
        """
        return Z3_solver_get_num_scopes(self.ctx.ref(), self.solver)

    def reset(self):
        """Remove all asserted constraints and backtracking points created using `push()`.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0)
        >>> s
        [x > 0]
        >>> s.reset()
        >>> s
        []
        """
        Z3_solver_reset(self.ctx.ref(), self.solver)

    def assert_exprs(self, *args):
        """Assert constraints into the solver.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.assert_exprs(x > 0, x < 2)
        >>> s
        [x > 0, x < 2]
        """
        args = _get_args(args)
        s    = BoolSort(self.ctx)
        for arg in args:
            if isinstance(arg, Goal) or isinstance(arg, AstVector):
                for f in arg:
                    Z3_solver_assert(self.ctx.ref(), self.solver, f.as_ast())
            else:
                arg = s.cast(arg)
                Z3_solver_assert(self.ctx.ref(), self.solver, arg.as_ast())

    def add(self, *args):
        """Assert constraints into the solver.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0, x < 2)
        >>> s
        [x > 0, x < 2]
        """
        self.assert_exprs(*args)

    def __iadd__(self, fml):
        self.add(fml)
        return self

    def append(self, *args):
        """Assert constraints into the solver.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.append(x > 0, x < 2)
        >>> s
        [x > 0, x < 2]
        """
        self.assert_exprs(*args)

    def insert(self, *args):
        """Assert constraints into the solver.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.insert(x > 0, x < 2)
        >>> s
        [x > 0, x < 2]
        """
        self.assert_exprs(*args)

    def assert_and_track(self, a, p):
        """Assert constraint `a` and track it in the unsat core using the Boolean constant `p`.

        If `p` is a string, it will be automatically converted into a Boolean constant.

        >>> x = Int('x')
        >>> p3 = Bool('p3')
        >>> s = Solver()
        >>> s.set(unsat_core=True)
        >>> s.assert_and_track(x > 0,  'p1')
        >>> s.assert_and_track(x != 1, 'p2')
        >>> s.assert_and_track(x < 0,  p3)
        >>> print(s.check())
        unsat
        >>> c = s.unsat_core()
        >>> len(c)
        2
        >>> Bool('p1') in c
        True
        >>> Bool('p2') in c
        False
        >>> p3 in c
        True
        """
        if isinstance(p, str):
            p = Bool(p, self.ctx)
        _z3_assert(isinstance(a, BoolRef), "Boolean expression expected")
        _z3_assert(isinstance(p, BoolRef) and is_const(p), "Boolean expression expected")
        Z3_solver_assert_and_track(self.ctx.ref(), self.solver, a.as_ast(), p.as_ast())

    def check(self, *assumptions):
        """Check whether the assertions in the given solver plus the optional assumptions are consistent or not.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.check()
        sat
        >>> s.add(x > 0, x < 2)
        >>> s.check()
        sat
        >>> s.model()
        [x = 1]
        >>> s.add(x < 1)
        >>> s.check()
        unsat
        >>> s.reset()
        >>> s.add(2**x == 4)
        >>> s.check()
        unknown
        """
        assumptions = _get_args(assumptions)
        num = len(assumptions)
        _assumptions = (Ast * num)()
        for i in range(num):
            _assumptions[i] = assumptions[i].as_ast()
        r = Z3_solver_check_assumptions(self.ctx.ref(), self.solver, num, _assumptions)
        return CheckSatResult(r)

    def model(self):
        """Return a model for the last `check()`.

        This function raises an exception if
        a model is not available (e.g., last `check()` returned unsat).

        >>> s = Solver()
        >>> a = Int('a')
        >>> s.add(a + 2 == 0)
        >>> s.check()
        sat
        >>> s.model()
        [a = -2]
        """
        try:
            return ModelRef(Z3_solver_get_model(self.ctx.ref(), self.solver), self.ctx)
        except Z3Exception:
            raise Z3Exception("model is not available")

    def unsat_core(self):
        """Return a subset (as an AST vector) of the assumptions provided to the last check().

        These are the assumptions Z3 used in the unsatisfiability proof.
        Assumptions are available in Z3. They are used to extract unsatisfiable cores.
        They may be also used to "retract" assumptions. Note that, assumptions are not really
        "soft constraints", but they can be used to implement them.

        >>> p1, p2, p3 = Bools('p1 p2 p3')
        >>> x, y       = Ints('x y')
        >>> s          = Solver()
        >>> s.add(Implies(p1, x > 0))
        >>> s.add(Implies(p2, y > x))
        >>> s.add(Implies(p2, y < 1))
        >>> s.add(Implies(p3, y > -3))
        >>> s.check(p1, p2, p3)
        unsat
        >>> core = s.unsat_core()
        >>> len(core)
        2
        >>> p1 in core
        True
        >>> p2 in core
        True
        >>> p3 in core
        False
        >>> # "Retracting" p2
        >>> s.check(p1, p3)
        sat
        """
        return AstVector(Z3_solver_get_unsat_core(self.ctx.ref(), self.solver), self.ctx)

    def consequences(self, assumptions, variables):
        """Determine fixed values for the variables based on the solver state and assumptions.        
        >>> s = Solver()
        >>> a, b, c, d = Bools('a b c d')
        >>> s.add(Implies(a,b), Implies(b, c))
        >>> s.consequences([a],[b,c,d])
        (sat, [Implies(a, b), Implies(a, c)])
        >>> s.consequences([Not(c),d],[a,b,c,d])
        (sat, [Implies(d, d), Implies(Not(c), Not(c)), Implies(Not(c), Not(b)), Implies(Not(c), Not(a))])
        """
        if isinstance(assumptions, list):
            _asms = AstVector(None, self.ctx)
            for a in assumptions:
                _asms.push(a)
            assumptions = _asms
        if isinstance(variables, list):
            _vars = AstVector(None, self.ctx)
            for a in variables:
                _vars.push(a)
            variables = _vars            
        _z3_assert(isinstance(assumptions, AstVector), "ast vector expected")
        _z3_assert(isinstance(variables, AstVector), "ast vector expected")
        consequences = AstVector(None, self.ctx)
        r = Z3_solver_get_consequences(self.ctx.ref(), self.solver, assumptions.vector, variables.vector, consequences.vector)
        sz = len(consequences)
        consequences = [ consequences[i] for i in range(sz) ]
        return CheckSatResult(r), consequences

    def from_file(self, filename):
        """Parse assertions from a file"""
        try:
            Z3_solver_from_file(self.ctx.ref(), self.solver, filename)
        except Z3Exception as e:
            _handle_parse_error(e, self.ctx)

    def from_string(self, s):
        """Parse assertions from a string"""
        try:
           Z3_solver_from_string(self.ctx.ref(), self.solver, s)
        except Z3Exception as e:
            _handle_parse_error(e, self.ctx)        
    
    def cube(self, vars = None):
        """Get set of cubes"""
        self.cube_vs = AstVector(None, self.ctx)
        if vars is not None:
           for v in vars:
               self.cube_vs.push(v)
        while True:
            lvl = self.backtrack_level
            self.backtrack_level = 4000000000
            r = AstVector(Z3_solver_cube(self.ctx.ref(), self.solver, self.cube_vs.vector, lvl), self.ctx)            
            if (len(r) == 1 and is_false(r[0])):
                return            
            yield r         
            if (len(r) == 0):                
                return

    def cube_vars(self):
        return self.cube_vs

    def proof(self):
        """Return a proof for the last `check()`. Proof construction must be enabled."""
        return _to_expr_ref(Z3_solver_get_proof(self.ctx.ref(), self.solver), self.ctx)

    def from_file(self, filename):
        """Parse assertions from a file"""
        Z3_solver_from_file(self.ctx.ref(), self.solver, filename)

    def from_string(self, s):
        """Parse assertions from a string"""
        Z3_solver_from_string(self.ctx.ref(), self.solver, s)
        
    def assertions(self):
        """Return an AST vector containing all added constraints.

        >>> s = Solver()
        >>> s.assertions()
        []
        >>> a = Int('a')
        >>> s.add(a > 0)
        >>> s.add(a < 10)
        >>> s.assertions()
        [a > 0, a < 10]
        """
        return AstVector(Z3_solver_get_assertions(self.ctx.ref(), self.solver), self.ctx)

    def units(self):
        """Return an AST vector containing all currently inferred units.
        """
        return AstVector(Z3_solver_get_units(self.ctx.ref(), self.solver), self.ctx)

    def statistics(self):
        """Return statistics for the last `check()`.

        >>> s = SimpleSolver()
        >>> x = Int('x')
        >>> s.add(x > 0)
        >>> s.check()
        sat
        >>> st = s.statistics()
        >>> st.get_key_value('final checks')
        1
        >>> len(st) > 0
        True
        >>> st[0] != 0
        True
        """
        return Statistics(Z3_solver_get_statistics(self.ctx.ref(), self.solver), self.ctx)

    def reason_unknown(self):
        """Return a string describing why the last `check()` returned `unknown`.

        >>> x = Int('x')
        >>> s = SimpleSolver()
        >>> s.add(2**x == 4)
        >>> s.check()
        unknown
        >>> s.reason_unknown()
        '(incomplete (theory arithmetic))'
        """
        return Z3_solver_get_reason_unknown(self.ctx.ref(), self.solver)

    def help(self):
        """Display a string describing all available options."""
        print(Z3_solver_get_help(self.ctx.ref(), self.solver))

    def param_descrs(self):
        """Return the parameter description set."""
        return ParamDescrsRef(Z3_solver_get_param_descrs(self.ctx.ref(), self.solver), self.ctx)

    def __repr__(self):
        """Return a formatted string with all added constraints."""
        return obj_to_string(self)

    def translate(self, target):
        """Translate `self` to the context `target`. That is, return a copy of `self` in the context `target`.

        >>> c1 = Context()
        >>> c2 = Context()
        >>> s1 = Solver(ctx=c1)
        >>> s2 = s1.translate(c2)
        """
        if __debug__:
            _z3_assert(isinstance(target, Context), "argument must be a Z3 context")
        solver = Z3_solver_translate(self.ctx.ref(), self.solver, target.ref())
        return Solver(solver, target)

    def __copy__(self):
        return self.translate(self.ctx)

    def __deepcopy__(self):
        return self.translate(self.ctx)

    def sexpr(self):
        """Return a formatted string (in Lisp-like format) with all added constraints. We say the string is in s-expression format.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0)
        >>> s.add(x < 2)
        >>> r = s.sexpr()
        """
        return Z3_solver_to_string(self.ctx.ref(), self.solver)

    def to_smt2(self):
        """return SMTLIB2 formatted benchmark for solver's assertions"""
        es = self.assertions()
        sz = len(es)
        sz1 = sz
        if sz1 > 0:
            sz1 -= 1
        v = (Ast * sz1)()
        for i in range(sz1):
            v[i] = es[i].as_ast()
        if sz > 0:
            e = es[sz1].as_ast()
        else:
            e = BoolVal(True, self.ctx).as_ast()
        return Z3_benchmark_to_smtlib_string(self.ctx.ref(), "benchmark generated from python API", "", "unknown", "", sz1, v, e)

def SolverFor(logic, ctx=None):
    """Create a solver customized for the given logic.

    The parameter `logic` is a string. It should be contains
    the name of a SMT-LIB logic.
    See http://www.smtlib.org/ for the name of all available logics.

    >>> s = SolverFor("QF_LIA")
    >>> x = Int('x')
    >>> s.add(x > 0)
    >>> s.add(x < 2)
    >>> s.check()
    sat
    >>> s.model()
    [x = 1]
    """
    ctx = _get_ctx(ctx)
    logic = to_symbol(logic)
    return Solver(Z3_mk_solver_for_logic(ctx.ref(), logic), ctx)

def SimpleSolver(ctx=None):
    """Return a simple general purpose solver with limited amount of preprocessing.

    >>> s = SimpleSolver()
    >>> x = Int('x')
    >>> s.add(x > 0)
    >>> s.check()
    sat
    """
    ctx = _get_ctx(ctx)
    return Solver(Z3_mk_simple_solver(ctx.ref()), ctx)

#########################################
#
# Fixedpoint
#
#########################################

class Fixedpoint(Z3PPObject):
    """Fixedpoint API provides methods for solving with recursive predicates"""

    def __init__(self, fixedpoint=None, ctx=None):
        assert fixedpoint is None or ctx is not None
        self.ctx    = _get_ctx(ctx)
        self.fixedpoint = None
        if fixedpoint is None:
            self.fixedpoint = Z3_mk_fixedpoint(self.ctx.ref())
        else:
            self.fixedpoint = fixedpoint
        Z3_fixedpoint_inc_ref(self.ctx.ref(), self.fixedpoint)
        self.vars = []

    def __deepcopy__(self, memo={}):
        return FixedPoint(self.fixedpoint, self.ctx)

    def __del__(self):
        if self.fixedpoint is not None and self.ctx.ref() is not None:
            Z3_fixedpoint_dec_ref(self.ctx.ref(), self.fixedpoint)

    def set(self, *args, **keys):
        """Set a configuration option. The method `help()` return a string containing all available options.
        """
        p = args2params(args, keys, self.ctx)
        Z3_fixedpoint_set_params(self.ctx.ref(), self.fixedpoint, p.params)

    def help(self):
        """Display a string describing all available options."""
        print(Z3_fixedpoint_get_help(self.ctx.ref(), self.fixedpoint))

    def param_descrs(self):
        """Return the parameter description set."""
        return ParamDescrsRef(Z3_fixedpoint_get_param_descrs(self.ctx.ref(), self.fixedpoint), self.ctx)

    def assert_exprs(self, *args):
        """Assert constraints as background axioms for the fixedpoint solver."""
        args = _get_args(args)
        s    = BoolSort(self.ctx)
        for arg in args:
            if isinstance(arg, Goal) or isinstance(arg, AstVector):
                for f in arg:
                    f = self.abstract(f)
                    Z3_fixedpoint_assert(self.ctx.ref(), self.fixedpoint, f.as_ast())
            else:
                arg = s.cast(arg)
                arg = self.abstract(arg)
                Z3_fixedpoint_assert(self.ctx.ref(), self.fixedpoint, arg.as_ast())

    def add(self, *args):
        """Assert constraints as background axioms for the fixedpoint solver. Alias for assert_expr."""
        self.assert_exprs(*args)

    def __iadd__(self, fml):
        self.add(fml)
        return self

    def append(self, *args):
        """Assert constraints as background axioms for the fixedpoint solver. Alias for assert_expr."""
        self.assert_exprs(*args)

    def insert(self, *args):
        """Assert constraints as background axioms for the fixedpoint solver. Alias for assert_expr."""
        self.assert_exprs(*args)

    def add_rule(self, head, body = None, name = None):
        """Assert rules defining recursive predicates to the fixedpoint solver.
        >>> a = Bool('a')
        >>> b = Bool('b')
        >>> s = Fixedpoint()
        >>> s.register_relation(a.decl())
        >>> s.register_relation(b.decl())
        >>> s.fact(a)
        >>> s.rule(b, a)
        >>> s.query(b)
        sat
        """
        if name is None:
            name = ""
        name = to_symbol(name, self.ctx)
        if body is None:
            head = self.abstract(head)
            Z3_fixedpoint_add_rule(self.ctx.ref(), self.fixedpoint, head.as_ast(), name)
        else:
            body = _get_args(body)
            f    = self.abstract(Implies(And(body, self.ctx),head))
            Z3_fixedpoint_add_rule(self.ctx.ref(), self.fixedpoint, f.as_ast(), name)

    def rule(self, head, body = None, name = None):
        """Assert rules defining recursive predicates to the fixedpoint solver. Alias for add_rule."""
        self.add_rule(head, body, name)

    def fact(self, head, name = None):
        """Assert facts defining recursive predicates to the fixedpoint solver. Alias for add_rule."""
        self.add_rule(head, None, name)

    def query(self, *query):
        """Query the fixedpoint engine whether formula is derivable.
           You can also pass an tuple or list of recursive predicates.
        """
        query = _get_args(query)
        sz = len(query)
        if sz >= 1 and isinstance(query[0], FuncDeclRef):
            _decls = (FuncDecl * sz)()
            i = 0
            for q in query:
                _decls[i] = q.ast
                i = i + 1
            r = Z3_fixedpoint_query_relations(self.ctx.ref(), self.fixedpoint, sz, _decls)
        else:
            if sz == 1:
                query = query[0]
            else:
                query = And(query, self.ctx)
            query = self.abstract(query, False)
            r = Z3_fixedpoint_query(self.ctx.ref(), self.fixedpoint, query.as_ast())
        return CheckSatResult(r)

    def query_from_lvl (self, lvl, *query):
        """Query the fixedpoint engine whether formula is derivable starting at the given query level.
        """
        query = _get_args(query)
        sz = len(query)
        if sz >= 1 and isinstance(query[0], FuncDecl):
            _z3_assert (False, "unsupported")
        else:
            if sz == 1:
                query = query[0]
            else:
                query = And(query)
            query = self.abstract(query, False)
            r = Z3_fixedpoint_query_from_lvl (self.ctx.ref(), self.fixedpoint, query.as_ast(), lvl)
        return CheckSatResult(r)

    def push(self):
        """create a backtracking point for added rules, facts and assertions"""
        Z3_fixedpoint_push(self.ctx.ref(), self.fixedpoint)

    def pop(self):
        """restore to previously created backtracking point"""
        Z3_fixedpoint_pop(self.ctx.ref(), self.fixedpoint)

    def update_rule(self, head, body, name):
        """update rule"""
        if name is None:
            name = ""
        name = to_symbol(name, self.ctx)
        body = _get_args(body)
        f    = self.abstract(Implies(And(body, self.ctx),head))
        Z3_fixedpoint_update_rule(self.ctx.ref(), self.fixedpoint, f.as_ast(), name)

    def get_answer(self):
        """Retrieve answer from last query call."""
        r = Z3_fixedpoint_get_answer(self.ctx.ref(), self.fixedpoint)
        return _to_expr_ref(r, self.ctx)

    def get_ground_sat_answer(self):
        """Retrieve a ground cex from last query call."""
        r = Z3_fixedpoint_get_ground_sat_answer(self.ctx.ref(), self.fixedpoint)
        return _to_expr_ref(r, self.ctx)

    def get_rules_along_trace(self):
        """retrieve rules along the counterexample trace"""
        return AstVector(Z3_fixedpoint_get_rules_along_trace(self.ctx.ref(), self.fixedpoint), self.ctx)

    def get_rule_names_along_trace(self):
        """retrieve rule names along the counterexample trace"""
        # this is a hack as I don't know how to return a list of symbols from C++;
        # obtain names as a single string separated by semicolons
        names = _symbol2py (self.ctx, Z3_fixedpoint_get_rule_names_along_trace(self.ctx.ref(), self.fixedpoint))
        # split into individual names
        return names.split (';')

    def get_num_levels(self, predicate):
        """Retrieve number of levels used for predicate in PDR engine"""
        return Z3_fixedpoint_get_num_levels(self.ctx.ref(), self.fixedpoint, predicate.ast)

    def get_cover_delta(self, level, predicate):
        """Retrieve properties known about predicate for the level'th unfolding. -1 is treated as the limit (infinity)"""
        r = Z3_fixedpoint_get_cover_delta(self.ctx.ref(), self.fixedpoint, level, predicate.ast)
        return _to_expr_ref(r, self.ctx)

    def add_cover(self, level, predicate, property):
        """Add property to predicate for the level'th unfolding. -1 is treated as infinity (infinity)"""
        Z3_fixedpoint_add_cover(self.ctx.ref(), self.fixedpoint, level, predicate.ast, property.ast)

    def register_relation(self, *relations):
        """Register relation as recursive"""
        relations = _get_args(relations)
        for f in relations:
            Z3_fixedpoint_register_relation(self.ctx.ref(), self.fixedpoint, f.ast)

    def set_predicate_representation(self, f, *representations):
        """Control how relation is represented"""
        representations = _get_args(representations)
        representations = [to_symbol(s) for s in representations]
        sz = len(representations)
        args = (Symbol * sz)()
        for i in range(sz):
            args[i] = representations[i]
        Z3_fixedpoint_set_predicate_representation(self.ctx.ref(), self.fixedpoint, f.ast, sz, args)

    def parse_string(self, s):
        """Parse rules and queries from a string"""
        try:
            return AstVector(Z3_fixedpoint_from_string(self.ctx.ref(), self.fixedpoint, s), self.ctx)
        except Z3Exception as e:
            _handle_parse_error(e, self.ctx)

    def parse_file(self, f):
        """Parse rules and queries from a file"""
        try:
            return AstVector(Z3_fixedpoint_from_file(self.ctx.ref(), self.fixedpoint, f), self.ctx)
        except Z3Exception as e:
            _handle_parse_error(e, self.ctx)

    def get_rules(self):
        """retrieve rules that have been added to fixedpoint context"""
        return AstVector(Z3_fixedpoint_get_rules(self.ctx.ref(), self.fixedpoint), self.ctx)

    def get_assertions(self):
        """retrieve assertions that have been added to fixedpoint context"""
        return AstVector(Z3_fixedpoint_get_assertions(self.ctx.ref(), self.fixedpoint), self.ctx)

    def __repr__(self):
        """Return a formatted string with all added rules and constraints."""
        return self.sexpr()

    def sexpr(self):
        """Return a formatted string (in Lisp-like format) with all added constraints. We say the string is in s-expression format.
        """
        return Z3_fixedpoint_to_string(self.ctx.ref(), self.fixedpoint, 0, (Ast * 0)())

    def to_string(self, queries):
        """Return a formatted string (in Lisp-like format) with all added constraints.
           We say the string is in s-expression format.
           Include also queries.
        """
        args, len = _to_ast_array(queries)
        return Z3_fixedpoint_to_string(self.ctx.ref(), self.fixedpoint, len, args)

    def statistics(self):
        """Return statistics for the last `query()`.
        """
        return Statistics(Z3_fixedpoint_get_statistics(self.ctx.ref(), self.fixedpoint), self.ctx)

    def reason_unknown(self):
        """Return a string describing why the last `query()` returned `unknown`.
        """
        return Z3_fixedpoint_get_reason_unknown(self.ctx.ref(), self.fixedpoint)

    def declare_var(self, *vars):
        """Add variable or several variables.
        The added variable or variables will be bound in the rules
        and queries
        """
        vars = _get_args(vars)
        for v in vars:
            self.vars += [v]

    def abstract(self, fml, is_forall=True):
        if self.vars == []:
            return fml
        if is_forall:
            return ForAll(self.vars, fml)
        else:
            return Exists(self.vars, fml)


#########################################
#
# Finite domains
#
#########################################

class FiniteDomainSortRef(SortRef):
    """Finite domain sort."""

    def size(self):
        """Return the size of the finite domain sort"""
        r = (ctypes.c_ulonglong * 1)()
        if Z3_get_finite_domain_sort_size(self.ctx_ref(), self.ast, r):
            return r[0]
        else:
            raise Z3Exception("Failed to retrieve finite domain sort size")

def FiniteDomainSort(name, sz, ctx=None):
    """Create a named finite domain sort of a given size sz"""
    if not isinstance(name, Symbol):
        name = to_symbol(name)
    ctx = _get_ctx(ctx)
    return FiniteDomainSortRef(Z3_mk_finite_domain_sort(ctx.ref(), name, sz), ctx)

def is_finite_domain_sort(s):
    """Return True if `s` is a Z3 finite-domain sort.

    >>> is_finite_domain_sort(FiniteDomainSort('S', 100))
    True
    >>> is_finite_domain_sort(IntSort())
    False
    """
    return isinstance(s, FiniteDomainSortRef)


class FiniteDomainRef(ExprRef):
    """Finite-domain expressions."""

    def sort(self):
        """Return the sort of the finite-domain expression `self`."""
        return FiniteDomainSortRef(Z3_get_sort(self.ctx_ref(), self.as_ast()), self.ctx)

    def as_string(self):
        """Return a Z3 floating point expression as a Python string."""
        return Z3_ast_to_string(self.ctx_ref(), self.as_ast())

def is_finite_domain(a):
    """Return `True` if `a` is a Z3 finite-domain expression.

    >>> s = FiniteDomainSort('S', 100)
    >>> b = Const('b', s)
    >>> is_finite_domain(b)
    True
    >>> is_finite_domain(Int('x'))
    False
    """
    return isinstance(a, FiniteDomainRef)


class FiniteDomainNumRef(FiniteDomainRef):
    """Integer values."""

    def as_long(self):
        """Return a Z3 finite-domain numeral as a Python long (bignum) numeral.

        >>> s = FiniteDomainSort('S', 100)
        >>> v = FiniteDomainVal(3, s)
        >>> v
        3
        >>> v.as_long() + 1
        4
        """
        return int(self.as_string())

    def as_string(self):
        """Return a Z3 finite-domain numeral as a Python string.

        >>> s = FiniteDomainSort('S', 100)
        >>> v = FiniteDomainVal(42, s)
        >>> v.as_string()
        '42'
        """
        return Z3_get_numeral_string(self.ctx_ref(), self.as_ast())


def FiniteDomainVal(val, sort, ctx=None):
    """Return a Z3 finite-domain value. If `ctx=None`, then the global context is used.

    >>> s = FiniteDomainSort('S', 256)
    >>> FiniteDomainVal(255, s)
    255
    >>> FiniteDomainVal('100', s)
    100
    """
    if __debug__:
        _z3_assert(is_finite_domain_sort(sort), "Expected finite-domain sort" )
    ctx = sort.ctx
    return FiniteDomainNumRef(Z3_mk_numeral(ctx.ref(), _to_int_str(val), sort.ast), ctx)

def is_finite_domain_value(a):
    """Return `True` if `a` is a Z3 finite-domain value.

    >>> s = FiniteDomainSort('S', 100)
    >>> b = Const('b', s)
    >>> is_finite_domain_value(b)
    False
    >>> b = FiniteDomainVal(10, s)
    >>> b
    10
    >>> is_finite_domain_value(b)
    True
    """
    return is_finite_domain(a) and _is_numeral(a.ctx, a.as_ast())


#########################################
#
# Optimize
#
#########################################

class OptimizeObjective:
    def __init__(self, opt, value, is_max):
        self._opt = opt
        self._value = value
        self._is_max = is_max

    def lower(self):
        opt = self._opt
        return _to_expr_ref(Z3_optimize_get_lower(opt.ctx.ref(), opt.optimize, self._value), opt.ctx)

    def upper(self):
        opt = self._opt
        return _to_expr_ref(Z3_optimize_get_upper(opt.ctx.ref(), opt.optimize, self._value), opt.ctx)

    def lower_values(self):
        opt = self._opt
        return AstVector(Z3_optimize_get_lower_as_vector(opt.ctx.ref(), opt.optimize, self._value), opt.ctx)

    def upper_values(self):
        opt = self._opt
        return AstVector(Z3_optimize_get_upper_as_vector(opt.ctx.ref(), opt.optimize, self._value), opt.ctx)

    def value(self):
        if self._is_max:
            return self.upper()
        else:
            return self.lower()

    def __str__(self):
        return "%s:%s" % (self._value, self._is_max)


class Optimize(Z3PPObject):
    """Optimize API provides methods for solving using objective functions and weighted soft constraints"""

    def __init__(self, ctx=None):
        self.ctx    = _get_ctx(ctx)
        self.optimize = Z3_mk_optimize(self.ctx.ref())
        Z3_optimize_inc_ref(self.ctx.ref(), self.optimize)

    def __deepcopy__(self, memo={}):
        return Optimize(self.optimize, self.ctx)

    def __del__(self):
        if self.optimize is not None and self.ctx.ref() is not None:
            Z3_optimize_dec_ref(self.ctx.ref(), self.optimize)

    def set(self, *args, **keys):
        """Set a configuration option. The method `help()` return a string containing all available options.
        """
        p = args2params(args, keys, self.ctx)
        Z3_optimize_set_params(self.ctx.ref(), self.optimize, p.params)

    def help(self):
        """Display a string describing all available options."""
        print(Z3_optimize_get_help(self.ctx.ref(), self.optimize))

    def param_descrs(self):
        """Return the parameter description set."""
        return ParamDescrsRef(Z3_optimize_get_param_descrs(self.ctx.ref(), self.optimize), self.ctx)

    def assert_exprs(self, *args):
        """Assert constraints as background axioms for the optimize solver."""
        args = _get_args(args)
        s    = BoolSort(self.ctx)
        for arg in args:
            if isinstance(arg, Goal) or isinstance(arg, AstVector):
                for f in arg:
                    Z3_optimize_assert(self.ctx.ref(), self.optimize, f.as_ast())
            else:
                arg = s.cast(arg)
                Z3_optimize_assert(self.ctx.ref(), self.optimize, arg.as_ast())

    def add(self, *args):
        """Assert constraints as background axioms for the optimize solver. Alias for assert_expr."""
        self.assert_exprs(*args)

    def __iadd__(self, fml):
        self.add(fml)
        return self

    def add_soft(self, arg, weight = "1", id = None):
        """Add soft constraint with optional weight and optional identifier.
           If no weight is supplied, then the penalty for violating the soft constraint
           is 1.
           Soft constraints are grouped by identifiers. Soft constraints that are
           added without identifiers are grouped by default.
        """
        if _is_int(weight):
            weight = "%d" % weight
        elif isinstance(weight, float):
            weight = "%f" % weight
        if not isinstance(weight, str):
            raise Z3Exception("weight should be a string or an integer")
        if id is None:
            id = ""
        id = to_symbol(id, self.ctx)
        v = Z3_optimize_assert_soft(self.ctx.ref(), self.optimize, arg.as_ast(), weight, id)
        return OptimizeObjective(self, v, False)

    def maximize(self, arg):
        """Add objective function to maximize."""
        return OptimizeObjective(self, Z3_optimize_maximize(self.ctx.ref(), self.optimize, arg.as_ast()), True)

    def minimize(self, arg):
        """Add objective function to minimize."""
        return OptimizeObjective(self, Z3_optimize_minimize(self.ctx.ref(), self.optimize, arg.as_ast()), False)

    def push(self):
        """create a backtracking point for added rules, facts and assertions"""
        Z3_optimize_push(self.ctx.ref(), self.optimize)

    def pop(self):
        """restore to previously created backtracking point"""
        Z3_optimize_pop(self.ctx.ref(), self.optimize)

    def check(self):
        """Check satisfiability while optimizing objective functions."""
        return CheckSatResult(Z3_optimize_check(self.ctx.ref(), self.optimize))

    def reason_unknown(self):
        """Return a string that describes why the last `check()` returned `unknown`."""
        return Z3_optimize_get_reason_unknown(self.ctx.ref(), self.optimize)

    def model(self):
        """Return a model for the last check()."""
        try:
            return ModelRef(Z3_optimize_get_model(self.ctx.ref(), self.optimize), self.ctx)
        except Z3Exception:
            raise Z3Exception("model is not available")

    def lower(self, obj):
        if not isinstance(obj, OptimizeObjective):
            raise Z3Exception("Expecting objective handle returned by maximize/minimize")
        return obj.lower()

    def upper(self, obj):
        if not isinstance(obj, OptimizeObjective):
            raise Z3Exception("Expecting objective handle returned by maximize/minimize")
        return obj.upper()

    def lower_values(self, obj):
        if not isinstance(obj, OptimizeObjective):
            raise Z3Exception("Expecting objective handle returned by maximize/minimize")
        return obj.lower_values()

    def upper_values(self, obj):
        if not isinstance(obj, OptimizeObjective):
            raise Z3Exception("Expecting objective handle returned by maximize/minimize")
        return obj.upper_values()    

    def from_file(self, filename):
        """Parse assertions and objectives from a file"""
        try:
            Z3_optimize_from_file(self.ctx.ref(), self.optimize, filename)
        except Z3Exception as e:
            _handle_parse_error(e, self.ctx)

    def from_string(self, s):
        """Parse assertions and objectives from a string"""
        try:
            Z3_optimize_from_string(self.ctx.ref(), self.optimize, s)
        except Z3Exception as e:
            _handle_parse_error(e, self.ctx)

    def assertions(self):
        """Return an AST vector containing all added constraints."""
        return AstVector(Z3_optimize_get_assertions(self.ctx.ref(), self.optimize), self.ctx)

    def objectives(self):
        """returns set of objective functions"""
        return AstVector(Z3_optimize_get_objectives(self.ctx.ref(), self.optimize), self.ctx)

    def __repr__(self):
        """Return a formatted string with all added rules and constraints."""
        return self.sexpr()

    def sexpr(self):
        """Return a formatted string (in Lisp-like format) with all added constraints. We say the string is in s-expression format.
        """
        return Z3_optimize_to_string(self.ctx.ref(), self.optimize)

    def statistics(self):
        """Return statistics for the last check`.
        """
        return Statistics(Z3_optimize_get_statistics(self.ctx.ref(), self.optimize), self.ctx)




#########################################
#
# ApplyResult
#
#########################################
class ApplyResult(Z3PPObject):
    """An ApplyResult object contains the subgoals produced by a tactic when applied to a goal. It also contains model and proof converters."""

    def __init__(self, result, ctx):
        self.result = result
        self.ctx    = ctx
        Z3_apply_result_inc_ref(self.ctx.ref(), self.result)

    def __deepcopy__(self, memo={}):
        return ApplyResult(self.result, self.ctx)

    def __del__(self):
        if self.ctx.ref() is not None:
            Z3_apply_result_dec_ref(self.ctx.ref(), self.result)

    def __len__(self):
        """Return the number of subgoals in `self`.

        >>> a, b = Ints('a b')
        >>> g = Goal()
        >>> g.add(Or(a == 0, a == 1), Or(b == 0, b == 1), a > b)
        >>> t = Tactic('split-clause')
        >>> r = t(g)
        >>> len(r)
        2
        >>> t = Then(Tactic('split-clause'), Tactic('split-clause'))
        >>> len(t(g))
        4
        >>> t = Then(Tactic('split-clause'), Tactic('split-clause'), Tactic('propagate-values'))
        >>> len(t(g))
        1
        """
        return int(Z3_apply_result_get_num_subgoals(self.ctx.ref(), self.result))

    def __getitem__(self, idx):
        """Return one of the subgoals stored in ApplyResult object `self`.

        >>> a, b = Ints('a b')
        >>> g = Goal()
        >>> g.add(Or(a == 0, a == 1), Or(b == 0, b == 1), a > b)
        >>> t = Tactic('split-clause')
        >>> r = t(g)
        >>> r[0]
        [a == 0, Or(b == 0, b == 1), a > b]
        >>> r[1]
        [a == 1, Or(b == 0, b == 1), a > b]
        """
        if idx >= len(self):
            raise IndexError
        return Goal(goal=Z3_apply_result_get_subgoal(self.ctx.ref(), self.result, idx), ctx=self.ctx)

    def __repr__(self):
        return obj_to_string(self)

    def sexpr(self):
        """Return a textual representation of the s-expression representing the set of subgoals in `self`."""
        return Z3_apply_result_to_string(self.ctx.ref(), self.result)


    def as_expr(self):
        """Return a Z3 expression consisting of all subgoals.

        >>> x = Int('x')
        >>> g = Goal()
        >>> g.add(x > 1)
        >>> g.add(Or(x == 2, x == 3))
        >>> r = Tactic('simplify')(g)
        >>> r
        [[Not(x <= 1), Or(x == 2, x == 3)]]
        >>> r.as_expr()
        And(Not(x <= 1), Or(x == 2, x == 3))
        >>> r = Tactic('split-clause')(g)
        >>> r
        [[x > 1, x == 2], [x > 1, x == 3]]
        >>> r.as_expr()
        Or(And(x > 1, x == 2), And(x > 1, x == 3))
        """
        sz = len(self)
        if sz == 0:
            return BoolVal(False, self.ctx)
        elif sz == 1:
            return self[0].as_expr()
        else:
            return Or([ self[i].as_expr() for i in range(len(self)) ])

#########################################
#
# Tactics
#
#########################################
class Tactic:
    """Tactics transform, solver and/or simplify sets of constraints (Goal). A Tactic can be converted into a Solver using the method solver().

    Several combinators are available for creating new tactics using the built-in ones: Then(), OrElse(), FailIf(), Repeat(), When(), Cond().
    """
    def __init__(self, tactic, ctx=None):
        self.ctx    = _get_ctx(ctx)
        self.tactic = None
        if isinstance(tactic, TacticObj):
            self.tactic = tactic
        else:
            if __debug__:
                _z3_assert(isinstance(tactic, str), "tactic name expected")
            try:
                self.tactic = Z3_mk_tactic(self.ctx.ref(), str(tactic))
            except Z3Exception:
                raise Z3Exception("unknown tactic '%s'" % tactic)
        Z3_tactic_inc_ref(self.ctx.ref(), self.tactic)

    def __deepcopy__(self, memo={}):
        return Tactic(self.tactic, self.ctx)

    def __del__(self):
        if self.tactic is not None and self.ctx.ref() is not None:
            Z3_tactic_dec_ref(self.ctx.ref(), self.tactic)

    def solver(self):
        """Create a solver using the tactic `self`.

        The solver supports the methods `push()` and `pop()`, but it
        will always solve each `check()` from scratch.

        >>> t = Then('simplify', 'nlsat')
        >>> s = t.solver()
        >>> x = Real('x')
        >>> s.add(x**2 == 2, x > 0)
        >>> s.check()
        sat
        >>> s.model()
        [x = 1.4142135623?]
        """
        return Solver(Z3_mk_solver_from_tactic(self.ctx.ref(), self.tactic), self.ctx)

    def apply(self, goal, *arguments, **keywords):
        """Apply tactic `self` to the given goal or Z3 Boolean expression using the given options.

        >>> x, y = Ints('x y')
        >>> t = Tactic('solve-eqs')
        >>> t.apply(And(x == 0, y >= x + 1))
        [[y >= 1]]
        """
        if __debug__:
            _z3_assert(isinstance(goal, Goal) or isinstance(goal, BoolRef), "Z3 Goal or Boolean expressions expected")
        goal = _to_goal(goal)
        if len(arguments) > 0 or len(keywords) > 0:
            p = args2params(arguments, keywords, self.ctx)
            return ApplyResult(Z3_tactic_apply_ex(self.ctx.ref(), self.tactic, goal.goal, p.params), self.ctx)
        else:
            return ApplyResult(Z3_tactic_apply(self.ctx.ref(), self.tactic, goal.goal), self.ctx)

    def __call__(self, goal, *arguments, **keywords):
        """Apply tactic `self` to the given goal or Z3 Boolean expression using the given options.

        >>> x, y = Ints('x y')
        >>> t = Tactic('solve-eqs')
        >>> t(And(x == 0, y >= x + 1))
        [[y >= 1]]
        """
        return self.apply(goal, *arguments, **keywords)

    def help(self):
        """Display a string containing a description of the available options for the `self` tactic."""
        print(Z3_tactic_get_help(self.ctx.ref(), self.tactic))

    def param_descrs(self):
        """Return the parameter description set."""
        return ParamDescrsRef(Z3_tactic_get_param_descrs(self.ctx.ref(), self.tactic), self.ctx)

def _to_goal(a):
    if isinstance(a, BoolRef):
        goal = Goal(ctx = a.ctx)
        goal.add(a)
        return goal
    else:
        return a

def _to_tactic(t, ctx=None):
    if isinstance(t, Tactic):
        return t
    else:
        return Tactic(t, ctx)

def _and_then(t1, t2, ctx=None):
    t1 = _to_tactic(t1, ctx)
    t2 = _to_tactic(t2, ctx)
    if __debug__:
        _z3_assert(t1.ctx == t2.ctx, "Context mismatch")
    return Tactic(Z3_tactic_and_then(t1.ctx.ref(), t1.tactic, t2.tactic), t1.ctx)

def _or_else(t1, t2, ctx=None):
    t1 = _to_tactic(t1, ctx)
    t2 = _to_tactic(t2, ctx)
    if __debug__:
        _z3_assert(t1.ctx == t2.ctx, "Context mismatch")
    return Tactic(Z3_tactic_or_else(t1.ctx.ref(), t1.tactic, t2.tactic), t1.ctx)

def AndThen(*ts, **ks):
    """Return a tactic that applies the tactics in `*ts` in sequence.

    >>> x, y = Ints('x y')
    >>> t = AndThen(Tactic('simplify'), Tactic('solve-eqs'))
    >>> t(And(x == 0, y > x + 1))
    [[Not(y <= 1)]]
    >>> t(And(x == 0, y > x + 1)).as_expr()
    Not(y <= 1)
    """
    if __debug__:
        _z3_assert(len(ts) >= 2, "At least two arguments expected")
    ctx = ks.get('ctx', None)
    num = len(ts)
    r = ts[0]
    for i in range(num - 1):
        r = _and_then(r, ts[i+1], ctx)
    return r

def Then(*ts, **ks):
    """Return a tactic that applies the tactics in `*ts` in sequence. Shorthand for AndThen(*ts, **ks).

    >>> x, y = Ints('x y')
    >>> t = Then(Tactic('simplify'), Tactic('solve-eqs'))
    >>> t(And(x == 0, y > x + 1))
    [[Not(y <= 1)]]
    >>> t(And(x == 0, y > x + 1)).as_expr()
    Not(y <= 1)
    """
    return AndThen(*ts, **ks)

def OrElse(*ts, **ks):
    """Return a tactic that applies the tactics in `*ts` until one of them succeeds (it doesn't fail).

    >>> x = Int('x')
    >>> t = OrElse(Tactic('split-clause'), Tactic('skip'))
    >>> # Tactic split-clause fails if there is no clause in the given goal.
    >>> t(x == 0)
    [[x == 0]]
    >>> t(Or(x == 0, x == 1))
    [[x == 0], [x == 1]]
    """
    if __debug__:
        _z3_assert(len(ts) >= 2, "At least two arguments expected")
    ctx = ks.get('ctx', None)
    num = len(ts)
    r = ts[0]
    for i in range(num - 1):
        r = _or_else(r, ts[i+1], ctx)
    return r

def ParOr(*ts, **ks):
    """Return a tactic that applies the tactics in `*ts` in parallel until one of them succeeds (it doesn't fail).

    >>> x = Int('x')
    >>> t = ParOr(Tactic('simplify'), Tactic('fail'))
    >>> t(x + 1 == 2)
    [[x == 1]]
    """
    if __debug__:
        _z3_assert(len(ts) >= 2, "At least two arguments expected")
    ctx = _get_ctx(ks.get('ctx', None))
    ts  = [ _to_tactic(t, ctx) for t in ts ]
    sz  = len(ts)
    _args = (TacticObj * sz)()
    for i in range(sz):
        _args[i] = ts[i].tactic
    return Tactic(Z3_tactic_par_or(ctx.ref(), sz, _args), ctx)

def ParThen(t1, t2, ctx=None):
    """Return a tactic that applies t1 and then t2 to every subgoal produced by t1. The subgoals are processed in parallel.

    >>> x, y = Ints('x y')
    >>> t = ParThen(Tactic('split-clause'), Tactic('propagate-values'))
    >>> t(And(Or(x == 1, x == 2), y == x + 1))
    [[x == 1, y == 2], [x == 2, y == 3]]
    """
    t1 = _to_tactic(t1, ctx)
    t2 = _to_tactic(t2, ctx)
    if __debug__:
        _z3_assert(t1.ctx == t2.ctx, "Context mismatch")
    return Tactic(Z3_tactic_par_and_then(t1.ctx.ref(), t1.tactic, t2.tactic), t1.ctx)

def ParAndThen(t1, t2, ctx=None):
    """Alias for ParThen(t1, t2, ctx)."""
    return ParThen(t1, t2, ctx)

def With(t, *args, **keys):
    """Return a tactic that applies tactic `t` using the given configuration options.

    >>> x, y = Ints('x y')
    >>> t = With(Tactic('simplify'), som=True)
    >>> t((x + 1)*(y + 2) == 0)
    [[2*x + y + x*y == -2]]
    """
    ctx = keys.pop('ctx', None)
    t = _to_tactic(t, ctx)
    p = args2params(args, keys, t.ctx)
    return Tactic(Z3_tactic_using_params(t.ctx.ref(), t.tactic, p.params), t.ctx)

def WithParams(t, p):
    """Return a tactic that applies tactic `t` using the given configuration options.

    >>> x, y = Ints('x y')
    >>> p = ParamsRef()
    >>> p.set("som", True)
    >>> t = WithParams(Tactic('simplify'), p)
    >>> t((x + 1)*(y + 2) == 0)
    [[2*x + y + x*y == -2]]
    """
    t = _to_tactic(t, None)
    return Tactic(Z3_tactic_using_params(t.ctx.ref(), t.tactic, p.params), t.ctx)

def Repeat(t, max=4294967295, ctx=None):
    """Return a tactic that keeps applying `t` until the goal is not modified anymore or the maximum number of iterations `max` is reached.

    >>> x, y = Ints('x y')
    >>> c = And(Or(x == 0, x == 1), Or(y == 0, y == 1), x > y)
    >>> t = Repeat(OrElse(Tactic('split-clause'), Tactic('skip')))
    >>> r = t(c)
    >>> for subgoal in r: print(subgoal)
    [x == 0, y == 0, x > y]
    [x == 0, y == 1, x > y]
    [x == 1, y == 0, x > y]
    [x == 1, y == 1, x > y]
    >>> t = Then(t, Tactic('propagate-values'))
    >>> t(c)
    [[x == 1, y == 0]]
    """
    t = _to_tactic(t, ctx)
    return Tactic(Z3_tactic_repeat(t.ctx.ref(), t.tactic, max), t.ctx)

def TryFor(t, ms, ctx=None):
    """Return a tactic that applies `t` to a given goal for `ms` milliseconds.

    If `t` does not terminate in `ms` milliseconds, then it fails.
    """
    t = _to_tactic(t, ctx)
    return Tactic(Z3_tactic_try_for(t.ctx.ref(), t.tactic, ms), t.ctx)

def tactics(ctx=None):
    """Return a list of all available tactics in Z3.

    >>> l = tactics()
    >>> l.count('simplify') == 1
    True
    """
    ctx = _get_ctx(ctx)
    return [ Z3_get_tactic_name(ctx.ref(), i) for i in range(Z3_get_num_tactics(ctx.ref())) ]

def tactic_description(name, ctx=None):
    """Return a short description for the tactic named `name`.

    >>> d = tactic_description('simplify')
    """
    ctx = _get_ctx(ctx)
    return Z3_tactic_get_descr(ctx.ref(), name)

def describe_tactics():
    """Display a (tabular) description of all available tactics in Z3."""
    if in_html_mode():
        even = True
        print('<table border="1" cellpadding="2" cellspacing="0">')
        for t in tactics():
            if even:
                print('<tr style="background-color:#CFCFCF">')
                even = False
            else:
                print('<tr>')
                even = True
            print('<td>%s</td><td>%s</td></tr>' % (t, insert_line_breaks(tactic_description(t), 40)))
        print('</table>')
    else:
        for t in tactics():
            print('%s : %s' % (t, tactic_description(t)))

class Probe:
    """Probes are used to inspect a goal (aka problem) and collect information that may be used to decide which solver and/or preprocessing step will be used."""
    def __init__(self, probe, ctx=None):
        self.ctx    = _get_ctx(ctx)
        self.probe  = None
        if isinstance(probe, ProbeObj):
            self.probe = probe
        elif isinstance(probe, float):
            self.probe = Z3_probe_const(self.ctx.ref(), probe)
        elif _is_int(probe):
            self.probe = Z3_probe_const(self.ctx.ref(), float(probe))
        elif isinstance(probe, bool):
            if probe:
                self.probe = Z3_probe_const(self.ctx.ref(), 1.0)
            else:
                self.probe = Z3_probe_const(self.ctx.ref(), 0.0)
        else:
            if __debug__:
                _z3_assert(isinstance(probe, str), "probe name expected")
            try:
                self.probe = Z3_mk_probe(self.ctx.ref(), probe)
            except Z3Exception:
                raise Z3Exception("unknown probe '%s'" % probe)
        Z3_probe_inc_ref(self.ctx.ref(), self.probe)

    def __deepcopy__(self, memo={}):
        return Probe(self.probe, self.ctx)

    def __del__(self):
        if self.probe is not None and self.ctx.ref() is not None:
            Z3_probe_dec_ref(self.ctx.ref(), self.probe)

    def __lt__(self, other):
        """Return a probe that evaluates to "true" when the value returned by `self` is less than the value returned by `other`.

        >>> p = Probe('size') < 10
        >>> x = Int('x')
        >>> g = Goal()
        >>> g.add(x > 0)
        >>> g.add(x < 10)
        >>> p(g)
        1.0
        """
        return Probe(Z3_probe_lt(self.ctx.ref(), self.probe, _to_probe(other, self.ctx).probe), self.ctx)

    def __gt__(self, other):
        """Return a probe that evaluates to "true" when the value returned by `self` is greater than the value returned by `other`.

        >>> p = Probe('size') > 10
        >>> x = Int('x')
        >>> g = Goal()
        >>> g.add(x > 0)
        >>> g.add(x < 10)
        >>> p(g)
        0.0
        """
        return Probe(Z3_probe_gt(self.ctx.ref(), self.probe, _to_probe(other, self.ctx).probe), self.ctx)

    def __le__(self, other):
        """Return a probe that evaluates to "true" when the value returned by `self` is less than or equal to the value returned by `other`.

        >>> p = Probe('size') <= 2
        >>> x = Int('x')
        >>> g = Goal()
        >>> g.add(x > 0)
        >>> g.add(x < 10)
        >>> p(g)
        1.0
        """
        return Probe(Z3_probe_le(self.ctx.ref(), self.probe, _to_probe(other, self.ctx).probe), self.ctx)

    def __ge__(self, other):
        """Return a probe that evaluates to "true" when the value returned by `self` is greater than or equal to the value returned by `other`.

        >>> p = Probe('size') >= 2
        >>> x = Int('x')
        >>> g = Goal()
        >>> g.add(x > 0)
        >>> g.add(x < 10)
        >>> p(g)
        1.0
        """
        return Probe(Z3_probe_ge(self.ctx.ref(), self.probe, _to_probe(other, self.ctx).probe), self.ctx)

    def __eq__(self, other):
        """Return a probe that evaluates to "true" when the value returned by `self` is equal to the value returned by `other`.

        >>> p = Probe('size') == 2
        >>> x = Int('x')
        >>> g = Goal()
        >>> g.add(x > 0)
        >>> g.add(x < 10)
        >>> p(g)
        1.0
        """
        return Probe(Z3_probe_eq(self.ctx.ref(), self.probe, _to_probe(other, self.ctx).probe), self.ctx)

    def __ne__(self, other):
        """Return a probe that evaluates to "true" when the value returned by `self` is not equal to the value returned by `other`.

        >>> p = Probe('size') != 2
        >>> x = Int('x')
        >>> g = Goal()
        >>> g.add(x > 0)
        >>> g.add(x < 10)
        >>> p(g)
        0.0
        """
        p = self.__eq__(other)
        return Probe(Z3_probe_not(self.ctx.ref(), p.probe), self.ctx)

    def __call__(self, goal):
        """Evaluate the probe `self` in the given goal.

        >>> p = Probe('size')
        >>> x = Int('x')
        >>> g = Goal()
        >>> g.add(x > 0)
        >>> g.add(x < 10)
        >>> p(g)
        2.0
        >>> g.add(x < 20)
        >>> p(g)
        3.0
        >>> p = Probe('num-consts')
        >>> p(g)
        1.0
        >>> p = Probe('is-propositional')
        >>> p(g)
        0.0
        >>> p = Probe('is-qflia')
        >>> p(g)
        1.0
        """
        if __debug__:
            _z3_assert(isinstance(goal, Goal) or isinstance(goal, BoolRef), "Z3 Goal or Boolean expression expected")
        goal = _to_goal(goal)
        return Z3_probe_apply(self.ctx.ref(), self.probe, goal.goal)

def is_probe(p):
    """Return `True` if `p` is a Z3 probe.

    >>> is_probe(Int('x'))
    False
    >>> is_probe(Probe('memory'))
    True
    """
    return isinstance(p, Probe)

def _to_probe(p, ctx=None):
    if is_probe(p):
        return p
    else:
        return Probe(p, ctx)

def probes(ctx=None):
    """Return a list of all available probes in Z3.

    >>> l = probes()
    >>> l.count('memory') == 1
    True
    """
    ctx = _get_ctx(ctx)
    return [ Z3_get_probe_name(ctx.ref(), i) for i in range(Z3_get_num_probes(ctx.ref())) ]

def probe_description(name, ctx=None):
    """Return a short description for the probe named `name`.

    >>> d = probe_description('memory')
    """
    ctx = _get_ctx(ctx)
    return Z3_probe_get_descr(ctx.ref(), name)

def describe_probes():
    """Display a (tabular) description of all available probes in Z3."""
    if in_html_mode():
        even = True
        print('<table border="1" cellpadding="2" cellspacing="0">')
        for p in probes():
            if even:
                print('<tr style="background-color:#CFCFCF">')
                even = False
            else:
                print('<tr>')
                even = True
            print('<td>%s</td><td>%s</td></tr>' % (p, insert_line_breaks(probe_description(p), 40)))
        print('</table>')
    else:
        for p in probes():
            print('%s : %s' % (p, probe_description(p)))

def _probe_nary(f, args, ctx):
    if __debug__:
        _z3_assert(len(args) > 0, "At least one argument expected")
    num = len(args)
    r = _to_probe(args[0], ctx)
    for i in range(num - 1):
        r = Probe(f(ctx.ref(), r.probe, _to_probe(args[i+1], ctx).probe), ctx)
    return r

def _probe_and(args, ctx):
    return _probe_nary(Z3_probe_and, args, ctx)

def _probe_or(args, ctx):
    return _probe_nary(Z3_probe_or, args, ctx)

def FailIf(p, ctx=None):
    """Return a tactic that fails if the probe `p` evaluates to true. Otherwise, it returns the input goal unmodified.

    In the following example, the tactic applies 'simplify' if and only if there are more than 2 constraints in the goal.

    >>> t = OrElse(FailIf(Probe('size') > 2), Tactic('simplify'))
    >>> x, y = Ints('x y')
    >>> g = Goal()
    >>> g.add(x > 0)
    >>> g.add(y > 0)
    >>> t(g)
    [[x > 0, y > 0]]
    >>> g.add(x == y + 1)
    >>> t(g)
    [[Not(x <= 0), Not(y <= 0), x == 1 + y]]
    """
    p = _to_probe(p, ctx)
    return Tactic(Z3_tactic_fail_if(p.ctx.ref(), p.probe), p.ctx)

def When(p, t, ctx=None):
    """Return a tactic that applies tactic `t` only if probe `p` evaluates to true. Otherwise, it returns the input goal unmodified.

    >>> t = When(Probe('size') > 2, Tactic('simplify'))
    >>> x, y = Ints('x y')
    >>> g = Goal()
    >>> g.add(x > 0)
    >>> g.add(y > 0)
    >>> t(g)
    [[x > 0, y > 0]]
    >>> g.add(x == y + 1)
    >>> t(g)
    [[Not(x <= 0), Not(y <= 0), x == 1 + y]]
    """
    p = _to_probe(p, ctx)
    t = _to_tactic(t, ctx)
    return Tactic(Z3_tactic_when(t.ctx.ref(), p.probe, t.tactic), t.ctx)

def Cond(p, t1, t2, ctx=None):
    """Return a tactic that applies tactic `t1` to a goal if probe `p` evaluates to true, and `t2` otherwise.

    >>> t = Cond(Probe('is-qfnra'), Tactic('qfnra'), Tactic('smt'))
    """
    p = _to_probe(p, ctx)
    t1 = _to_tactic(t1, ctx)
    t2 = _to_tactic(t2, ctx)
    return Tactic(Z3_tactic_cond(t1.ctx.ref(), p.probe, t1.tactic, t2.tactic), t1.ctx)

#########################################
#
# Utils
#
#########################################

def simplify(a, *arguments, **keywords):
    """Simplify the expression `a` using the given options.

    This function has many options. Use `help_simplify` to obtain the complete list.

    >>> x = Int('x')
    >>> y = Int('y')
    >>> simplify(x + 1 + y + x + 1)
    2 + 2*x + y
    >>> simplify((x + 1)*(y + 1), som=True)
    1 + x + y + x*y
    >>> simplify(Distinct(x, y, 1), blast_distinct=True)
    And(Not(x == y), Not(x == 1), Not(y == 1))
    >>> simplify(And(x == 0, y == 1), elim_and=True)
    Not(Or(Not(x == 0), Not(y == 1)))
    """
    if __debug__:
        _z3_assert(is_expr(a), "Z3 expression expected")
    if len(arguments) > 0 or len(keywords) > 0:
        p = args2params(arguments, keywords, a.ctx)
        return _to_expr_ref(Z3_simplify_ex(a.ctx_ref(), a.as_ast(), p.params), a.ctx)
    else:
        return _to_expr_ref(Z3_simplify(a.ctx_ref(), a.as_ast()), a.ctx)

def help_simplify():
    """Return a string describing all options available for Z3 `simplify` procedure."""
    print(Z3_simplify_get_help(main_ctx().ref()))

def simplify_param_descrs():
    """Return the set of parameter descriptions for Z3 `simplify` procedure."""
    return ParamDescrsRef(Z3_simplify_get_param_descrs(main_ctx().ref()), main_ctx())

def substitute(t, *m):
    """Apply substitution m on t, m is a list of pairs of the form (from, to). Every occurrence in t of from is replaced with to.

    >>> x = Int('x')
    >>> y = Int('y')
    >>> substitute(x + 1, (x, y + 1))
    y + 1 + 1
    >>> f = Function('f', IntSort(), IntSort())
    >>> substitute(f(x) + f(y), (f(x), IntVal(1)), (f(y), IntVal(1)))
    1 + 1
    """
    if isinstance(m, tuple):
        m1 = _get_args(m)
        if isinstance(m1, list):
            m = m1
    if __debug__:
        _z3_assert(is_expr(t), "Z3 expression expected")
        _z3_assert(all([isinstance(p, tuple) and is_expr(p[0]) and is_expr(p[1]) and p[0].sort().eq(p[1].sort()) for p in m]), "Z3 invalid substitution, expression pairs expected.")
    num = len(m)
    _from = (Ast * num)()
    _to   = (Ast * num)()
    for i in range(num):
        _from[i] = m[i][0].as_ast()
        _to[i]   = m[i][1].as_ast()
    return _to_expr_ref(Z3_substitute(t.ctx.ref(), t.as_ast(), num, _from, _to), t.ctx)

def substitute_vars(t, *m):
    """Substitute the free variables in t with the expression in m.

    >>> v0 = Var(0, IntSort())
    >>> v1 = Var(1, IntSort())
    >>> x  = Int('x')
    >>> f  = Function('f', IntSort(), IntSort(), IntSort())
    >>> # replace v0 with x+1 and v1 with x
    >>> substitute_vars(f(v0, v1), x + 1, x)
    f(x + 1, x)
    """
    if __debug__:
        _z3_assert(is_expr(t), "Z3 expression expected")
        _z3_assert(all([is_expr(n) for n in m]), "Z3 invalid substitution, list of expressions expected.")
    num = len(m)
    _to   = (Ast * num)()
    for i in range(num):
        _to[i] = m[i].as_ast()
    return _to_expr_ref(Z3_substitute_vars(t.ctx.ref(), t.as_ast(), num, _to), t.ctx)

def Sum(*args):
    """Create the sum of the Z3 expressions.

    >>> a, b, c = Ints('a b c')
    >>> Sum(a, b, c)
    a + b + c
    >>> Sum([a, b, c])
    a + b + c
    >>> A = IntVector('a', 5)
    >>> Sum(A)
    a__0 + a__1 + a__2 + a__3 + a__4
    """
    args  = _get_args(args)
    if len(args) == 0:
        return 0
    ctx   = _ctx_from_ast_arg_list(args)
    if ctx is None:
        return _reduce(lambda a, b: a + b, args, 0)
    args  = _coerce_expr_list(args, ctx)
    if is_bv(args[0]):
        return _reduce(lambda a, b: a + b, args, 0)
    else:
        _args, sz = _to_ast_array(args)
        return ArithRef(Z3_mk_add(ctx.ref(), sz, _args), ctx)


def Product(*args):
    """Create the product of the Z3 expressions.

    >>> a, b, c = Ints('a b c')
    >>> Product(a, b, c)
    a*b*c
    >>> Product([a, b, c])
    a*b*c
    >>> A = IntVector('a', 5)
    >>> Product(A)
    a__0*a__1*a__2*a__3*a__4
    """
    args  = _get_args(args)
    if len(args) == 0:
        return 1
    ctx   = _ctx_from_ast_arg_list(args)
    if ctx is None:
        return _reduce(lambda a, b: a * b, args, 1)    
    args  = _coerce_expr_list(args, ctx)
    if is_bv(args[0]):
        return _reduce(lambda a, b: a * b, args, 1)
    else:
        _args, sz = _to_ast_array(args)
        return ArithRef(Z3_mk_mul(ctx.ref(), sz, _args), ctx)

def AtMost(*args):
    """Create an at-most Pseudo-Boolean k constraint.

    >>> a, b, c = Bools('a b c')
    >>> f = AtMost(a, b, c, 2)
    """
    args  = _get_args(args)
    if __debug__:
        _z3_assert(len(args) > 1, "Non empty list of arguments expected")
    ctx   = _ctx_from_ast_arg_list(args)
    if __debug__:
        _z3_assert(ctx is not None, "At least one of the arguments must be a Z3 expression")
    args1 = _coerce_expr_list(args[:-1], ctx)
    k = args[-1]
    _args, sz = _to_ast_array(args1)
    return BoolRef(Z3_mk_atmost(ctx.ref(), sz, _args, k), ctx)

def AtLeast(*args):
    """Create an at-most Pseudo-Boolean k constraint.

    >>> a, b, c = Bools('a b c')
    >>> f = AtLeast(a, b, c, 2)
    """
    args  = _get_args(args)
    if __debug__:
        _z3_assert(len(args) > 1, "Non empty list of arguments expected")
    ctx   = _ctx_from_ast_arg_list(args)
    if __debug__:
        _z3_assert(ctx is not None, "At least one of the arguments must be a Z3 expression")
    args1 = _coerce_expr_list(args[:-1], ctx)
    k = args[-1]
    _args, sz = _to_ast_array(args1)
    return BoolRef(Z3_mk_atleast(ctx.ref(), sz, _args, k), ctx)


def _pb_args_coeffs(args, default_ctx = None):
    args  = _get_args_ast_list(args)
    if len(args) == 0:
       return _get_ctx(default_ctx), 0, (Ast * 0)(), (ctypes.c_int * 0)()
    args, coeffs = zip(*args)
    if __debug__:
        _z3_assert(len(args) > 0, "Non empty list of arguments expected")
    ctx   = _ctx_from_ast_arg_list(args)
    if __debug__:
        _z3_assert(ctx is not None, "At least one of the arguments must be a Z3 expression")
    args = _coerce_expr_list(args, ctx)
    _args, sz = _to_ast_array(args)
    _coeffs = (ctypes.c_int * len(coeffs))()
    for i in range(len(coeffs)):
        _z3_check_cint_overflow(coeffs[i], "coefficient")
        _coeffs[i] = coeffs[i]
    return ctx, sz, _args, _coeffs

def PbLe(args, k):
    """Create a Pseudo-Boolean inequality k constraint.

    >>> a, b, c = Bools('a b c')
    >>> f = PbLe(((a,1),(b,3),(c,2)), 3)
    """
    _z3_check_cint_overflow(k, "k")
    ctx, sz, _args, _coeffs = _pb_args_coeffs(args)
    return BoolRef(Z3_mk_pble(ctx.ref(), sz, _args, _coeffs, k), ctx)

def PbGe(args, k):
    """Create a Pseudo-Boolean inequality k constraint.

    >>> a, b, c = Bools('a b c')
    >>> f = PbGe(((a,1),(b,3),(c,2)), 3)
    """
    _z3_check_cint_overflow(k, "k")
    ctx, sz, _args, _coeffs = _pb_args_coeffs(args)
    return BoolRef(Z3_mk_pbge(ctx.ref(), sz, _args, _coeffs, k), ctx)

def PbEq(args, k, ctx = None):
    """Create a Pseudo-Boolean inequality k constraint.

    >>> a, b, c = Bools('a b c')
    >>> f = PbEq(((a,1),(b,3),(c,2)), 3)
    """
    _z3_check_cint_overflow(k, "k")
    ctx, sz, _args, _coeffs = _pb_args_coeffs(args)
    return BoolRef(Z3_mk_pbeq(ctx.ref(), sz, _args, _coeffs, k), ctx)


def solve(*args, **keywords):
    """Solve the constraints `*args`.

    This is a simple function for creating demonstrations. It creates a solver,
    configure it using the options in `keywords`, adds the constraints
    in `args`, and invokes check.

    >>> a = Int('a')
    >>> solve(a > 0, a < 2)
    [a = 1]
    """
    s = Solver()
    s.set(**keywords)
    s.add(*args)
    if keywords.get('show', False):
        print(s)
    r = s.check()
    if r == unsat:
        print("no solution")
    elif r == unknown:
        print("failed to solve")
        try:
            print(s.model())
        except Z3Exception:
            return
    else:
        print(s.model())

def solve_using(s, *args, **keywords):
    """Solve the constraints `*args` using solver `s`.

    This is a simple function for creating demonstrations. It is similar to `solve`,
    but it uses the given solver `s`.
    It configures solver `s` using the options in `keywords`, adds the constraints
    in `args`, and invokes check.
    """
    if __debug__:
        _z3_assert(isinstance(s, Solver), "Solver object expected")
    s.set(**keywords)
    s.add(*args)
    if keywords.get('show', False):
        print("Problem:")
        print(s)
    r = s.check()
    if r == unsat:
        print("no solution")
    elif r == unknown:
        print("failed to solve")
        try:
            print(s.model())
        except Z3Exception:
            return
    else:
        if keywords.get('show', False):
            print("Solution:")
        print(s.model())

def prove(claim, **keywords):
    """Try to prove the given claim.

    This is a simple function for creating demonstrations.  It tries to prove
    `claim` by showing the negation is unsatisfiable.

    >>> p, q = Bools('p q')
    >>> prove(Not(And(p, q)) == Or(Not(p), Not(q)))
    proved
    """
    if __debug__:
        _z3_assert(is_bool(claim), "Z3 Boolean expression expected")
    s = Solver()
    s.set(**keywords)
    s.add(Not(claim))
    if keywords.get('show', False):
        print(s)
    r = s.check()
    if r == unsat:
        print("proved")
    elif r == unknown:
        print("failed to prove")
        print(s.model())
    else:
        print("counterexample")
        print(s.model())

def _solve_html(*args, **keywords):
    """Version of funcion `solve` used in RiSE4Fun."""
    s = Solver()
    s.set(**keywords)
    s.add(*args)
    if keywords.get('show', False):
        print("<b>Problem:</b>")
        print(s)
    r = s.check()
    if r == unsat:
        print("<b>no solution</b>")
    elif r == unknown:
        print("<b>failed to solve</b>")
        try:
            print(s.model())
        except Z3Exception:
            return
    else:
        if keywords.get('show', False):
            print("<b>Solution:</b>")
        print(s.model())

def _solve_using_html(s, *args, **keywords):
    """Version of funcion `solve_using` used in RiSE4Fun."""
    if __debug__:
        _z3_assert(isinstance(s, Solver), "Solver object expected")
    s.set(**keywords)
    s.add(*args)
    if keywords.get('show', False):
        print("<b>Problem:</b>")
        print(s)
    r = s.check()
    if r == unsat:
        print("<b>no solution</b>")
    elif r == unknown:
        print("<b>failed to solve</b>")
        try:
            print(s.model())
        except Z3Exception:
            return
    else:
        if keywords.get('show', False):
            print("<b>Solution:</b>")
        print(s.model())

def _prove_html(claim, **keywords):
    """Version of funcion `prove` used in RiSE4Fun."""
    if __debug__:
        _z3_assert(is_bool(claim), "Z3 Boolean expression expected")
    s = Solver()
    s.set(**keywords)
    s.add(Not(claim))
    if keywords.get('show', False):
        print(s)
    r = s.check()
    if r == unsat:
        print("<b>proved</b>")
    elif r == unknown:
        print("<b>failed to prove</b>")
        print(s.model())
    else:
        print("<b>counterexample</b>")
        print(s.model())

def _dict2sarray(sorts, ctx):
    sz = len(sorts)
    _names = (Symbol * sz)()
    _sorts = (Sort * sz) ()
    i = 0
    for k in sorts:
        v = sorts[k]
        if __debug__:
            _z3_assert(isinstance(k, str), "String expected")
            _z3_assert(is_sort(v), "Z3 sort expected")
        _names[i] = to_symbol(k, ctx)
        _sorts[i] = v.ast
        i = i + 1
    return sz, _names, _sorts

def _dict2darray(decls, ctx):
    sz = len(decls)
    _names = (Symbol * sz)()
    _decls = (FuncDecl * sz) ()
    i = 0
    for k in decls:
        v = decls[k]
        if __debug__:
            _z3_assert(isinstance(k, str), "String expected")
            _z3_assert(is_func_decl(v) or is_const(v), "Z3 declaration or constant expected")
        _names[i] = to_symbol(k, ctx)
        if is_const(v):
            _decls[i] = v.decl().ast
        else:
            _decls[i] = v.ast
        i = i + 1
    return sz, _names, _decls


def parse_smt2_string(s, sorts={}, decls={}, ctx=None):
    """Parse a string in SMT 2.0 format using the given sorts and decls.

    The arguments sorts and decls are Python dictionaries used to initialize
    the symbol table used for the SMT 2.0 parser.

    >>> parse_smt2_string('(declare-const x Int) (assert (> x 0)) (assert (< x 10))')
    [x > 0, x < 10]
    >>> x, y = Ints('x y')
    >>> f = Function('f', IntSort(), IntSort())
    >>> parse_smt2_string('(assert (> (+ foo (g bar)) 0))', decls={ 'foo' : x, 'bar' : y, 'g' : f})
    [x + f(y) > 0]
    >>> parse_smt2_string('(declare-const a U) (assert (> a 0))', sorts={ 'U' : IntSort() })
    [a > 0]
    """
    ctx = _get_ctx(ctx)
    ssz, snames, ssorts = _dict2sarray(sorts, ctx)
    dsz, dnames, ddecls = _dict2darray(decls, ctx)
    return AstVector(Z3_parse_smtlib2_string(ctx.ref(), s, ssz, snames, ssorts, dsz, dnames, ddecls), ctx)

def parse_smt2_file(f, sorts={}, decls={}, ctx=None):
    """Parse a file in SMT 2.0 format using the given sorts and decls.

    This function is similar to parse_smt2_string().
    """
    ctx = _get_ctx(ctx)
    ssz, snames, ssorts = _dict2sarray(sorts, ctx)
    dsz, dnames, ddecls = _dict2darray(decls, ctx)
    return AstVector(Z3_parse_smtlib2_file(ctx.ref(), f, ssz, snames, ssorts, dsz, dnames, ddecls), ctx)


#########################################
#
# Floating-Point Arithmetic
#
#########################################


# Global default rounding mode
_dflt_rounding_mode = Z3_OP_FPA_RM_TOWARD_ZERO
_dflt_fpsort_ebits = 11
_dflt_fpsort_sbits = 53

def get_default_rounding_mode(ctx=None):
    """Retrieves the global default rounding mode."""
    global _dflt_rounding_mode
    if _dflt_rounding_mode == Z3_OP_FPA_RM_TOWARD_ZERO:
        return RTZ(ctx)
    elif _dflt_rounding_mode == Z3_OP_FPA_RM_TOWARD_NEGATIVE:
        return RTN(ctx)
    elif _dflt_rounding_mode == Z3_OP_FPA_RM_TOWARD_POSITIVE:
        return RTP(ctx)
    elif _dflt_rounding_mode == Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN:
        return RNE(ctx)
    elif _dflt_rounding_mode == Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY:
        return RNA(ctx)

def set_default_rounding_mode(rm, ctx=None):
    global _dflt_rounding_mode
    if is_fprm_value(rm):
        _dflt_rounding_mode = rm.decl().kind()
    else:
        _z3_assert(_dflt_rounding_mode == Z3_OP_FPA_RM_TOWARD_ZERO or
                   _dflt_rounding_mode == Z3_OP_FPA_RM_TOWARD_NEGATIVE or
                   _dflt_rounding_mode == Z3_OP_FPA_RM_TOWARD_POSITIVE or
                   _dflt_rounding_mode == Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN or
                   _dflt_rounding_mode == Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY,
                   "illegal rounding mode")
        _dflt_rounding_mode = rm

def get_default_fp_sort(ctx=None):
    return FPSort(_dflt_fpsort_ebits, _dflt_fpsort_sbits, ctx)

def set_default_fp_sort(ebits, sbits, ctx=None):
    global _dflt_fpsort_ebits
    global _dflt_fpsort_sbits
    _dflt_fpsort_ebits = ebits
    _dflt_fpsort_sbits = sbits

def _dflt_rm(ctx=None):
    return get_default_rounding_mode(ctx)

def _dflt_fps(ctx=None):
    return get_default_fp_sort(ctx)

def _coerce_fp_expr_list(alist, ctx):
    first_fp_sort = None
    for a in alist:
        if is_fp(a):
            if first_fp_sort is None:
                first_fp_sort = a.sort()
            elif first_fp_sort == a.sort():
                pass # OK, same as before
            else:
                # we saw at least 2 different float sorts; something will
                # throw a sort mismatch later, for now assume None.
                first_fp_sort = None
                break

    r = []
    for i in range(len(alist)):
        a = alist[i]
        if (isinstance(a, str) and a.contains('2**(') and a.endswith(')')) or _is_int(a) or isinstance(a, float) or isinstance(a, bool):
            r.append(FPVal(a, None, first_fp_sort, ctx))
        else:
            r.append(a)
    return _coerce_expr_list(r, ctx)


### FP Sorts

class FPSortRef(SortRef):
    """Floating-point sort."""

    def ebits(self):
       """Retrieves the number of bits reserved for the exponent in the FloatingPoint sort `self`.
       >>> b = FPSort(8, 24)
       >>> b.ebits()
       8
       """
       return int(Z3_fpa_get_ebits(self.ctx_ref(), self.ast))

    def sbits(self):
       """Retrieves the number of bits reserved for the significand in the FloatingPoint sort `self`.
       >>> b = FPSort(8, 24)
       >>> b.sbits()
       24
       """
       return int(Z3_fpa_get_sbits(self.ctx_ref(), self.ast))

    def cast(self, val):
        """Try to cast `val` as a floating-point expression.
        >>> b = FPSort(8, 24)
        >>> b.cast(1.0)
        1
        >>> b.cast(1.0).sexpr()
        '(fp #b0 #x7f #b00000000000000000000000)'
        """
        if is_expr(val):
            if __debug__:
                _z3_assert(self.ctx == val.ctx, "Context mismatch")
            return val
        else:
            return FPVal(val, None, self, self.ctx)


def Float16(ctx=None):
    """Floating-point 16-bit (half) sort."""
    ctx = _get_ctx(ctx)
    return FPSortRef(Z3_mk_fpa_sort_16(ctx.ref()), ctx)

def FloatHalf(ctx=None):
    """Floating-point 16-bit (half) sort."""
    ctx = _get_ctx(ctx)
    return FPSortRef(Z3_mk_fpa_sort_half(ctx.ref()), ctx)

def Float32(ctx=None):
    """Floating-point 32-bit (single) sort."""
    ctx = _get_ctx(ctx)
    return FPSortRef(Z3_mk_fpa_sort_32(ctx.ref()), ctx)

def FloatSingle(ctx=None):
    """Floating-point 32-bit (single) sort."""
    ctx = _get_ctx(ctx)
    return FPSortRef(Z3_mk_fpa_sort_single(ctx.ref()), ctx)

def Float64(ctx=None):
    """Floating-point 64-bit (double) sort."""
    ctx = _get_ctx(ctx)
    return FPSortRef(Z3_mk_fpa_sort_64(ctx.ref()), ctx)

def FloatDouble(ctx=None):
    """Floating-point 64-bit (double) sort."""
    ctx = _get_ctx(ctx)
    return FPSortRef(Z3_mk_fpa_sort_double(ctx.ref()), ctx)

def Float128(ctx=None):
    """Floating-point 128-bit (quadruple) sort."""
    ctx = _get_ctx(ctx)
    return FPSortRef(Z3_mk_fpa_sort_128(ctx.ref()), ctx)

def FloatQuadruple(ctx=None):
    """Floating-point 128-bit (quadruple) sort."""
    ctx = _get_ctx(ctx)
    return FPSortRef(Z3_mk_fpa_sort_quadruple(ctx.ref()), ctx)

class FPRMSortRef(SortRef):
    """"Floating-point rounding mode sort."""


def is_fp_sort(s):
    """Return True if `s` is a Z3 floating-point sort.

    >>> is_fp_sort(FPSort(8, 24))
    True
    >>> is_fp_sort(IntSort())
    False
    """
    return isinstance(s, FPSortRef)

def is_fprm_sort(s):
    """Return True if `s` is a Z3 floating-point rounding mode sort.

    >>> is_fprm_sort(FPSort(8, 24))
    False
    >>> is_fprm_sort(RNE().sort())
    True
    """
    return isinstance(s, FPRMSortRef)

### FP Expressions

class FPRef(ExprRef):
    """Floating-point expressions."""

    def sort(self):
        """Return the sort of the floating-point expression `self`.

        >>> x = FP('1.0', FPSort(8, 24))
        >>> x.sort()
        FPSort(8, 24)
        >>> x.sort() == FPSort(8, 24)
        True
        """
        return FPSortRef(Z3_get_sort(self.ctx_ref(), self.as_ast()), self.ctx)

    def ebits(self):
       """Retrieves the number of bits reserved for the exponent in the FloatingPoint expression `self`.
       >>> b = FPSort(8, 24)
       >>> b.ebits()
       8
       """
       return self.sort().ebits();

    def sbits(self):
       """Retrieves the number of bits reserved for the exponent in the FloatingPoint expression `self`.
       >>> b = FPSort(8, 24)
       >>> b.sbits()
       24
       """
       return self.sort().sbits();

    def as_string(self):
        """Return a Z3 floating point expression as a Python string."""
        return Z3_ast_to_string(self.ctx_ref(), self.as_ast())

    def __le__(self, other):
        return fpLEQ(self, other, self.ctx)

    def __lt__(self, other):
        return fpLT(self, other, self.ctx)

    def __ge__(self, other):
        return fpGEQ(self, other, self.ctx)

    def __gt__(self, other):
        return fpGT(self, other, self.ctx)

    def __add__(self, other):
        """Create the Z3 expression `self + other`.

        >>> x = FP('x', FPSort(8, 24))
        >>> y = FP('y', FPSort(8, 24))
        >>> x + y
        x + y
        >>> (x + y).sort()
        FPSort(8, 24)
        """
        [a, b] = _coerce_fp_expr_list([self, other], self.ctx)
        return fpAdd(_dflt_rm(), a, b, self.ctx)

    def __radd__(self, other):
        """Create the Z3 expression `other + self`.

        >>> x = FP('x', FPSort(8, 24))
        >>> 10 + x
        1.25*(2**3) + x
        """
        [a, b] = _coerce_fp_expr_list([other, self], self.ctx)
        return fpAdd(_dflt_rm(), a, b, self.ctx)

    def __sub__(self, other):
        """Create the Z3 expression `self - other`.

        >>> x = FP('x', FPSort(8, 24))
        >>> y = FP('y', FPSort(8, 24))
        >>> x - y
        x - y
        >>> (x - y).sort()
        FPSort(8, 24)
        """
        [a, b] = _coerce_fp_expr_list([self, other], self.ctx)
        return fpSub(_dflt_rm(), a, b, self.ctx)

    def __rsub__(self, other):
        """Create the Z3 expression `other - self`.

        >>> x = FP('x', FPSort(8, 24))
        >>> 10 - x
        1.25*(2**3) - x
        """
        [a, b] = _coerce_fp_expr_list([other, self], self.ctx)
        return fpSub(_dflt_rm(), a, b, self.ctx)

    def __mul__(self, other):
        """Create the Z3 expression `self * other`.

        >>> x = FP('x', FPSort(8, 24))
        >>> y = FP('y', FPSort(8, 24))
        >>> x * y
        x * y
        >>> (x * y).sort()
        FPSort(8, 24)
        >>> 10 * y
        1.25*(2**3) * y
        """
        [a, b] = _coerce_fp_expr_list([self, other], self.ctx)
        return fpMul(_dflt_rm(), a, b, self.ctx)

    def __rmul__(self, other):
        """Create the Z3 expression `other * self`.

        >>> x = FP('x', FPSort(8, 24))
        >>> y = FP('y', FPSort(8, 24))
        >>> x * y
        x * y
        >>> x * 10
        x * 1.25*(2**3)
        """
        [a, b] = _coerce_fp_expr_list([other, self], self.ctx)
        return fpMul(_dflt_rm(), a, b, self.ctx)

    def __pos__(self):
        """Create the Z3 expression `+self`."""
        return self

    def __neg__(self):
        """Create the Z3 expression `-self`.
        
        >>> x = FP('x', Float32())
        >>> -x
        -x
        """
        return fpNeg(self)

    def __div__(self, other):
        """Create the Z3 expression `self / other`.

        >>> x = FP('x', FPSort(8, 24))
        >>> y = FP('y', FPSort(8, 24))
        >>> x / y
        x / y
        >>> (x / y).sort()
        FPSort(8, 24)
        >>> 10 / y
        1.25*(2**3) / y
        """
        [a, b] = _coerce_fp_expr_list([self, other], self.ctx)
        return fpDiv(_dflt_rm(), a, b, self.ctx)

    def __rdiv__(self, other):
        """Create the Z3 expression `other / self`.

        >>> x = FP('x', FPSort(8, 24))
        >>> y = FP('y', FPSort(8, 24))
        >>> x / y
        x / y
        >>> x / 10
        x / 1.25*(2**3)
        """
        [a, b] = _coerce_fp_expr_list([other, self], self.ctx)
        return fpDiv(_dflt_rm(), a, b, self.ctx)

    if not sys.version < '3':
        def __truediv__(self, other):
            """Create the Z3 expression division `self / other`."""
            return self.__div__(other)

        def __rtruediv__(self, other):
            """Create the Z3 expression division `other / self`."""
            return self.__rdiv__(other)

    def __mod__(self, other):
        """Create the Z3 expression mod `self % other`."""
        return fpRem(self, other)

    def __rmod__(self, other):
        """Create the Z3 expression mod `other % self`."""
        return fpRem(other, self)

class FPRMRef(ExprRef):
    """Floating-point rounding mode expressions"""

    def as_string(self):
        """Return a Z3 floating point expression as a Python string."""
        return Z3_ast_to_string(self.ctx_ref(), self.as_ast())


def RoundNearestTiesToEven(ctx=None):
    ctx = _get_ctx(ctx)
    return FPRMRef(Z3_mk_fpa_round_nearest_ties_to_even(ctx.ref()), ctx)

def RNE (ctx=None):
    ctx = _get_ctx(ctx)
    return FPRMRef(Z3_mk_fpa_round_nearest_ties_to_even(ctx.ref()), ctx)

def RoundNearestTiesToAway(ctx=None):
    ctx = _get_ctx(ctx)
    return FPRMRef(Z3_mk_fpa_round_nearest_ties_to_away(ctx.ref()), ctx)

def RNA (ctx=None):
    ctx = _get_ctx(ctx)
    return FPRMRef(Z3_mk_fpa_round_nearest_ties_to_away(ctx.ref()), ctx)

def RoundTowardPositive(ctx=None):
    ctx = _get_ctx(ctx)
    return FPRMRef(Z3_mk_fpa_round_toward_positive(ctx.ref()), ctx)

def RTP(ctx=None):
    ctx = _get_ctx(ctx)
    return FPRMRef(Z3_mk_fpa_round_toward_positive(ctx.ref()), ctx)

def RoundTowardNegative(ctx=None):
    ctx = _get_ctx(ctx)
    return FPRMRef(Z3_mk_fpa_round_toward_negative(ctx.ref()), ctx)

def RTN(ctx=None):
    ctx = _get_ctx(ctx)
    return FPRMRef(Z3_mk_fpa_round_toward_negative(ctx.ref()), ctx)

def RoundTowardZero(ctx=None):
    ctx = _get_ctx(ctx)
    return FPRMRef(Z3_mk_fpa_round_toward_zero(ctx.ref()), ctx)

def RTZ(ctx=None):
    ctx = _get_ctx(ctx)
    return FPRMRef(Z3_mk_fpa_round_toward_zero(ctx.ref()), ctx)

def is_fprm(a):
    """Return `True` if `a` is a Z3 floating-point rounding mode expression.

    >>> rm = RNE()
    >>> is_fprm(rm)
    True
    >>> rm = 1.0
    >>> is_fprm(rm)
    False
    """
    return isinstance(a, FPRMRef)

def is_fprm_value(a):
    """Return `True` if `a` is a Z3 floating-point rounding mode numeral value."""
    return is_fprm(a) and _is_numeral(a.ctx, a.ast)

### FP Numerals

class FPNumRef(FPRef):   
    """The sign of the numeral.

    >>> x = FPVal(+1.0, FPSort(8, 24))
    >>> x.sign()
    False
    >>> x = FPVal(-1.0, FPSort(8, 24))
    >>> x.sign()
    True
    """
    def sign(self):
        l = (ctypes.c_int)()
        if Z3_fpa_get_numeral_sign(self.ctx.ref(), self.as_ast(), byref(l)) == False:
            raise Z3Exception("error retrieving the sign of a numeral.")
        return l.value != 0

    """The sign of a floating-point numeral as a bit-vector expression.
    
    Remark: NaN's are invalid arguments.
    """
    def sign_as_bv(self):
        return BitVecNumRef(Z3_fpa_get_numeral_sign_bv(self.ctx.ref(), self.as_ast()), self.ctx)

    """The significand of the numeral.

    >>> x = FPVal(2.5, FPSort(8, 24))
    >>> x.significand()
    1.25
    """
    def significand(self):
        return Z3_fpa_get_numeral_significand_string(self.ctx.ref(), self.as_ast())

    """The significand of the numeral as a long.

    >>> x = FPVal(2.5, FPSort(8, 24))
    >>> x.significand_as_long()
    1.25
    """
    def significand_as_long(self):
        ptr = (ctypes.c_ulonglong * 1)()
        if not Z3_fpa_get_numeral_significand_uint64(self.ctx.ref(), self.as_ast(), ptr):
            raise Z3Exception("error retrieving the significand of a numeral.")
        return ptr[0]
    
    """The significand of the numeral as a bit-vector expression.

    Remark: NaN are invalid arguments.
    """
    def significand_as_bv(self):
        return BitVecNumRef(Z3_fpa_get_numeral_significand_bv(self.ctx.ref(), self.as_ast()), self.ctx)

    """The exponent of the numeral.

    >>> x = FPVal(2.5, FPSort(8, 24))
    >>> x.exponent()
    1
    """
    def exponent(self, biased=True):
        return Z3_fpa_get_numeral_exponent_string(self.ctx.ref(), self.as_ast(), biased)

    """The exponent of the numeral as a long.

    >>> x = FPVal(2.5, FPSort(8, 24))
    >>> x.exponent_as_long()
    1
    """
    def exponent_as_long(self, biased=True):
        ptr = (ctypes.c_longlong * 1)()
        if not Z3_fpa_get_numeral_exponent_int64(self.ctx.ref(), self.as_ast(), ptr, biased):
            raise Z3Exception("error retrieving the exponent of a numeral.")
        return ptr[0]

    """The exponent of the numeral as a bit-vector expression.

    Remark: NaNs are invalid arguments.
    """
    def exponent_as_bv(self, biased=True):
        return BitVecNumRef(Z3_fpa_get_numeral_exponent_bv(self.ctx.ref(), self.as_ast(), biased), self.ctx)

    """Indicates whether the numeral is a NaN."""
    def isNaN(self):
        return Z3_fpa_is_numeral_nan(self.ctx.ref(), self.as_ast())

    """Indicates whether the numeral is +oo or -oo."""
    def isInf(self):
        return Z3_fpa_is_numeral_inf(self.ctx.ref(), self.as_ast())

    """Indicates whether the numeral is +zero or -zero."""
    def isZero(self):
        return Z3_fpa_is_numeral_zero(self.ctx.ref(), self.as_ast())

    """Indicates whether the numeral is normal."""
    def isNormal(self):
        return Z3_fpa_is_numeral_normal(self.ctx.ref(), self.as_ast())

    """Indicates whether the numeral is subnormal."""
    def isSubnormal(self):
        return Z3_fpa_is_numeral_subnormal(self.ctx.ref(), self.as_ast())

    """Indicates whether the numeral is positive."""
    def isPositive(self):
        return Z3_fpa_is_numeral_positive(self.ctx.ref(), self.as_ast())

    """Indicates whether the numeral is negative."""
    def isNegative(self):
        return Z3_fpa_is_numeral_negative(self.ctx.ref(), self.as_ast())

    """
    The string representation of the numeral.

    >>> x = FPVal(20, FPSort(8, 24))
    >>> x.as_string()
    1.25*(2**4)
    """
    def as_string(self):
        s = Z3_get_numeral_string(self.ctx.ref(), self.as_ast())
        return ("FPVal(%s, %s)" % (s, self.sort()))

def is_fp(a):
    """Return `True` if `a` is a Z3 floating-point expression.

    >>> b = FP('b', FPSort(8, 24))
    >>> is_fp(b)
    True
    >>> is_fp(b + 1.0)
    True
    >>> is_fp(Int('x'))
    False
    """
    return isinstance(a, FPRef)

def is_fp_value(a):
    """Return `True` if `a` is a Z3 floating-point numeral value.

    >>> b = FP('b', FPSort(8, 24))
    >>> is_fp_value(b)
    False
    >>> b = FPVal(1.0, FPSort(8, 24))
    >>> b
    1
    >>> is_fp_value(b)
    True
    """
    return is_fp(a) and _is_numeral(a.ctx, a.ast)

def FPSort(ebits, sbits, ctx=None):
    """Return a Z3 floating-point sort of the given sizes. If `ctx=None`, then the global context is used.

    >>> Single = FPSort(8, 24)
    >>> Double = FPSort(11, 53)
    >>> Single
    FPSort(8, 24)
    >>> x = Const('x', Single)
    >>> eq(x, FP('x', FPSort(8, 24)))
    True
    """
    ctx = _get_ctx(ctx)
    return FPSortRef(Z3_mk_fpa_sort(ctx.ref(), ebits, sbits), ctx)

def _to_float_str(val, exp=0):
    if isinstance(val, float):
        if math.isnan(val):
            res = "NaN"
        elif val == 0.0:
            sone = math.copysign(1.0, val)
            if sone < 0.0:
                return "-0.0"
            else:
                return "+0.0"
        elif val == float("+inf"):
            res = "+oo"
        elif val == float("-inf"):
            res = "-oo"
        else:
            v = val.as_integer_ratio()
            num = v[0]
            den = v[1]
            rvs = str(num) + '/' + str(den)
            res = rvs + 'p' + _to_int_str(exp)
    elif isinstance(val, bool):
        if val:
            res = "1.0"
        else:
            res = "0.0"
    elif _is_int(val):
        res = str(val)
    elif isinstance(val, str):
        inx = val.find('*(2**')
        if inx == -1:
            res = val
        elif val[-1] == ')':
            res = val[0:inx]
            exp = str(int(val[inx+5:-1]) + int(exp))
        else:
            _z3_assert(False, "String does not have floating-point numeral form.")
    elif __debug__:
        _z3_assert(False, "Python value cannot be used to create floating-point numerals.")
    if exp == 0:
        return res
    else:
        return res + 'p' + exp


def fpNaN(s):
    """Create a Z3 floating-point NaN term.

    >>> s = FPSort(8, 24)
    >>> set_fpa_pretty(True)
    >>> fpNaN(s)
    NaN
    >>> pb = get_fpa_pretty()
    >>> set_fpa_pretty(False)
    >>> fpNaN(s)
    fpNaN(FPSort(8, 24))
    >>> set_fpa_pretty(pb)
    """
    _z3_assert(isinstance(s, FPSortRef), "sort mismatch")
    return FPNumRef(Z3_mk_fpa_nan(s.ctx_ref(), s.ast), s.ctx)

def fpPlusInfinity(s):
    """Create a Z3 floating-point +oo term.

    >>> s = FPSort(8, 24)
    >>> pb = get_fpa_pretty()
    >>> set_fpa_pretty(True)
    >>> fpPlusInfinity(s)
    +oo
    >>> set_fpa_pretty(False)
    >>> fpPlusInfinity(s)
    fpPlusInfinity(FPSort(8, 24))
    >>> set_fpa_pretty(pb)
    """
    _z3_assert(isinstance(s, FPSortRef), "sort mismatch")
    return FPNumRef(Z3_mk_fpa_inf(s.ctx_ref(), s.ast, False), s.ctx)

def fpMinusInfinity(s):
    """Create a Z3 floating-point -oo term."""
    _z3_assert(isinstance(s, FPSortRef), "sort mismatch")
    return FPNumRef(Z3_mk_fpa_inf(s.ctx_ref(), s.ast, True), s.ctx)

def fpInfinity(s, negative):
    """Create a Z3 floating-point +oo or -oo term."""
    _z3_assert(isinstance(s, FPSortRef), "sort mismatch")
    _z3_assert(isinstance(negative, bool), "expected Boolean flag")
    return FPNumRef(Z3_mk_fpa_inf(s.ctx_ref(), s.ast, negative), s.ctx)

def fpPlusZero(s):
    """Create a Z3 floating-point +0.0 term."""
    _z3_assert(isinstance(s, FPSortRef), "sort mismatch")
    return FPNumRef(Z3_mk_fpa_zero(s.ctx_ref(), s.ast, False), s.ctx)

def fpMinusZero(s):
    """Create a Z3 floating-point -0.0 term."""
    _z3_assert(isinstance(s, FPSortRef), "sort mismatch")
    return FPNumRef(Z3_mk_fpa_zero(s.ctx_ref(), s.ast, True), s.ctx)

def fpZero(s, negative):
    """Create a Z3 floating-point +0.0 or -0.0 term."""
    _z3_assert(isinstance(s, FPSortRef), "sort mismatch")
    _z3_assert(isinstance(negative, bool), "expected Boolean flag")
    return FPNumRef(Z3_mk_fpa_zero(s.ctx_ref(), s.ast, negative), s.ctx)

def FPVal(sig, exp=None, fps=None, ctx=None):
    """Return a floating-point value of value `val` and sort `fps`. If `ctx=None`, then the global context is used.

    >>> v = FPVal(20.0, FPSort(8, 24))
    >>> v
    1.25*(2**4)
    >>> print("0x%.8x" % v.exponent_as_long(False))
    0x00000004
    >>> v = FPVal(2.25, FPSort(8, 24))
    >>> v
    1.125*(2**1)
    >>> v = FPVal(-2.25, FPSort(8, 24))
    >>> v
    -1.125*(2**1)
    >>> FPVal(-0.0, FPSort(8, 24))
    -0.0
    >>> FPVal(0.0, FPSort(8, 24))
    +0.0
    >>> FPVal(+0.0, FPSort(8, 24))
    +0.0
    """
    ctx = _get_ctx(ctx)
    if is_fp_sort(exp):
        fps = exp
        exp = None
    elif fps is None:
        fps = _dflt_fps(ctx)
    _z3_assert(is_fp_sort(fps), "sort mismatch")
    if exp is None:
        exp = 0
    val = _to_float_str(sig)
    if val == "NaN" or val == "nan":
        return fpNaN(fps)
    elif val == "-0.0":
        return fpMinusZero(fps)
    elif val == "0.0" or val == "+0.0":
        return fpPlusZero(fps)
    elif val == "+oo" or val == "+inf" or val == "+Inf":
        return fpPlusInfinity(fps)
    elif val == "-oo" or val == "-inf" or val == "-Inf":
        return fpMinusInfinity(fps)
    else:
        return FPNumRef(Z3_mk_numeral(ctx.ref(), val, fps.ast), ctx)

def FP(name, fpsort, ctx=None):
    """Return a floating-point constant named `name`.
    `fpsort` is the floating-point sort.
    If `ctx=None`, then the global context is used.

    >>> x  = FP('x', FPSort(8, 24))
    >>> is_fp(x)
    True
    >>> x.ebits()
    8
    >>> x.sort()
    FPSort(8, 24)
    >>> word = FPSort(8, 24)
    >>> x2 = FP('x', word)
    >>> eq(x, x2)
    True
    """
    if isinstance(fpsort, FPSortRef) and ctx is None:
        ctx = fpsort.ctx
    else:
        ctx = _get_ctx(ctx)
    return FPRef(Z3_mk_const(ctx.ref(), to_symbol(name, ctx), fpsort.ast), ctx)

def FPs(names, fpsort, ctx=None):
    """Return an array of floating-point constants.

    >>> x, y, z = FPs('x y z', FPSort(8, 24))
    >>> x.sort()
    FPSort(8, 24)
    >>> x.sbits()
    24
    >>> x.ebits()
    8
    >>> fpMul(RNE(), fpAdd(RNE(), x, y), z)
    fpMul(RNE(), fpAdd(RNE(), x, y), z)
    """
    ctx = _get_ctx(ctx)
    if isinstance(names, str):
        names = names.split(" ")
    return [FP(name, fpsort, ctx) for name in names]

def fpAbs(a, ctx=None):
    """Create a Z3 floating-point absolute value expression.

    >>> s = FPSort(8, 24)
    >>> rm = RNE()
    >>> x = FPVal(1.0, s)
    >>> fpAbs(x)
    fpAbs(1)
    >>> y = FPVal(-20.0, s)
    >>> y
    -1.25*(2**4)
    >>> fpAbs(y)
    fpAbs(-1.25*(2**4))
    >>> fpAbs(-1.25*(2**4))
    fpAbs(-1.25*(2**4))
    >>> fpAbs(x).sort()
    FPSort(8, 24)
    """
    ctx = _get_ctx(ctx)
    [a] = _coerce_fp_expr_list([a], ctx)
    return FPRef(Z3_mk_fpa_abs(ctx.ref(), a.as_ast()), ctx)

def fpNeg(a, ctx=None):
    """Create a Z3 floating-point addition expression.

    >>> s = FPSort(8, 24)
    >>> rm = RNE()
    >>> x = FP('x', s)
    >>> fpNeg(x)
    -x
    >>> fpNeg(x).sort()
    FPSort(8, 24)
    """
    ctx = _get_ctx(ctx)
    [a] = _coerce_fp_expr_list([a], ctx)
    return FPRef(Z3_mk_fpa_neg(ctx.ref(), a.as_ast()), ctx)

def _mk_fp_unary(f, rm, a, ctx):
    ctx = _get_ctx(ctx)
    [a] = _coerce_fp_expr_list([a], ctx)
    if __debug__:
        _z3_assert(is_fprm(rm), "First argument must be a Z3 floating-point rounding mode expression")
        _z3_assert(is_fp(a), "Second argument must be a Z3 floating-point expression")
    return FPRef(f(ctx.ref(), rm.as_ast(), a.as_ast()), ctx)

def _mk_fp_unary_norm(f, a, ctx):
    ctx = _get_ctx(ctx)
    [a] = _coerce_fp_expr_list([a], ctx)
    if __debug__:
        _z3_assert(is_fp(a), "First argument must be a Z3 floating-point expression")
    return FPRef(f(ctx.ref(), a.as_ast()), ctx)

def _mk_fp_unary_pred(f, a, ctx):
    ctx = _get_ctx(ctx)
    [a] = _coerce_fp_expr_list([a], ctx)
    if __debug__:
        _z3_assert(is_fp(a) or is_fp(b), "Second or third argument must be a Z3 floating-point expression")
    return BoolRef(f(ctx.ref(), a.as_ast()), ctx)

def _mk_fp_bin(f, rm, a, b, ctx):
    ctx = _get_ctx(ctx)
    [a, b] = _coerce_fp_expr_list([a, b], ctx)
    if __debug__:
        _z3_assert(is_fprm(rm), "First argument must be a Z3 floating-point rounding mode expression")
        _z3_assert(is_fp(a) or is_fp(b), "Second or third argument must be a Z3 floating-point expression")
    return FPRef(f(ctx.ref(), rm.as_ast(), a.as_ast(), b.as_ast()), ctx)

def _mk_fp_bin_norm(f, a, b, ctx):
    ctx = _get_ctx(ctx)
    [a, b] = _coerce_fp_expr_list([a, b], ctx)
    if __debug__:
        _z3_assert(is_fp(a) or is_fp(b), "First or second argument must be a Z3 floating-point expression")
    return FPRef(f(ctx.ref(), a.as_ast(), b.as_ast()), ctx)

def _mk_fp_bin_pred(f, a, b, ctx):
    ctx = _get_ctx(ctx)
    [a, b] = _coerce_fp_expr_list([a, b], ctx)
    if __debug__:
        _z3_assert(is_fp(a) or is_fp(b), "Second or third argument must be a Z3 floating-point expression")
    return BoolRef(f(ctx.ref(), a.as_ast(), b.as_ast()), ctx)

def _mk_fp_tern(f, rm, a, b, c, ctx):
    ctx = _get_ctx(ctx)
    [a, b, c] = _coerce_fp_expr_list([a, b, c], ctx)
    if __debug__:
        _z3_assert(is_fprm(rm), "First argument must be a Z3 floating-point rounding mode expression")
        _z3_assert(is_fp(a) or is_fp(b) or is_fp(c), "At least one of the arguments must be a Z3 floating-point expression")
    return FPRef(f(ctx.ref(), rm.as_ast(), a.as_ast(), b.as_ast(), c.as_ast()), ctx)

def fpAdd(rm, a, b, ctx=None):
    """Create a Z3 floating-point addition expression.

    >>> s = FPSort(8, 24)
    >>> rm = RNE()
    >>> x = FP('x', s)
    >>> y = FP('y', s)
    >>> fpAdd(rm, x, y)
    fpAdd(RNE(), x, y)
    >>> fpAdd(RTZ(), x, y) # default rounding mode is RTZ
    x + y
    >>> fpAdd(rm, x, y).sort()
    FPSort(8, 24)
    """
    return _mk_fp_bin(Z3_mk_fpa_add, rm, a, b, ctx)

def fpSub(rm, a, b, ctx=None):
    """Create a Z3 floating-point subtraction expression.

    >>> s = FPSort(8, 24)
    >>> rm = RNE()
    >>> x = FP('x', s)
    >>> y = FP('y', s)
    >>> fpSub(rm, x, y)
    fpSub(RNE(), x, y)
    >>> fpSub(rm, x, y).sort()
    FPSort(8, 24)
    """
    return _mk_fp_bin(Z3_mk_fpa_sub, rm, a, b, ctx)

def fpMul(rm, a, b, ctx=None):
    """Create a Z3 floating-point multiplication expression.

    >>> s = FPSort(8, 24)
    >>> rm = RNE()
    >>> x = FP('x', s)
    >>> y = FP('y', s)
    >>> fpMul(rm, x, y)
    fpMul(RNE(), x, y)
    >>> fpMul(rm, x, y).sort()
    FPSort(8, 24)
    """
    return _mk_fp_bin(Z3_mk_fpa_mul, rm, a, b, ctx)

def fpDiv(rm, a, b, ctx=None):
    """Create a Z3 floating-point division expression.

    >>> s = FPSort(8, 24)
    >>> rm = RNE()
    >>> x = FP('x', s)
    >>> y = FP('y', s)
    >>> fpDiv(rm, x, y)
    fpDiv(RNE(), x, y)
    >>> fpDiv(rm, x, y).sort()
    FPSort(8, 24)
    """
    return _mk_fp_bin(Z3_mk_fpa_div, rm, a, b, ctx)

def fpRem(a, b, ctx=None):
    """Create a Z3 floating-point remainder expression.

    >>> s = FPSort(8, 24)
    >>> x = FP('x', s)
    >>> y = FP('y', s)
    >>> fpRem(x, y)
    fpRem(x, y)
    >>> fpRem(x, y).sort()
    FPSort(8, 24)
    """
    return _mk_fp_bin_norm(Z3_mk_fpa_rem, a, b, ctx)

def fpMin(a, b, ctx=None):
    """Create a Z3 floating-point minimum expression.

    >>> s = FPSort(8, 24)
    >>> rm = RNE()
    >>> x = FP('x', s)
    >>> y = FP('y', s)
    >>> fpMin(x, y)
    fpMin(x, y)
    >>> fpMin(x, y).sort()
    FPSort(8, 24)
    """
    return _mk_fp_bin_norm(Z3_mk_fpa_min, a, b, ctx)

def fpMax(a, b, ctx=None):
    """Create a Z3 floating-point maximum expression.

    >>> s = FPSort(8, 24)
    >>> rm = RNE()
    >>> x = FP('x', s)
    >>> y = FP('y', s)
    >>> fpMax(x, y)
    fpMax(x, y)
    >>> fpMax(x, y).sort()
    FPSort(8, 24)
    """
    return _mk_fp_bin_norm(Z3_mk_fpa_max, a, b, ctx)

def fpFMA(rm, a, b, c, ctx=None):
    """Create a Z3 floating-point fused multiply-add expression.
    """
    return _mk_fp_tern(Z3_mk_fpa_fma, rm, a, b, c, ctx)

def fpSqrt(rm, a, ctx=None):
    """Create a Z3 floating-point square root expression.
    """
    return _mk_fp_unary(Z3_mk_fpa_sqrt, rm, a, ctx)

def fpRoundToIntegral(rm, a, ctx=None):
    """Create a Z3 floating-point roundToIntegral expression.
    """
    return _mk_fp_unary(Z3_mk_fpa_round_to_integral, rm, a, ctx)

def fpIsNaN(a, ctx=None):
    """Create a Z3 floating-point isNaN expression.

    >>> s = FPSort(8, 24)
    >>> x = FP('x', s)
    >>> y = FP('y', s)
    >>> fpIsNaN(x)
    fpIsNaN(x)
    """
    return _mk_fp_unary_norm(Z3_mk_fpa_is_nan, a, ctx)

def fpIsInf(a, ctx=None):
    """Create a Z3 floating-point isInfinite expression.

    >>> s = FPSort(8, 24)
    >>> x = FP('x', s)
    >>> fpIsInf(x)
    fpIsInf(x)
    """
    return _mk_fp_unary_norm(Z3_mk_fpa_is_infinite, a, ctx)

def fpIsZero(a, ctx=None):
    """Create a Z3 floating-point isZero expression.
    """
    return _mk_fp_unary_norm(Z3_mk_fpa_is_zero, a, ctx)

def fpIsNormal(a, ctx=None):
    """Create a Z3 floating-point isNormal expression.
    """
    return _mk_fp_unary_norm(Z3_mk_fpa_is_normal, a, ctx)

def fpIsSubnormal(a, ctx=None):
    """Create a Z3 floating-point isSubnormal expression.
    """
    return _mk_fp_unary_norm(Z3_mk_fpa_is_subnormal, a, ctx)

def fpIsNegative(a, ctx=None):
    """Create a Z3 floating-point isNegative expression.
    """
    return _mk_fp_unary_norm(Z3_mk_fpa_is_negative, a, ctx)

def fpIsPositive(a, ctx=None):
    """Create a Z3 floating-point isPositive expression.
    """
    return _mk_fp_unary_norm(Z3_mk_fpa_is_positive, a, ctx)
    return FPRef(Z3_mk_fpa_is_positive(a.ctx_ref(), a.as_ast()), a.ctx)

def _check_fp_args(a, b):
    if __debug__:
        _z3_assert(is_fp(a) or is_fp(b), "At least one of the arguments must be a Z3 floating-point expression")

def fpLT(a, b, ctx=None):
    """Create the Z3 floating-point expression `other < self`.

    >>> x, y = FPs('x y', FPSort(8, 24))
    >>> fpLT(x, y)
    x < y
    >>> (x < y).sexpr()
    '(fp.lt x y)'
    """
    return _mk_fp_bin_pred(Z3_mk_fpa_lt, a, b, ctx)

def fpLEQ(a, b, ctx=None):
    """Create the Z3 floating-point expression `other <= self`.

    >>> x, y = FPs('x y', FPSort(8, 24))
    >>> fpLEQ(x, y)
    x <= y
    >>> (x <= y).sexpr()
    '(fp.leq x y)'
    """
    return _mk_fp_bin_pred(Z3_mk_fpa_leq, a, b, ctx)

def fpGT(a, b, ctx=None):
    """Create the Z3 floating-point expression `other > self`.

    >>> x, y = FPs('x y', FPSort(8, 24))
    >>> fpGT(x, y)
    x > y
    >>> (x > y).sexpr()
    '(fp.gt x y)'
    """
    return _mk_fp_bin_pred(Z3_mk_fpa_gt, a, b, ctx)

def fpGEQ(a, b, ctx=None):
    """Create the Z3 floating-point expression `other >= self`.

    >>> x, y = FPs('x y', FPSort(8, 24))
    >>> fpGEQ(x, y)
    x >= y
    >>> (x >= y).sexpr()
    '(fp.geq x y)'
    """
    return _mk_fp_bin_pred(Z3_mk_fpa_geq, a, b, ctx)

def fpEQ(a, b, ctx=None):
    """Create the Z3 floating-point expression `fpEQ(other, self)`.

    >>> x, y = FPs('x y', FPSort(8, 24))
    >>> fpEQ(x, y)
    fpEQ(x, y)
    >>> fpEQ(x, y).sexpr()
    '(fp.eq x y)'
    """
    return _mk_fp_bin_pred(Z3_mk_fpa_eq, a, b, ctx)

def fpNEQ(a, b, ctx=None):
    """Create the Z3 floating-point expression `Not(fpEQ(other, self))`.

    >>> x, y = FPs('x y', FPSort(8, 24))
    >>> fpNEQ(x, y)
    Not(fpEQ(x, y))
    >>> (x != y).sexpr()
    '(distinct x y)'
    """
    return Not(fpEQ(a, b, ctx))

def fpFP(sgn, exp, sig, ctx=None):
    """Create the Z3 floating-point value `fpFP(sgn, sig, exp)` from the three bit-vectors sgn, sig, and exp.

    >>> s = FPSort(8, 24)
    >>> x = fpFP(BitVecVal(1, 1), BitVecVal(2**7-1, 8), BitVecVal(2**22, 23))
    >>> print(x)
    fpFP(1, 127, 4194304)
    >>> xv = FPVal(-1.5, s)
    >>> print(xv)
    -1.5
    >>> slvr = Solver()
    >>> slvr.add(fpEQ(x, xv))
    >>> slvr.check()
    sat
    >>> xv = FPVal(+1.5, s)
    >>> print(xv)
    1.5
    >>> slvr = Solver()
    >>> slvr.add(fpEQ(x, xv))
    >>> slvr.check()
    unsat
    """
    _z3_assert(is_bv(sgn) and is_bv(exp) and is_bv(sig), "sort mismatch")
    _z3_assert(sgn.sort().size() == 1, "sort mismatch")
    ctx = _get_ctx(ctx)
    _z3_assert(ctx == sgn.ctx == exp.ctx == sig.ctx, "context mismatch")
    return FPRef(Z3_mk_fpa_fp(ctx.ref(), sgn.ast, exp.ast, sig.ast), ctx)

def fpToFP(a1, a2=None, a3=None, ctx=None):
    """Create a Z3 floating-point conversion expression from other term sorts
    to floating-point.

    From a bit-vector term in IEEE 754-2008 format:
    >>> x = FPVal(1.0, Float32())
    >>> x_bv = fpToIEEEBV(x)
    >>> simplify(fpToFP(x_bv, Float32()))
    1

    From a floating-point term with different precision:
    >>> x = FPVal(1.0, Float32())
    >>> x_db = fpToFP(RNE(), x, Float64())
    >>> x_db.sort()
    FPSort(11, 53)

    From a real term:
    >>> x_r = RealVal(1.5)
    >>> simplify(fpToFP(RNE(), x_r, Float32()))
    1.5

    From a signed bit-vector term:
    >>> x_signed = BitVecVal(-5, BitVecSort(32))
    >>> simplify(fpToFP(RNE(), x_signed, Float32()))
    -1.25*(2**2)
    """
    ctx = _get_ctx(ctx)
    if is_bv(a1) and is_fp_sort(a2):
        return FPRef(Z3_mk_fpa_to_fp_bv(ctx.ref(), a1.ast, a2.ast), ctx)
    elif is_fprm(a1) and is_fp(a2) and is_fp_sort(a3):
        return FPRef(Z3_mk_fpa_to_fp_float(ctx.ref(), a1.ast, a2.ast, a3.ast), ctx)
    elif is_fprm(a1) and is_real(a2) and is_fp_sort(a3):
        return FPRef(Z3_mk_fpa_to_fp_real(ctx.ref(), a1.ast, a2.ast, a3.ast), ctx)
    elif is_fprm(a1) and is_bv(a2) and is_fp_sort(a3):
        return FPRef(Z3_mk_fpa_to_fp_signed(ctx.ref(), a1.ast, a2.ast, a3.ast), ctx)
    else:
        raise Z3Exception("Unsupported combination of arguments for conversion to floating-point term.")

def fpBVToFP(v, sort, ctx=None):
    """Create a Z3 floating-point conversion expression that represents the 
    conversion from a bit-vector term to a floating-point term.

    >>> x_bv = BitVecVal(0x3F800000, 32)
    >>> x_fp = fpBVToFP(x_bv, Float32())
    >>> x_fp
    fpToFP(1065353216)
    >>> simplify(x_fp)
    1
    """
    _z3_assert(is_bv(v), "First argument must be a Z3 floating-point rounding mode expression.")
    _z3_assert(is_fp_sort(sort), "Second argument must be a Z3 floating-point sort.")
    ctx = _get_ctx(ctx)
    return FPRef(Z3_mk_fpa_to_fp_bv(ctx.ref(), v.ast, sort.ast), ctx)

def fpFPToFP(rm, v, sort, ctx=None):
    """Create a Z3 floating-point conversion expression that represents the 
    conversion from a floating-point term to a floating-point term of different precision.

    >>> x_sgl = FPVal(1.0, Float32())
    >>> x_dbl = fpFPToFP(RNE(), x_sgl, Float64())
    >>> x_dbl
    fpToFP(RNE(), 1)
    >>> simplify(x_dbl)
    1
    >>> x_dbl.sort()
    FPSort(11, 53)
    """
    _z3_assert(is_fprm(rm), "First argument must be a Z3 floating-point rounding mode expression.")
    _z3_assert(is_fp(v), "Second argument must be a Z3 floating-point expression.")
    _z3_assert(is_fp_sort(sort), "Third argument must be a Z3 floating-point sort.")
    ctx = _get_ctx(ctx)
    return FPRef(Z3_mk_fpa_to_fp_float(ctx.ref(), rm.ast, v.ast, sort.ast), ctx)

def fpRealToFP(rm, v, sort, ctx=None):
    """Create a Z3 floating-point conversion expression that represents the 
    conversion from a real term to a floating-point term.

    >>> x_r = RealVal(1.5)
    >>> x_fp = fpRealToFP(RNE(), x_r, Float32())
    >>> x_fp
    fpToFP(RNE(), 3/2)
    >>> simplify(x_fp)
    1.5
    """
    _z3_assert(is_fprm(rm), "First argument must be a Z3 floating-point rounding mode expression.")
    _z3_assert(is_real(v), "Second argument must be a Z3 expression or real sort.")
    _z3_assert(is_fp_sort(sort), "Third argument must be a Z3 floating-point sort.")
    ctx = _get_ctx(ctx)
    return FPRef(Z3_mk_fpa_to_fp_real(ctx.ref(), rm.ast, v.ast, sort.ast), ctx)

def fpSignedToFP(rm, v, sort, ctx=None):
    """Create a Z3 floating-point conversion expression that represents the 
    conversion from a signed bit-vector term (encoding an integer) to a floating-point term.

    >>> x_signed = BitVecVal(-5, BitVecSort(32))
    >>> x_fp = fpSignedToFP(RNE(), x_signed, Float32())
    >>> x_fp
    fpToFP(RNE(), 4294967291)
    >>> simplify(x_fp)
    -1.25*(2**2)
    """
    _z3_assert(is_fprm(rm), "First argument must be a Z3 floating-point rounding mode expression.")
    _z3_assert(is_bv(v), "Second argument must be a Z3 expression or real sort.")
    _z3_assert(is_fp_sort(sort), "Third argument must be a Z3 floating-point sort.")
    ctx = _get_ctx(ctx)
    return FPRef(Z3_mk_fpa_to_fp_signed(ctx.ref(), rm.ast, v.ast, sort.ast), ctx)

def fpUnsignedToFP(rm, v, sort, ctx=None):
    """Create a Z3 floating-point conversion expression that represents the 
    conversion from an unsigned bit-vector term (encoding an integer) to a floating-point term.

    >>> x_signed = BitVecVal(-5, BitVecSort(32))
    >>> x_fp = fpUnsignedToFP(RNE(), x_signed, Float32())
    >>> x_fp
    fpToFPUnsigned(RNE(), 4294967291)
    >>> simplify(x_fp)
    1*(2**32)
    """
    _z3_assert(is_fprm(rm), "First argument must be a Z3 floating-point rounding mode expression.")
    _z3_assert(is_bv(v), "Second argument must be a Z3 expression or real sort.")
    _z3_assert(is_fp_sort(sort), "Third argument must be a Z3 floating-point sort.")
    ctx = _get_ctx(ctx)
    return FPRef(Z3_mk_fpa_to_fp_unsigned(ctx.ref(), rm.ast, v.ast, sort.ast), ctx)

def fpToFPUnsigned(rm, x, s, ctx=None):
    """Create a Z3 floating-point conversion expression, from unsigned bit-vector to floating-point expression."""
    if __debug__:
        _z3_assert(is_fprm(rm), "First argument must be a Z3 floating-point rounding mode expression")
        _z3_assert(is_bv(x), "Second argument must be a Z3 bit-vector expression")
        _z3_assert(is_fp_sort(s), "Third argument must be Z3 floating-point sort")
    ctx = _get_ctx(ctx)
    return FPRef(Z3_mk_fpa_to_fp_unsigned(ctx.ref(), rm.ast, x.ast, s.ast), ctx)

def fpToSBV(rm, x, s, ctx=None):
    """Create a Z3 floating-point conversion expression, from floating-point expression to signed bit-vector.

    >>> x = FP('x', FPSort(8, 24))
    >>> y = fpToSBV(RTZ(), x, BitVecSort(32))
    >>> print(is_fp(x))
    True
    >>> print(is_bv(y))
    True
    >>> print(is_fp(y))
    False
    >>> print(is_bv(x))
    False
    """
    if __debug__:
        _z3_assert(is_fprm(rm), "First argument must be a Z3 floating-point rounding mode expression")
        _z3_assert(is_fp(x), "Second argument must be a Z3 floating-point expression")
        _z3_assert(is_bv_sort(s), "Third argument must be Z3 bit-vector sort")
    ctx = _get_ctx(ctx)
    return BitVecRef(Z3_mk_fpa_to_sbv(ctx.ref(), rm.ast, x.ast, s.size()), ctx)

def fpToUBV(rm, x, s, ctx=None):
    """Create a Z3 floating-point conversion expression, from floating-point expression to unsigned bit-vector.

    >>> x = FP('x', FPSort(8, 24))
    >>> y = fpToUBV(RTZ(), x, BitVecSort(32))
    >>> print(is_fp(x))
    True
    >>> print(is_bv(y))
    True
    >>> print(is_fp(y))
    False
    >>> print(is_bv(x))
    False
    """
    if __debug__:
        _z3_assert(is_fprm(rm), "First argument must be a Z3 floating-point rounding mode expression")
        _z3_assert(is_fp(x), "Second argument must be a Z3 floating-point expression")
        _z3_assert(is_bv_sort(s), "Third argument must be Z3 bit-vector sort")
    ctx = _get_ctx(ctx)
    return BitVecRef(Z3_mk_fpa_to_ubv(ctx.ref(), rm.ast, x.ast, s.size()), ctx)

def fpToReal(x, ctx=None):
    """Create a Z3 floating-point conversion expression, from floating-point expression to real.

    >>> x = FP('x', FPSort(8, 24))
    >>> y = fpToReal(x)
    >>> print(is_fp(x))
    True
    >>> print(is_real(y))
    True
    >>> print(is_fp(y))
    False
    >>> print(is_real(x))
    False
    """
    if __debug__:
        _z3_assert(is_fp(x), "First argument must be a Z3 floating-point expression")
    ctx = _get_ctx(ctx)
    return ArithRef(Z3_mk_fpa_to_real(ctx.ref(), x.ast), ctx)

def fpToIEEEBV(x, ctx=None):
    """\brief Conversion of a floating-point term into a bit-vector term in IEEE 754-2008 format.

    The size of the resulting bit-vector is automatically determined.

    Note that IEEE 754-2008 allows multiple different representations of NaN. This conversion
    knows only one NaN and it will always produce the same bit-vector representation of
    that NaN.

    >>> x = FP('x', FPSort(8, 24))
    >>> y = fpToIEEEBV(x)
    >>> print(is_fp(x))
    True
    >>> print(is_bv(y))
    True
    >>> print(is_fp(y))
    False
    >>> print(is_bv(x))
    False
    """
    if __debug__:
        _z3_assert(is_fp(x), "First argument must be a Z3 floating-point expression")
    ctx = _get_ctx(ctx)
    return BitVecRef(Z3_mk_fpa_to_ieee_bv(ctx.ref(), x.ast), ctx)



#########################################
#
# Strings, Sequences and Regular expressions
#
#########################################

class SeqSortRef(SortRef):
    """Sequence sort."""

    def is_string(self):
        """Determine if sort is a string
        >>> s = StringSort()
        >>> s.is_string()
        True
        >>> s = SeqSort(IntSort())
        >>> s.is_string()
        False
        """
        return Z3_is_string_sort(self.ctx_ref(), self.ast)
        

def StringSort(ctx=None):
    """Create a string sort
    >>> s = StringSort()
    >>> print(s)
    String
    """
    ctx = _get_ctx(ctx)
    return SeqSortRef(Z3_mk_string_sort(ctx.ref()), ctx)


def SeqSort(s):
    """Create a sequence sort over elements provided in the argument
    >>> s = SeqSort(IntSort())
    >>> s == Unit(IntVal(1)).sort()
    True
    """
    return SeqSortRef(Z3_mk_seq_sort(s.ctx_ref(), s.ast), s.ctx)

class SeqRef(ExprRef):
    """Sequence expression."""

    def sort(self):
        return SeqSortRef(Z3_get_sort(self.ctx_ref(), self.as_ast()), self.ctx)

    def __add__(self, other):
        return Concat(self, other)

    def __radd__(self, other):
        return Concat(other, self)

    def __getitem__(self, i):
        if _is_int(i):
            i = IntVal(i, self.ctx)
        return SeqRef(Z3_mk_seq_at(self.ctx_ref(), self.as_ast(), i.as_ast()), self.ctx)

    def is_string(self):
        return Z3_is_string_sort(self.ctx_ref(), Z3_get_sort(self.ctx_ref(), self.as_ast()))

    def is_string_value(self):
        return Z3_is_string(self.ctx_ref(), self.as_ast())

    def as_string(self):
        """Return a string representation of sequence expression."""
        return Z3_ast_to_string(self.ctx_ref(), self.as_ast())


def _coerce_seq(s, ctx=None):
    if isinstance(s, str):
        ctx = _get_ctx(ctx)
        s = StringVal(s, ctx)
    if not is_expr(s):
        raise Z3Exception("Non-expression passed as a sequence")
    if not is_seq(s):
        raise Z3Exception("Non-sequence passed as a sequence")
    return s

def _get_ctx2(a, b, ctx=None):
    if is_expr(a):
        return a.ctx
    if is_expr(b):
        return b.ctx
    if ctx is None:
        ctx = main_ctx()
    return ctx

def is_seq(a):
    """Return `True` if `a` is a Z3 sequence expression.
    >>> print (is_seq(Unit(IntVal(0))))
    True
    >>> print (is_seq(StringVal("abc")))
    True
    """
    return isinstance(a, SeqRef)

def is_string(a):
    """Return `True` if `a` is a Z3 string expression.
    >>> print (is_string(StringVal("ab")))
    True
    """
    return isinstance(a, SeqRef) and a.is_string()

def is_string_value(a):
    """return 'True' if 'a' is a Z3 string constant expression.
    >>> print (is_string_value(StringVal("a")))
    True
    >>> print (is_string_value(StringVal("a") + StringVal("b")))
    False
    """
    return isinstance(a, SeqRef) and a.is_string_value()


def StringVal(s, ctx=None):
    """create a string expression"""
    ctx = _get_ctx(ctx)
    return SeqRef(Z3_mk_string(ctx.ref(), s), ctx)

def String(name, ctx=None):
    """Return a string constant named `name`. If `ctx=None`, then the global context is used.

    >>> x = String('x')
    """
    ctx = _get_ctx(ctx)
    return SeqRef(Z3_mk_const(ctx.ref(), to_symbol(name, ctx), StringSort(ctx).ast), ctx)

def SubString(s, offset, length):
    """Extract substring or subsequence starting at offset"""
    return Extract(s, offset, length)

def SubSeq(s, offset, length):
    """Extract substring or subsequence starting at offset"""
    return Extract(s, offset, length)

def Strings(names, ctx=None):
    """Return a tuple of String constants. """
    ctx = _get_ctx(ctx)
    if isinstance(names, str):
        names = names.split(" ")
    return [String(name, ctx) for name in names]

def Empty(s):
    """Create the empty sequence of the given sort
    >>> e = Empty(StringSort())
    >>> print(e)
    ""
    >>> e2 = StringVal("")
    >>> print(e.eq(e2))
    True
    >>> e3 = Empty(SeqSort(IntSort()))
    >>> print(e3)
    seq.empty
    >>> e4 = Empty(ReSort(SeqSort(IntSort())))
    >>> print(e4)
    re.empty
    """
    if isinstance(s, SeqSortRef):
       return SeqRef(Z3_mk_seq_empty(s.ctx_ref(), s.ast), s.ctx)
    if isinstance(s, ReSortRef):
       return ReRef(Z3_mk_re_empty(s.ctx_ref(), s.ast), s.ctx)
    raise Z3Exception("Non-sequence, non-regular expression sort passed to Empty")

def Full(s):
    """Create the regular expression that accepts the universal language
    >>> e = Full(ReSort(SeqSort(IntSort())))
    >>> print(e)
    re.all
    >>> e1 = Full(ReSort(StringSort()))
    >>> print(e1)
    re.all
    """
    if isinstance(s, ReSortRef):
       return ReRef(Z3_mk_re_full(s.ctx_ref(), s.ast), s.ctx)
    raise Z3Exception("Non-sequence, non-regular expression sort passed to Full")


def Unit(a):
    """Create a singleton sequence"""
    return SeqRef(Z3_mk_seq_unit(a.ctx_ref(), a.as_ast()), a.ctx)

def PrefixOf(a, b):
    """Check if 'a' is a prefix of 'b'
    >>> s1 = PrefixOf("ab", "abc")
    >>> simplify(s1)
    True
    >>> s2 = PrefixOf("bc", "abc")
    >>> simplify(s2)
    False
    """
    ctx = _get_ctx2(a, b)
    a = _coerce_seq(a, ctx)
    b = _coerce_seq(b, ctx)
    return BoolRef(Z3_mk_seq_prefix(a.ctx_ref(), a.as_ast(), b.as_ast()), a.ctx)

def SuffixOf(a, b):
    """Check if 'a' is a suffix of 'b'
    >>> s1 = SuffixOf("ab", "abc")
    >>> simplify(s1)
    False
    >>> s2 = SuffixOf("bc", "abc")
    >>> simplify(s2)
    True
    """
    ctx = _get_ctx2(a, b)
    a = _coerce_seq(a, ctx)
    b = _coerce_seq(b, ctx)
    return BoolRef(Z3_mk_seq_suffix(a.ctx_ref(), a.as_ast(), b.as_ast()), a.ctx)

def Contains(a, b):
    """Check if 'a' contains 'b'
    >>> s1 = Contains("abc", "ab")
    >>> simplify(s1)
    True
    >>> s2 = Contains("abc", "bc")
    >>> simplify(s2)
    True
    >>> x, y, z = Strings('x y z')
    >>> s3 = Contains(Concat(x,y,z), y)
    >>> simplify(s3)
    True
    """
    ctx = _get_ctx2(a, b)
    a = _coerce_seq(a, ctx)
    b = _coerce_seq(b, ctx)
    return BoolRef(Z3_mk_seq_contains(a.ctx_ref(), a.as_ast(), b.as_ast()), a.ctx)


def Replace(s, src, dst):
    """Replace the first occurrence of 'src' by 'dst' in 's'
    >>> r = Replace("aaa", "a", "b")
    >>> simplify(r)
    "baa"
    """
    ctx = _get_ctx2(dst, s)
    if ctx is None and is_expr(src):
        ctx = src.ctx
    src = _coerce_seq(src, ctx)
    dst = _coerce_seq(dst, ctx)
    s   = _coerce_seq(s, ctx)
    return SeqRef(Z3_mk_seq_replace(src.ctx_ref(), s.as_ast(), src.as_ast(), dst.as_ast()), s.ctx)

def IndexOf(s, substr):
    return IndexOf(s, substr, IntVal(0))

def IndexOf(s, substr, offset):
    """Retrieve the index of substring within a string starting at a specified offset.
    >>> simplify(IndexOf("abcabc", "bc", 0))
    1
    >>> simplify(IndexOf("abcabc", "bc", 2))
    4
    """
    ctx = None
    if is_expr(offset):
        ctx = offset.ctx
    ctx = _get_ctx2(s, substr, ctx)
    s = _coerce_seq(s, ctx)
    substr = _coerce_seq(substr, ctx)
    if _is_int(offset):
        offset = IntVal(offset, ctx)
    return SeqRef(Z3_mk_seq_index(s.ctx_ref(), s.as_ast(), substr.as_ast(), offset.as_ast()), s.ctx)

def Length(s):
    """Obtain the length of a sequence 's'
    >>> l = Length(StringVal("abc"))
    >>> simplify(l)
    3
    """
    s = _coerce_seq(s)
    return ArithRef(Z3_mk_seq_length(s.ctx_ref(), s.as_ast()), s.ctx)

def StrToInt(s):
    """Convert string expression to integer
    >>> a = StrToInt("1")
    >>> simplify(1 == a)
    True
    >>> b = StrToInt("2")
    >>> simplify(1 == b)
    False
    >>> c = StrToInt(IntToStr(2))
    >>> simplify(1 == c)
    False
    """
    s = _coerce_seq(s)
    return ArithRef(Z3_mk_str_to_int(s.ctx_ref(), s.as_ast()), s.ctx)


def IntToStr(s):
    """Convert integer expression to string"""
    if not is_expr(s):
        s = _py2expr(s)
    return SeqRef(Z3_mk_int_to_str(s.ctx_ref(), s.as_ast()), s.ctx)


def Re(s, ctx=None):
    """The regular expression that accepts sequence 's'
    >>> s1 = Re("ab")
    >>> s2 = Re(StringVal("ab"))
    >>> s3 = Re(Unit(BoolVal(True)))
    """
    s = _coerce_seq(s, ctx)
    return ReRef(Z3_mk_seq_to_re(s.ctx_ref(), s.as_ast()), s.ctx)




## Regular expressions

class ReSortRef(SortRef):
    """Regular expression sort."""


def ReSort(s):
    if is_ast(s):
        return ReSortRef(Z3_mk_re_sort(s.ctx.ref(), s.ast), s.ctx)
    if s is None or isinstance(s, Context):
        ctx = _get_ctx(s)
        return ReSortRef(Z3_mk_re_sort(ctx.ref(), Z3_mk_string_sort(ctx.ref())), s.ctx)
    raise Z3Exception("Regular expression sort constructor expects either a string or a context or no argument")


class ReRef(ExprRef):
    """Regular expressions."""

    def __add__(self, other):
        return Union(self, other)


def is_re(s):
    return isinstance(s, ReRef)


def InRe(s, re):
    """Create regular expression membership test
    >>> re = Union(Re("a"),Re("b"))
    >>> print (simplify(InRe("a", re)))
    True
    >>> print (simplify(InRe("b", re)))
    True
    >>> print (simplify(InRe("c", re)))
    False
    """
    s = _coerce_seq(s, re.ctx)
    return BoolRef(Z3_mk_seq_in_re(s.ctx_ref(), s.as_ast(), re.as_ast()), s.ctx)

def Union(*args):
    """Create union of regular expressions.
    >>> re = Union(Re("a"), Re("b"), Re("c"))
    >>> print (simplify(InRe("d", re)))
    False
    """
    args = _get_args(args)
    sz = len(args)
    if __debug__:
        _z3_assert(sz > 0, "At least one argument expected.")
        _z3_assert(all([is_re(a) for a in args]), "All arguments must be regular expressions.")
    if sz == 1:
        return args[0]
    ctx = args[0].ctx
    v = (Ast * sz)()
    for i in range(sz):
        v[i] = args[i].as_ast()
    return ReRef(Z3_mk_re_union(ctx.ref(), sz, v), ctx)

def Plus(re):
    """Create the regular expression accepting one or more repetitions of argument.
    >>> re = Plus(Re("a"))
    >>> print(simplify(InRe("aa", re)))
    True
    >>> print(simplify(InRe("ab", re)))
    False
    >>> print(simplify(InRe("", re)))
    False
    """
    return ReRef(Z3_mk_re_plus(re.ctx_ref(), re.as_ast()), re.ctx)

def Option(re):
    """Create the regular expression that optionally accepts the argument.
    >>> re = Option(Re("a"))
    >>> print(simplify(InRe("a", re)))
    True
    >>> print(simplify(InRe("", re)))
    True
    >>> print(simplify(InRe("aa", re)))
    False
    """
    return ReRef(Z3_mk_re_option(re.ctx_ref(), re.as_ast()), re.ctx)

def Complement(re):
    """Create the complement regular expression."""
    return ReRef(Z3_mk_re_complement(re.ctx_ref(), re.as_ast()), re.ctx)

def Star(re):
    """Create the regular expression accepting zero or more repetitions of argument.
    >>> re = Star(Re("a"))
    >>> print(simplify(InRe("aa", re)))
    True
    >>> print(simplify(InRe("ab", re)))
    False
    >>> print(simplify(InRe("", re)))
    True
    """
    return ReRef(Z3_mk_re_star(re.ctx_ref(), re.as_ast()), re.ctx)

def Loop(re, lo, hi=0):
    """Create the regular expression accepting between a lower and upper bound repetitions
    >>> re = Loop(Re("a"), 1, 3)
    >>> print(simplify(InRe("aa", re)))
    True
    >>> print(simplify(InRe("aaaa", re)))
    False
    >>> print(simplify(InRe("", re)))
    False
    """
    return ReRef(Z3_mk_re_loop(re.ctx_ref(), re.as_ast(), lo, hi), re.ctx)
