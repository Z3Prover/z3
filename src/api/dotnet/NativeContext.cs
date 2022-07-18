/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    NativeContext.cs

Abstract:

    Z3 Managed API: Native Context

Author:

    Christoph Wintersteiger (cwinter) 2012-03-22
    John Fleisher, Nikolaj Bjorner (nbjorner) 2022-03-01
       
--*/

using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Runtime.InteropServices;

namespace Microsoft.Z3
{
    using Z3_app = System.IntPtr;
    using Z3_ast = System.IntPtr;
    using Z3_ast_vector = System.IntPtr;
    using Z3_func_decl = System.IntPtr;
    using Z3_pattern = System.IntPtr;
    using Z3_solver = System.IntPtr;
    using Z3_sort = System.IntPtr;
    using Z3_stats = System.IntPtr;
    using Z3_symbol = System.IntPtr;

    /// <summary>
    /// The main interaction with Z3 happens via the Context.
    /// NativeContext allows for efficient wrapper-reduced interaction with Z3
    /// expressions.
    /// </summary>
    public class NativeContext : IDisposable
    {
        /// <summary>
        /// Constructor.
        /// </summary>
        /// <remarks>
        /// The following parameters can be set:
        ///     - proof  (Boolean)           Enable proof generation
        ///     - debug_ref_count (Boolean)  Enable debug support for Z3_ast reference counting
        ///     - trace  (Boolean)           Tracing support for VCC
        ///     - trace_file_name (String)   Trace out file for VCC traces
        ///     - timeout (unsigned)         default timeout (in milliseconds) used for solvers
        ///     - well_sorted_check          type checker
        ///     - auto_config                use heuristics to automatically select solver and configure it
        ///     - model                      model generation for solvers, this parameter can be overwritten when creating a solver
        ///     - model_validate             validate models produced by solvers
        ///     - unsat_core                 unsat-core generation for solvers, this parameter can be overwritten when creating a solver
        /// Note that in previous versions of Z3, this constructor was also used to set global and module parameters.
        /// For this purpose we should now use <see cref="Global.SetParameter"/>
        /// </remarks>
        public NativeContext(Dictionary<string, string> settings)
            : base()
        {
            Debug.Assert(settings != null);

            lock (creation_lock)
            {
                IntPtr cfg = Native.Z3_mk_config();
                foreach (KeyValuePair<string, string> kv in settings)
                    Native.Z3_set_param_value(cfg, kv.Key, kv.Value);
                m_ctx = Native.Z3_mk_context(cfg);
                Native.Z3_del_config(cfg);
                InitContext();
            }
        }

        #region Arithmetic
        /// <summary>
        /// Create an expression representing <c>t[0] + t[1] + ...</c>.
        /// </summary>

        public Z3_ast MkAdd(params Z3_ast[] t)
        {
            Debug.Assert(t != null);
            Debug.Assert(t.All(a => a != IntPtr.Zero));

            return Native.Z3_mk_add(nCtx, (uint)(t?.Length ?? 0), t);
        }

        /// <summary>
        /// Create an expression representing <c>t[0] * t[1] * ...</c>.
        /// </summary>
        public Z3_ast MkMul(params Z3_ast[] t)
        {
            Debug.Assert(t != null);
            Debug.Assert(t.All(a => a != IntPtr.Zero));

            var ts = t.ToArray();
            return Native.Z3_mk_mul(nCtx, (uint)(ts?.Length ?? 0), ts);
        }

        /// <summary>
        /// Create an expression representing <c>t[0] - t[1] - ...</c>.
        /// </summary>
	public Z3_ast MkSub(params Z3_ast[] t)
        {
            Debug.Assert(t != null);
            Debug.Assert(t.All(a => a != IntPtr.Zero));
            var ts = t.ToArray();
	    return Native.Z3_mk_sub(nCtx, (uint)(ts?.Length ?? 0), ts);
	}

        /// <summary>
        /// Create an expression representing <c>t1 / t2</c>.
        /// </summary>
        public Z3_ast MkDiv(Z3_ast t1, Z3_ast t2)
        {
            Debug.Assert(t1 != IntPtr.Zero);
            Debug.Assert(t2 != IntPtr.Zero);

            return Native.Z3_mk_div(nCtx, t1, t2);
        }

        /// <summary>
        /// Create an expression representing <c>t1 &lt;= t2</c>
        /// </summary>
        public Z3_ast MkLe(Z3_ast t1, Z3_ast t2)
        {
            Debug.Assert(t1 != IntPtr.Zero);
            Debug.Assert(t2 != IntPtr.Zero);

            return Native.Z3_mk_le(nCtx, t1, t2);
        }

        /// <summary>
        /// Create an expression representing <c>t1 &lt; t2</c>
        /// </summary>
        public Z3_ast MkLt(Z3_ast t1, Z3_ast t2)
        {
            Debug.Assert(t1 != IntPtr.Zero);
            Debug.Assert(t2 != IntPtr.Zero);

            return Native.Z3_mk_lt(nCtx, t1, t2);
        }

        /// <summary>
        /// Create an expression representing <c>t1 &gt;= t2</c>
        /// </summary>
        public Z3_ast MkGe(Z3_ast t1, Z3_ast t2)
        {
            Debug.Assert(t1 != IntPtr.Zero);
            Debug.Assert(t2 != IntPtr.Zero);

            return Native.Z3_mk_ge(nCtx, t1, t2);
        }

        /// <summary>
        /// Create an expression representing <c>t1 &gt; t2</c>
        /// </summary>
        public Z3_ast MkGt(Z3_ast t1, Z3_ast t2)
        {
            Debug.Assert(t1 != IntPtr.Zero);
            Debug.Assert(t2 != IntPtr.Zero);

            return Native.Z3_mk_gt(nCtx, t1, t2);
        }

        /// <summary>
        /// Unsigned less-than
        /// </summary>
        /// <remarks>
        /// The arguments must have the same bit-vector sort.
        /// </remarks>
        public Z3_ast MkBvUlt(Z3_ast t1, Z3_ast t2)
        {
            Debug.Assert(t1 != IntPtr.Zero);
            Debug.Assert(t2 != IntPtr.Zero);

            return Native.Z3_mk_bvult(nCtx, t1, t2);
        }

        /// <summary>
        /// Unsigned less-than-equal
        /// </summary>
        /// <remarks>
        /// The arguments must have the same bit-vector sort.
        /// </remarks>
        public Z3_ast MkBvUle(Z3_ast t1, Z3_ast t2)
        {
            Debug.Assert(t1 != IntPtr.Zero);
            Debug.Assert(t2 != IntPtr.Zero);

            return Native.Z3_mk_bvule(nCtx, t1, t2);
        }

        /// <summary>
        /// Creates the equality <paramref name="x"/> = <paramref name="y"/>.
        /// </summary>
        public Z3_ast MkEq(Z3_ast x, Z3_ast y)
        {
            Debug.Assert(x != IntPtr.Zero);
            Debug.Assert(y != IntPtr.Zero);

            return Native.Z3_mk_eq(nCtx, x, y);
        }

        /// <summary>
        ///  Mk an expression representing <c>not(a)</c>.
        /// </summary>
        public Z3_ast MkNot(Z3_ast a)
        {
            Debug.Assert(a != IntPtr.Zero);

            return Native.Z3_mk_not(nCtx, a);
        }

        /// <summary>
        /// Create an expression representing <c>t[0] and t[1] and ...</c>.
        /// </summary>
        public Z3_ast MkAnd(params Z3_ast[] t)
        {
            Debug.Assert(t != null);
            Debug.Assert(t.All(a => a != IntPtr.Zero));

            return Native.Z3_mk_and(nCtx, (uint)(t?.Length ?? 0), t);
        }

        /// <summary>
        /// Create an expression representing <c>t[0] or t[1] or ...</c>.
        /// </summary>
        public Z3_ast MkOr(params Z3_ast[] t)
        {
            Debug.Assert(t != null);
            Debug.Assert(t.All(a => a != IntPtr.Zero));

            return Native.Z3_mk_or(nCtx, (uint)(t?.Length ?? 0), t);
        }


        /// <summary>
        /// Create a real numeral.
        /// </summary>
        /// <param name="v">A string representing the Term value in decimal notation.</param>
        /// <returns>A Term with value <paramref name="v"/> and sort Real</returns>
        public Z3_ast MkReal(string v)
        {
            Debug.Assert(!string.IsNullOrEmpty(v));
            return Native.Z3_mk_numeral(nCtx, v, RealSort);
        }

        /// <summary>
        /// Create a Term of a given sort. This function can be used to create numerals that fit in a machine integer.
        /// </summary>
        /// <param name="v">Value of the numeral</param>
        /// <param name="sort">Sort of the numeral</param>
        public Z3_ast MkNumeral(int v, Z3_sort sort)
        {
            Debug.Assert(sort != IntPtr.Zero);

            return Native.Z3_mk_int(nCtx, v, sort);
        }

        /// <summary>
        /// Create a Term of a given sort. This function can be used to create numerals that fit in a machine integer.
        /// </summary>
        /// <param name="v">Value of the numeral</param>
        /// <param name="sort">Sort of the numeral</param>
        public Z3_ast MkNumeral(uint v, Z3_sort sort)
        {
            Debug.Assert(sort != null);

            return Native.Z3_mk_unsigned_int(nCtx, v, sort);
        }

        /// <summary>
        /// Create a Term of a given sort. This function can be used to create numerals that fit in a machine integer.
        /// </summary>
        /// <param name="v">Value of the numeral</param>
        /// <param name="sort">Sort of the numeral</param>
        public Z3_ast MkNumeral(long v, Z3_sort sort)
        {
            Debug.Assert(sort != null);

            return Native.Z3_mk_int64(nCtx, v, sort);
        }

        /// <summary>
        ///  Create an expression representing an if-then-else: <c>ite(t1, t2, t3)</c>.
        /// </summary>
        /// <param name="t1">An expression with Boolean sort</param>
        /// <param name="t2">An expression </param>
        /// <param name="t3">An expression with the same sort as <paramref name="t2"/></param>
        public Z3_ast MkIte(Z3_ast t1, Z3_ast t2, Z3_ast t3)
        {
            Debug.Assert(t1 != IntPtr.Zero);
            Debug.Assert(t2 != IntPtr.Zero);
            Debug.Assert(t3 != IntPtr.Zero);

            return Native.Z3_mk_ite(nCtx, t1, t2, t3);
        }

        /// <summary>
        /// Create an expression representing <c>t1 -> t2</c>.
        /// </summary>
        public Z3_ast MkImplies(Z3_ast t1, Z3_ast t2)
        {
            Debug.Assert(t1 != IntPtr.Zero);
            Debug.Assert(t2 != IntPtr.Zero);

            return Native.Z3_mk_implies(nCtx, t1, t2);
        }

        #endregion

        #region Sort

        /// <summary>
        /// Integer Sort
        /// </summary>
        public Z3_sort IntSort => Native.Z3_mk_int_sort(nCtx);

        /// <summary>
        /// Returns the "singleton" BoolSort for this NativeContext
        /// </summary>
        public Z3_sort BoolSort => Native.Z3_mk_bool_sort(nCtx);

        /// <summary>
        /// Returns the "singleton" RealSort for this NativeContext
        /// </summary>
        public Z3_sort RealSort => Native.Z3_mk_real_sort(nCtx);


        /// <summary>
        /// Returns the BvSort for size in this NativeContext
        /// </summary>
        public Z3_sort MkBvSort(uint size) => Native.Z3_mk_bv_sort(nCtx, size);

        /// <summary>
        /// returns ListSort
        /// </summary>
        /// <param name="name"></param>
        /// <param name="elemSort"></param>
        /// <param name="inil"></param>
        /// <param name="iisnil"></param>
        /// <param name="icons"></param>
        /// <param name="iiscons"></param>
        /// <param name="ihead"></param>
        /// <param name="itail"></param>
        /// <returns>The list algebraic datatype</returns>

        public Z3_sort MkListSort(string name, Z3_sort elemSort,
                                    out Z3_func_decl inil, out Z3_func_decl iisnil,
                                    out Z3_func_decl icons, out Z3_func_decl iiscons,
                                    out Z3_func_decl ihead, out Z3_func_decl itail)
        {
            Debug.Assert(!string.IsNullOrEmpty(name));
            Debug.Assert(elemSort != IntPtr.Zero);

            IntPtr nil = IntPtr.Zero, isnil = IntPtr.Zero,
                   cons = IntPtr.Zero, iscons = IntPtr.Zero,
                   head = IntPtr.Zero, tail = IntPtr.Zero;

            var symbol = Native.Z3_mk_string_symbol(nCtx, name);
            var sort = Native.Z3_mk_list_sort(nCtx, symbol, elemSort,
                                  ref nil, ref isnil, ref cons, ref iscons, ref head, ref tail);

            inil = nil;
            iisnil = isnil;
            icons = cons;
            iiscons = iscons;
            ihead = head;
            itail = tail;

            return sort;
        }

        /// <summary>
        /// Create a new array sort.
        /// </summary>
        public Z3_sort MkArraySort(Z3_sort domain, Z3_sort range)
        {
            Debug.Assert(domain != IntPtr.Zero);
            Debug.Assert(range != IntPtr.Zero);

            return Native.Z3_mk_array_sort(nCtx, domain, range);
        }

        /// <summary>
        /// Create a new tuple sort.
        /// </summary>
        public Z3_sort MkTupleSort(Z3_symbol name, Z3_symbol[] fieldNames, Z3_sort[] fieldSorts, out Z3_func_decl constructor, Z3_func_decl[] projections)
        {
            Debug.Assert(name != IntPtr.Zero);
            Debug.Assert(fieldNames != null);
            Debug.Assert(fieldNames.All(fn => fn != IntPtr.Zero));
            Debug.Assert(fieldSorts == null || fieldSorts.All(fs => fs != IntPtr.Zero));

            var numFields = (uint)(fieldNames?.Length ?? 0);
            constructor = IntPtr.Zero;
            return Native.Z3_mk_tuple_sort(nCtx, name, numFields, fieldNames, fieldSorts, ref constructor, projections);
        }

        #endregion

        #region Propositional
        /// <summary>
        /// The true Term.
        /// </summary>
        public Z3_ast MkTrue() => Native.Z3_mk_true(nCtx);

        /// <summary>
        /// The false Term.
        /// </summary>
        public Z3_ast MkFalse() => Native.Z3_mk_false(nCtx);

        /// <summary>
        /// Creates a Boolean value.
        /// </summary>
        public Z3_ast MkBool(bool value) => value ? MkTrue() : MkFalse();        

        /// <summary>
        /// Create an expression representing <c>t1 iff t2</c>.
        /// </summary>
        public Z3_ast MkIff(Z3_ast t1, Z3_ast t2)
        {
            Debug.Assert(t1 != IntPtr.Zero);
            Debug.Assert(t2 != IntPtr.Zero);

            return Native.Z3_mk_iff(nCtx, t1, t2);
        }
        #endregion

        #region Constants
        /// <summary>
        /// Creates a new Constant of sort <paramref name="range"/> and named <paramref name="name"/>.
        /// </summary>
        public Z3_ast MkConst(string name, Z3_sort range)
        {
            Debug.Assert(!string.IsNullOrEmpty(name));
            Debug.Assert(range != IntPtr.Zero);

            return Native.Z3_mk_const(nCtx, MkStringSymbol(name), range);
        }

        #endregion

        #region Symbol
        /// <summary>
        /// Return a ptr to symbol for string
        /// </summary>
        /// <param name="name"></param>
        /// <returns></returns>
        public Z3_symbol MkStringSymbol(string name)
        {
            Debug.Assert(!string.IsNullOrEmpty(name));

            return Native.Z3_mk_string_symbol(nCtx, name);
        }
        #endregion

        #region Terms
        /// <summary>
        /// Create a new function application.
        /// </summary>
        public Z3_ast MkApp(Z3_func_decl f, params Z3_ast[] args)
        {
            Debug.Assert(f != IntPtr.Zero);
            Debug.Assert(args == null || args.All(a => a != IntPtr.Zero));

            return Native.Z3_mk_app(nCtx, f, (uint)(args?.Length ?? 0), args);
        }

        #endregion

        #region Bound Variables
        /// <summary>
        /// Creates a new bound variable.
        /// </summary>
        /// <param name="index">The de-Bruijn index of the variable</param>
        /// <param name="sort">The sort of the variable</param>
        public Z3_ast MkBound(uint index, Z3_sort sort)
        {
            Debug.Assert(sort != IntPtr.Zero);

            return Native.Z3_mk_bound(nCtx, index, sort);
        }
        #endregion

        #region Bit-vectors
        /// <summary>
        /// Bitwise conjunction.
        /// </summary>
        /// <remarks>The arguments must have a bit-vector sort.</remarks>
        public Z3_ast_vector MkBvAnd(Z3_ast_vector t1, Z3_ast_vector t2)
        {
            Debug.Assert(t1 != IntPtr.Zero);
            Debug.Assert(t2 != IntPtr.Zero);

            return Native.Z3_mk_bvand(nCtx, t1, t2);
        }

        /// <summary>
        /// Bitwise negation.
        /// </summary>
        /// <remarks>The argument must have a bit-vector sort.</remarks>
        public Z3_ast_vector MkBvNot(Z3_ast_vector t)
        {
            Debug.Assert(t != IntPtr.Zero);

            return Native.Z3_mk_bvnot(nCtx, t);
        }

        /// <summary>
        /// Standard two's complement unary minus.
        /// </summary>
        /// <remarks>The arguments must have a bit-vector sort.</remarks>
        public Z3_ast_vector MkBvNeg(Z3_ast_vector t)
        {
            Debug.Assert(t != IntPtr.Zero);

            return Native.Z3_mk_bvneg(nCtx, t);
        }

        /// <summary>
        /// Standard two's complement unary minus.
        /// </summary>
        /// <remarks>The arguments must have a bit-vector sort.</remarks>
        public Z3_ast_vector MkBVNeg(Z3_ast_vector t)
        {
            Debug.Assert(t != IntPtr.Zero);

            return Native.Z3_mk_bvneg(nCtx, t);
        }

        /// <summary>
        /// Two's complement addition.
        /// </summary>
        /// <remarks>The arguments must have the same bit-vector sort.</remarks>
        public Z3_ast_vector MkBvAdd(Z3_ast_vector t1, Z3_ast_vector t2)
        {
            Debug.Assert(t1 != IntPtr.Zero);
            Debug.Assert(t2 != IntPtr.Zero);

            return Native.Z3_mk_bvadd(nCtx, t1, t2);
        }

        /// <summary>
        /// Bit-vector extraction.
        /// </summary>
        /// <remarks>
        /// Extract the bits <paramref name="high"/> down to <paramref name="low"/> from a bitvector of
        /// size <c>m</c> to yield a new bitvector of size <c>n</c>, where
        /// <c>n = high - low + 1</c>.
        /// The argument <paramref name="t"/> must have a bit-vector sort.
        /// </remarks>
        public Z3_ast_vector MkBvExtract(uint high, uint low, Z3_ast_vector t)
        {
            Debug.Assert(t != IntPtr.Zero);

            return Native.Z3_mk_extract(nCtx, high, low, t);
        }

        /// <summary>
        /// Bit-vector sign extension.
        /// </summary>
        /// <remarks>
        /// Sign-extends the given bit-vector to the (signed) equivalent bitvector of
        /// size <c>m+i</c>, where \c m is the size of the given bit-vector.
        /// The argument <paramref name="t"/> must have a bit-vector sort.
        /// </remarks>
        public Z3_ast_vector MkBvSignExt(uint i, Z3_ast_vector t)
        {
            Debug.Assert(t != IntPtr.Zero);

            return Native.Z3_mk_sign_ext(nCtx, i, t);
        }

        /// <summary>
        /// Bit-vector zero extension.
        /// </summary>
        /// <remarks>
        /// Extend the given bit-vector with zeros to the (unsigned) equivalent
        /// bitvector of size <c>m+i</c>, where \c m is the size of the
        /// given bit-vector.
        /// The argument <paramref name="t"/> must have a bit-vector sort.
        /// </remarks>
        public Z3_ast_vector MkBvZeroExt(uint i, Z3_ast_vector t)
        {
            Debug.Assert(t != IntPtr.Zero);

            return Native.Z3_mk_zero_ext(nCtx, i, t);
        }

        /// <summary>
        /// Shift left.
        /// </summary>
        /// <remarks>
        /// It is equivalent to multiplication by <c>2^x</c> where \c x is the value of <paramref name="t2"/>.
        ///
        /// NB. The semantics of shift operations varies between environments. This
        /// definition does not necessarily capture directly the semantics of the
        /// programming language or assembly architecture you are modeling.
        ///
        /// The arguments must have a bit-vector sort.
        /// </remarks>
        public Z3_ast_vector MkBvShl(Z3_ast_vector t1, Z3_ast_vector t2)
        {
            Debug.Assert(t1 != IntPtr.Zero);
            Debug.Assert(t2 != IntPtr.Zero);

            return Native.Z3_mk_bvshl(nCtx, t1, t2);
        }

        /// <summary>
        /// Logical shift right
        /// </summary>
        /// <remarks>
        /// It is equivalent to unsigned division by <c>2^x</c> where \c x is the value of <paramref name="t2"/>.
        ///
        /// NB. The semantics of shift operations varies between environments. This
        /// definition does not necessarily capture directly the semantics of the
        /// programming language or assembly architecture you are modeling.
        ///
        /// The arguments must have a bit-vector sort.
        /// </remarks>
        public Z3_ast_vector MkBvLshr(Z3_ast_vector t1, Z3_ast_vector t2)
        {
            Debug.Assert(t1 != IntPtr.Zero);
            Debug.Assert(t2 != IntPtr.Zero);

            return Native.Z3_mk_bvlshr(nCtx, t1, t2);
        }

        /// <summary>
        /// Arithmetic shift right
        /// </summary>
        /// <remarks>
        /// It is like logical shift right except that the most significant
        /// bits of the result always copy the most significant bit of the
        /// second argument.
        ///
        /// NB. The semantics of shift operations varies between environments. This
        /// definition does not necessarily capture directly the semantics of the
        /// programming language or assembly architecture you are modeling.
        ///
        /// The arguments must have a bit-vector sort.
        /// </remarks>
        public Z3_ast_vector MkBvAshr(Z3_ast_vector t1, Z3_ast_vector t2)
        {
            Debug.Assert(t1 != IntPtr.Zero);
            Debug.Assert(t2 != IntPtr.Zero);

            return Native.Z3_mk_bvashr(nCtx, t1, t2);
        }

        /// <summary>
        /// Two's complement signed less-than
        /// </summary>
        /// <remarks>
        /// The arguments must have the same bit-vector sort.
        /// </remarks>
        public Z3_ast MkBvSlt(Z3_ast_vector t1, Z3_ast_vector t2)
        {
            Debug.Assert(t1 != IntPtr.Zero);
            Debug.Assert(t2 != IntPtr.Zero);

            return Native.Z3_mk_bvslt(nCtx, t1, t2);
        }

        /// <summary>
        /// Two's complement multiplication.
        /// </summary>
        /// <remarks>The arguments must have the same bit-vector sort.</remarks>
        public Z3_ast_vector MkBvMul(Z3_ast_vector t1, Z3_ast_vector t2)
        {
            Debug.Assert(t1 != IntPtr.Zero);
            Debug.Assert(t2 != IntPtr.Zero);

            return Native.Z3_mk_bvmul(nCtx, t1, t2);
        }

        /// <summary>
        /// Unsigned division.
        /// </summary>
        /// <remarks>
        /// It is defined as the floor of <c>t1/t2</c> if \c t2 is
        /// different from zero. If <c>t2</c> is zero, then the result
        /// is undefined.
        /// The arguments must have the same bit-vector sort.
        /// </remarks>
        public Z3_ast_vector MkBvUdiv(Z3_ast_vector t1, Z3_ast_vector t2)
        {
            Debug.Assert(t1 != IntPtr.Zero);
            Debug.Assert(t2 != IntPtr.Zero);

            return Native.Z3_mk_bvudiv(nCtx, t1, t2);
        }

        /// <summary>
        /// Signed division.
        /// </summary>
        /// <remarks>
        /// It is defined in the following way:
        ///
        /// - The \c floor of <c>t1/t2</c> if \c t2 is different from zero, and <c>t1*t2 >= 0</c>.
        ///
        /// - The \c ceiling of <c>t1/t2</c> if \c t2 is different from zero, and <c>t1*t2 &lt; 0</c>.
        ///
        /// If <c>t2</c> is zero, then the result is undefined.
        /// The arguments must have the same bit-vector sort.
        /// </remarks>
        public Z3_ast_vector MkBvSdiv(Z3_ast_vector t1, Z3_ast_vector t2)
        {
            Debug.Assert(t1 != IntPtr.Zero);
            Debug.Assert(t2 != IntPtr.Zero);

            return Native.Z3_mk_bvsdiv(nCtx, t1, t2);
        }

        /// <summary>
        /// Unsigned remainder.
        /// </summary>
        /// <remarks>
        /// It is defined as <c>t1 - (t1 /u t2) * t2</c>, where <c>/u</c> represents unsigned division.
        /// If <c>t2</c> is zero, then the result is undefined.
        /// The arguments must have the same bit-vector sort.
        /// </remarks>
        public Z3_ast_vector MkBvUrem(Z3_ast_vector t1, Z3_ast_vector t2)
        {
            Debug.Assert(t1 != IntPtr.Zero);
            Debug.Assert(t2 != IntPtr.Zero);

            return Native.Z3_mk_bvurem(nCtx, t1, t2);
        }

        /// <summary>
        /// Signed remainder.
        /// </summary>
        /// <remarks>
        /// It is defined as <c>t1 - (t1 /s t2) * t2</c>, where <c>/s</c> represents signed division.
        /// The most significant bit (sign) of the result is equal to the most significant bit of \c t1.
        ///
        /// If <c>t2</c> is zero, then the result is undefined.
        /// The arguments must have the same bit-vector sort.
        /// </remarks>
        public Z3_ast_vector MkBvSrem(Z3_ast_vector t1, Z3_ast_vector t2)
        {
            Debug.Assert(t1 != IntPtr.Zero);
            Debug.Assert(t2 != IntPtr.Zero);

            return Native.Z3_mk_bvsrem(nCtx, t1, t2);
        }

        /// <summary>
        /// Two's complement subtraction.
        /// </summary>
        /// <remarks>The arguments must have the same bit-vector sort.</remarks>
        public Z3_ast_vector MkBvSub(Z3_ast_vector t1, Z3_ast_vector t2)
        {
            Debug.Assert(t1 != IntPtr.Zero);
            Debug.Assert(t2 != IntPtr.Zero);

            return Native.Z3_mk_bvsub(nCtx, t1, t2);
        }

        /// <summary>
        /// Bitwise disjunction.
        /// </summary>
        /// <remarks>The arguments must have a bit-vector sort.</remarks>
        public Z3_ast_vector MkBvOr(Z3_ast_vector t1, Z3_ast_vector t2)
        {
            Debug.Assert(t1 != IntPtr.Zero);
            Debug.Assert(t2 != IntPtr.Zero);

            return Native.Z3_mk_bvor(nCtx, t1, t2);
        }

        /// <summary>
        /// Bitwise XOR.
        /// </summary>
        /// <remarks>The arguments must have a bit-vector sort.</remarks>
        public Z3_ast_vector MkBvXor(Z3_ast_vector t1, Z3_ast_vector t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != IntPtr.Zero);

            return Native.Z3_mk_bvxor(nCtx, t1, t2);
        }
        #endregion

        #region Quantifiers
        /// <summary>
        /// Create a universal Quantifier.
        /// </summary>
        /// <remarks>
        /// Creates a forall formula, where <paramref name="weight"/> is the weight,
        /// <paramref name="patterns"/> is an array of patterns, <paramref name="sorts"/> is an array
        /// with the sorts of the bound variables, <paramref name="names"/> is an array with the
        /// 'names' of the bound variables, and <paramref name="body"/> is the body of the
        /// quantifier. Quantifiers are associated with weights indicating the importance of
        /// using the quantifier during instantiation.
        /// Note that the bound variables are de-Bruijn indices created using <see cref="MkBound"/>.
        /// Z3 applies the convention that the last element in <paramref name="names"/> and
        /// <paramref name="sorts"/> refers to the variable with index 0, the second to last element
        /// of <paramref name="names"/> and <paramref name="sorts"/> refers to the variable
        /// with index 1, etc.
        /// </remarks>
        /// <param name="sorts">the sorts of the bound variables.</param>
        /// <param name="names">names of the bound variables</param>
        /// <param name="body">the body of the quantifier.</param>
        /// <param name="weight">quantifiers are associated with weights indicating the importance of using the quantifier during instantiation. By default, pass the weight 0.</param>
        /// <param name="patterns">array containing the patterns created using <c>MkPattern</c>.</param>
        /// <param name="noPatterns">array containing the anti-patterns created using <c>MkPattern</c>.</param>
        /// <param name="quantifierID">optional symbol to track quantifier.</param>
        /// <param name="skolemID">optional symbol to track skolem constants.</param>
        public Z3_ast MkForall(Z3_sort[] sorts, Z3_symbol[] names, Z3_ast body, uint weight = 1, Z3_ast[] patterns = null, Z3_ast[] noPatterns = null, Symbol quantifierID = null, Symbol skolemID = null)
        {
            return MkQuantifier(true, sorts, names, body, weight, patterns, noPatterns, quantifierID, skolemID);
        }

        /// <summary>
        /// Same as MkForAll but defaults to "forall" = false
        /// Create an existential Quantifier.
        /// </summary>
        /// <param name="sorts"></param>
        /// <param name="names"></param>
        /// <param name="body"></param>
        /// <param name="weight"></param>
        /// <param name="patterns"></param>
        /// <param name="noPatterns"></param>
        /// <param name="quantifierID"></param>
        /// <param name="skolemID"></param>
        /// <returns></returns>
        public Z3_ast MkExists(Z3_sort[] sorts, Z3_symbol[] names, Z3_ast body, uint weight = 1, Z3_ast[] patterns = null, Z3_ast[] noPatterns = null, Symbol quantifierID = null, Symbol skolemID = null)
        {
            return MkQuantifier(false, sorts, names, body, weight, patterns, noPatterns, quantifierID, skolemID);
        }

        /// <summary>
        /// Create a quantified expression either forall or exists
        /// </summary>
        /// <param name="is_forall"></param>
        /// <param name="sorts"></param>
        /// <param name="names"></param>
        /// <param name="body"></param>
        /// <param name="weight"></param>
        /// <param name="patterns"></param>
        /// <param name="noPatterns"></param>
        /// <param name="quantifierID"></param>
        /// <param name="skolemID"></param>
        /// <returns></returns>
        private Z3_ast MkQuantifier(bool is_forall, Z3_sort[] sorts, Z3_symbol[] names, Z3_ast body, uint weight, Z3_ast[] patterns, Z3_ast[] noPatterns, Symbol quantifierID, Symbol skolemID)
        {
            Debug.Assert(sorts != null);
            Debug.Assert(names != null);
            Debug.Assert(body != null);
            Debug.Assert(sorts.Length == names.Length);
            Debug.Assert(sorts.All(s => s != IntPtr.Zero));
            Debug.Assert(names.All(n => n != IntPtr.Zero));
            Debug.Assert(patterns == null || patterns.All(p => p != IntPtr.Zero));
            Debug.Assert(noPatterns == null || noPatterns.All(np => np != IntPtr.Zero));

            if (noPatterns == null && quantifierID == null && skolemID == null)
            {
                return Native.Z3_mk_quantifier(nCtx, (byte)(is_forall ? 1 : 0), weight,
                                (uint)(patterns?.Length ?? 0), patterns,
                                (uint)(sorts?.Length ?? 0), sorts,
                                names,
                                body);
            }
            else
            {
                return Native.Z3_mk_quantifier_ex(nCtx, (byte)(is_forall ? 1 : 0), weight,
                                  AST.GetNativeObject(quantifierID), AST.GetNativeObject(skolemID),
                                  (uint)(patterns?.Length ?? 0), patterns,
                                  (uint)(noPatterns?.Length ?? 0), noPatterns,
                                  (uint)(sorts?.Length ?? 0), sorts,
                                  names,
                                  body);
            }
        }

        #endregion

        #region Options
        /// <summary>
        /// Selects the format used for pretty-printing expressions.
        /// </summary>
        /// <remarks>
        /// The default mode for pretty printing expressions is to produce
        /// SMT-LIB style output where common subexpressions are printed
        /// at each occurrence. The mode is called Z3_PRINT_SMTLIB_FULL.
        /// To print shared common subexpressions only once,
        /// use the Z3_PRINT_LOW_LEVEL mode.
        /// To print in way that conforms to SMT-LIB standards and uses let
        /// expressions to share common sub-expressions use Z3_PRINT_SMTLIB_COMPLIANT.
        /// </remarks>
        /// <seealso cref="AST.ToString()"/>
        /// <seealso cref="Pattern.ToString()"/>
        /// <seealso cref="FuncDecl.ToString()"/>
        /// <seealso cref="Sort.ToString()"/>
        public Z3_ast_print_mode PrintMode
        {
            set { Native.Z3_set_ast_print_mode(nCtx, (uint)value); }
        }

        #endregion

        #region Arrays


        /// <summary>
        /// Create a constant array.
        /// </summary>
        /// <remarks>
        /// The resulting term is an array, such that a <c>select</c>on an arbitrary index
        /// produces the value <c>v</c>.
        /// </remarks>
        public Z3_ast MkConstArray(Z3_sort domain, Z3_ast v)
        {
            Debug.Assert(domain != IntPtr.Zero);
            Debug.Assert(v != IntPtr.Zero);

            return Native.Z3_mk_const_array(nCtx, domain, v);
        }

        /// <summary>
        /// Array update.
        /// </summary>
        /// <remarks>
        /// The node <c>a</c> must have an array sort <c>[domain -> range]</c>,
        /// <c>i</c> must have sort <c>domain</c>,
        /// <c>v</c> must have sort range. The sort of the result is <c>[domain -> range]</c>.
        /// The semantics of this function is given by the theory of arrays described in the SMT-LIB
        /// standard. See http://smtlib.org for more details.
        /// The result of this function is an array that is equal to <c>a</c>
        /// (with respect to <c>select</c>)
        /// on all indices except for <c>i</c>, where it maps to <c>v</c>
        /// (and the <c>select</c> of <c>a</c> with
        /// respect to <c>i</c> may be a different value).
        /// </remarks>
        public Z3_ast MkStore(Z3_ast a, Z3_ast i, Z3_ast v)
        {
            Debug.Assert(a != IntPtr.Zero);
            Debug.Assert(i != IntPtr.Zero);
            Debug.Assert(v != IntPtr.Zero);

            return Native.Z3_mk_store(nCtx, a, i, v);
        }

        /// <summary>
        /// Array read.
        /// </summary>
        /// <remarks>
        /// The argument <c>array</c> is the array and <c>index</c> is the index
        /// of the array that gets read.
        ///
        /// The node <c>array</c> must have an array sort <c>[domain -> range]</c>,
        /// and <c>index</c> must have the sort <c>domain</c>.
        /// The sort of the result is <c>range</c>.
        /// </remarks>
        public Z3_ast MkSelect(Z3_ast array, Z3_ast index)
        {
            Debug.Assert(array != IntPtr.Zero);
            Debug.Assert(index != IntPtr.Zero);

            return Native.Z3_mk_select(nCtx, array, index);
        }

        /// <summary>
        /// Access the array default value.
        /// </summary>
        /// <remarks>
        /// Produces the default range value, for arrays that can be represented as
        /// finite maps with a default range value.
        /// </remarks>
        public Z3_ast MkDefault(Z3_ast a)
        {
            Debug.Assert(a != null);

            return Native.Z3_mk_array_default(nCtx, a);
        }

        #endregion

        #region Function Declarations

        /// <summary>
        /// Creates a new function declaration.
        /// </summary>
        public Z3_func_decl MkFuncDecl(string name, Z3_sort[] domain, Z3_sort range)
        {
            Debug.Assert(!string.IsNullOrEmpty(name));
            Debug.Assert(range != IntPtr.Zero);
            Debug.Assert(domain != null);
            Debug.Assert(domain.All(d => d != IntPtr.Zero));

            var symbol = Native.Z3_mk_string_symbol(nCtx, name);
            return Native.Z3_mk_func_decl(nCtx, symbol, (uint)(domain?.Length ?? 0), domain, range);
        }

        /// <summary>
        /// Creates a new function declaration.
        /// </summary>
        public Z3_func_decl MkFuncDecl(string name, Z3_sort domain, Z3_sort range)
        {
            Debug.Assert(!string.IsNullOrEmpty(name));
            Debug.Assert(range != IntPtr.Zero);
            Debug.Assert(domain != IntPtr.Zero);

            var symbol = Native.Z3_mk_string_symbol(nCtx, name);
            var q = new Z3_sort[] { domain };
            return Native.Z3_mk_func_decl(nCtx, symbol, (uint)q.Length, q, range);
        }

        /// <summary>
        /// Creates a fresh function declaration with a name prefixed with <paramref name="prefix"/>.
        /// </summary>
        public Z3_func_decl MkFreshFuncDecl(string prefix, Z3_sort[] domain, Z3_sort range)
        {
            Debug.Assert(domain != null);
            Debug.Assert(range != IntPtr.Zero);
            Debug.Assert(domain.All(d => d != IntPtr.Zero));

            return Native.Z3_mk_fresh_func_decl(nCtx, prefix, (uint)(domain?.Length ?? 0), domain, range);
        }

        /// <summary>
        /// Creates a new constant function declaration.
        /// </summary>
        public Z3_func_decl MkConstDecl(string name, Z3_sort range)
        {
            Debug.Assert(range != IntPtr.Zero);

            var symbol = Native.Z3_mk_string_symbol(nCtx, name);
            return Native.Z3_mk_func_decl(nCtx, symbol, 0, new IntPtr[0], range);
        }

        /// <summary>
        /// Get domain for a funcdecl
        /// </summary>
        /// <param name="fdecl"></param>
        /// <returns></returns>
        public Z3_sort[] GetDomain(Z3_func_decl fdecl)
        {
            Debug.Assert(fdecl != IntPtr.Zero);

            var sz = Native.Z3_get_domain_size(nCtx, fdecl);
            var domain = new Z3_sort[sz];
            for (uint i = 0; i < sz; i++)
            {
                domain[i] = Native.Z3_get_domain(nCtx, fdecl, i);
            }
            return domain;
        }

        /// <summary>
        /// Get range for a funcdecl
        /// </summary>
        /// <param name="fdecl"></param>
        /// <returns></returns>
        public Z3_sort GetRange(Z3_func_decl fdecl)
        {
            Debug.Assert(fdecl != IntPtr.Zero);

            return Native.Z3_get_range(nCtx, fdecl);
        }

        #endregion

        #region Quantifier Patterns
        /// <summary>
        /// Create a quantifier pattern.
        /// </summary>
        public Z3_pattern MkPattern(params Z3_ast[] terms)
        {
            Debug.Assert(terms != null);
            if (terms == null || terms.Length == 0)
                throw new Z3Exception("Cannot create a pattern from zero terms");

            return Native.Z3_mk_pattern(nCtx, (uint)terms.Length, terms);
        }
        #endregion

        #region Solver

        /// <summary>
        /// Creates a new (incremental) solver.
        /// </summary>
        public NativeSolver MkSimpleSolver()
        {
            Z3_solver nSolver = Native.Z3_mk_simple_solver(nCtx);
            return new NativeSolver(this, nSolver);
        }

        #endregion

        #region Utilities
        /// <summary>
        /// Get the sort kind from IntPtr
        /// </summary>
        public Z3_sort_kind GetSortKind(Z3_sort sort)
        {
            Debug.Assert(sort != IntPtr.Zero);

            return (Z3_sort_kind)Native.Z3_get_sort_kind(nCtx, sort);
        }

        /// <summary>
        /// Get the AST kind from IntPtr
        /// </summary>
        public Z3_ast_kind GetAstKind(Z3_ast ast)
        {
            Debug.Assert(ast != IntPtr.Zero);

            return (Z3_ast_kind)Native.Z3_get_ast_kind(nCtx, ast);
        }

        /// <summary>
        /// Get the Decl kind from IntPtr
        /// </summary>
        public Z3_decl_kind GetDeclKind(Z3_func_decl decl)
        {
            Debug.Assert(decl != IntPtr.Zero);

            return (Z3_decl_kind)Native.Z3_get_decl_kind(nCtx, decl);
        }

        /// <summary>
        /// Get Sort for AST
        /// </summary>
        public Z3_sort GetSort(Z3_ast ast)
        {
            Debug.Assert(ast != IntPtr.Zero);

            return Native.Z3_get_sort(nCtx, ast);
        }

        /// <summary>
        /// Get the arguments for app
        /// </summary>
        /// <param name="app"></param>
        /// <returns></returns>
        public Z3_ast[] GetAppArgs(Z3_app app)
        {
            var numArgs = GetNumArgs(app);
            var args = new Z3_ast[numArgs];
            for (uint i = 0; i < numArgs; i++)
            {
                args[i] = GetAppArg(app, i);
            }
            return args;
        }

        /// <summary>
        /// Return number of arguments for app
        /// </summary>
        /// <param name="app"></param>
        /// <returns></returns>
        public uint GetNumArgs(Z3_app app)
        {
            Debug.Assert(app != IntPtr.Zero);

            return Native.Z3_get_app_num_args(nCtx, app);
        }

        internal Z3_ast GetAppArg(Z3_app app, uint i) => Native.Z3_get_app_arg(nCtx, app, i);

        /// <summary>
        /// Get App Decl from IntPtr
        /// </summary>
        public Z3_func_decl GetAppDecl(Z3_ast ast)
        {
            Debug.Assert(ast != IntPtr.Zero);

            return Native.Z3_get_app_decl(nCtx, ast);
        }

        /// <summary>
        /// Get string name for Decl
        /// </summary>
        /// <param name="decl"></param>
        /// <returns></returns>
        public string GetDeclName(Z3_func_decl decl)
        {
            Debug.Assert(decl != IntPtr.Zero);

            var namePtr = Native.Z3_get_decl_name(nCtx, decl);
            return Marshal.PtrToStringAnsi(namePtr);
        }

        /// <summary>
        /// Get size of BitVector Sort
        /// </summary>
        public uint GetBvSortSize(Z3_sort bvSort)
        {
            Debug.Assert(bvSort != IntPtr.Zero);

            return Native.Z3_get_bv_sort_size(nCtx, bvSort);
        }

        /// <summary>
        /// Get the domain IntPtr for Sort
        /// </summary>
        public Z3_sort GetArraySortDomain(Z3_ast array)
        {
            Debug.Assert(array != IntPtr.Zero);

            return Native.Z3_get_array_sort_domain(nCtx, array);
        }

        /// <summary>
        /// Get the range IntPtr for Sort
        /// </summary>
        public Z3_sort GetArraySortRange(Z3_ast array)
        {
            Debug.Assert(array != IntPtr.Zero);

            return Native.Z3_get_array_sort_range(nCtx, array);
        }

        /// <summary>
        /// Try to get integer from AST
        /// </summary>
        /// <param name="v"></param>
        /// <param name="i"></param>
        /// <returns></returns>
        public bool TryGetNumeralInt(Z3_ast v, out int i)
        {
            Debug.Assert(v != IntPtr.Zero);

            int result = i = 0;
            if (Native.Z3_get_numeral_int(nCtx, v, ref result) == 0) 
            {
                return false;
            }
            i = result;
            return true;
        }

        /// <summary>
        /// Try to get uint from AST
        /// </summary>
        /// <param name="v"></param>
        /// <param name="u"></param>
        /// <returns></returns>
        public bool TryGetNumeralUInt(Z3_ast v, out uint u)
        {
            Debug.Assert(v != IntPtr.Zero);

            uint result = u = 0;
            if (Native.Z3_get_numeral_uint(nCtx, v, ref result) == 0)
            {
                return false;
            }
            u = result;
            return true;
        }

        /// <summary>
        /// Try to get long from AST
        /// </summary>
        /// <param name="v"></param>
        /// <param name="i"></param>
        /// <returns></returns>
        public bool TryGetNumeralInt64(Z3_ast v, out long i)
        {
            Debug.Assert(v != IntPtr.Zero);

            long result = i = 0;
            if (Native.Z3_get_numeral_int64(nCtx, v, ref result) == 0)
            {
                return false;
            }
            i = result;
            return true;
        }

        /// <summary>
        /// Try get ulong from AST
        /// </summary>
        /// <param name="v"></param>
        /// <param name="u"></param>
        /// <returns></returns>
        public bool TryGetNumeralUInt64(Z3_ast v, out ulong u)
        {
            Debug.Assert(v != IntPtr.Zero);

            ulong result = u = 0;
            if (Native.Z3_get_numeral_uint64(nCtx, v, ref result) == 0)
            {
                return false;
            }
            u = result;
            return true;
        }

        /// <summary>
        /// Get string for numeral ast
        /// </summary>
        /// <param name="v"></param>
        /// <returns></returns>
        public string GetNumeralString(Z3_ast v)
        {
            Debug.Assert(v != IntPtr.Zero);
            return Native.Z3_get_numeral_string(nCtx, v);
        }

        /// <summary>
        /// Get printable string representing Z3_ast
        /// </summary>
        /// <param name="ast"></param>
        /// <returns></returns>
        public string ToString(Z3_ast ast)
        {
            Debug.Assert(ast != IntPtr.Zero);

            return Native.Z3_ast_to_string(nCtx, ast);
        }

        /// <summary>
        /// Enable or disable warning messages
        /// </summary>
        /// <param name="turnOn"></param>
        public void ToggleWarningMessages(bool turnOn)
            => Native.Z3_toggle_warning_messages(turnOn ? (byte)1 : (byte)0);

        #endregion

        #region Internal
        internal static Object creation_lock = new Object();
        internal IntPtr m_ctx = IntPtr.Zero;
        internal Native.Z3_error_handler m_n_err_handler = null;
        internal IntPtr nCtx { get { return m_ctx; } }

        internal void NativeErrorHandler(IntPtr ctx, Z3_error_code errorCode)
        {
            // Do-nothing error handler. The wrappers in Z3.Native will throw exceptions upon errors.
        }

        internal void InitContext()
        {
            PrintMode = Z3_ast_print_mode.Z3_PRINT_SMTLIB2_COMPLIANT;
            m_n_err_handler = new Native.Z3_error_handler(NativeErrorHandler); // keep reference so it doesn't get collected.
            Native.Z3_set_error_handler(m_ctx, m_n_err_handler);

            GC.SuppressFinalize(this);
        }

        #endregion

        #region Tracing
        /// <summary>
        /// Enable trace to file
        /// </summary>
        /// <param name="tag">Tag to trace</param>
        public static void EnableTrace(string tag)
        {
            Debug.Assert(!string.IsNullOrEmpty(tag));
            Native.Z3_enable_trace(tag);
        }

        #endregion

        #region Dispose

        /// <summary>
        /// Disposes of the context.
        /// </summary>
        public void Dispose()
        {
            if (m_ctx != IntPtr.Zero)
            {
                m_n_err_handler = null;
                IntPtr ctx = m_ctx;
                m_ctx = IntPtr.Zero;
                Native.Z3_del_context(ctx);
            }
            else
                GC.ReRegisterForFinalize(this);
        }
        #endregion


        /// <summary>
        /// Utility to convert a vector object of ast to a .Net array
        /// </summary>
        /// <param name="vec"></param>
        /// <returns></returns>
        public Z3_ast[] ToArray(Z3_ast_vector vec)
        {
            Native.Z3_ast_vector_inc_ref(nCtx, vec);
            var sz = Native.Z3_ast_vector_size(nCtx, vec);
            var result = new Z3_ast[sz];
            for (uint i = 0; i < sz; ++i)
                result[i] = Native.Z3_ast_vector_get(nCtx, vec, i);
            Native.Z3_ast_vector_dec_ref(nCtx, vec);
            return result;
        }

        /// <summary>
        /// Retrieve statistics as an array of entries
        /// </summary>
        /// <param name="stats"></param>
        /// <returns></returns>
        public Statistics.Entry[] GetStatistics(Z3_stats stats)
        {
            Native.Z3_stats_inc_ref(nCtx, stats);
            var result = Statistics.NativeEntries(nCtx, stats);
            Native.Z3_stats_dec_ref(nCtx, stats);
            return result;
        }

    }
}