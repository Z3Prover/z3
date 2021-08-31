﻿/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    Context.cs

Abstract:

    Z3 Managed API: Context

Author:

    Christoph Wintersteiger (cwinter) 2012-03-15

Notes:

--*/

using System;
using System.Diagnostics;
using System.Collections.Generic;
using System.Runtime.InteropServices;
using System.Linq;

namespace Microsoft.Z3
{
    /// <summary>
    /// The main interaction with Z3 happens via the Context.
    /// </summary>
    public class Context : IDisposable
    {
        #region Constructors
        /// <summary>
        /// Constructor.
        /// </summary>
        public Context()
            : base()
        {
            lock (creation_lock)
            {
                m_ctx = Native.Z3_mk_context_rc(IntPtr.Zero);
                InitContext();
            }
        }

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
        public Context(Dictionary<string, string> settings)
            : base()
        {
            Debug.Assert(settings != null);

            lock (creation_lock)
            {
                IntPtr cfg = Native.Z3_mk_config();
                foreach (KeyValuePair<string, string> kv in settings)
                    Native.Z3_set_param_value(cfg, kv.Key, kv.Value);
                m_ctx = Native.Z3_mk_context_rc(cfg);
                Native.Z3_del_config(cfg);
                InitContext();
            }
        }
        #endregion

        #region Symbols
        /// <summary>
        /// Creates a new symbol using an integer.
        /// </summary>
        /// <remarks>
        /// Not all integers can be passed to this function.
        /// The legal range of unsigned integers is 0 to 2^30-1.
        /// </remarks>
        public IntSymbol MkSymbol(int i)
        {
            return new IntSymbol(this, i);
        }

        /// <summary>
        /// Create a symbol using a string.
        /// </summary>
        public StringSymbol MkSymbol(string name)
        {
            return new StringSymbol(this, name);
        }

        /// <summary>
        /// Create an array of symbols.
        /// </summary>
        internal Symbol[] MkSymbols(string[] names)
        {
            if (names == null) return null;
            Symbol[] result = new Symbol[names.Length];
            for (int i = 0; i < names.Length; ++i) result[i] = MkSymbol(names[i]);
            return result;
        }
        #endregion

        #region Sorts
        private BoolSort m_boolSort = null;
        private IntSort m_intSort = null;
        private RealSort m_realSort = null;
        private SeqSort m_stringSort = null;
        private CharSort m_charSort = null;

        /// <summary>
        /// Retrieves the Boolean sort of the context.
        /// </summary>
        public BoolSort BoolSort
        {
            get
            {
                if (m_boolSort == null) m_boolSort = new BoolSort(this); return m_boolSort;
            }
        }

        /// <summary>
        /// Retrieves the Integer sort of the context.
        /// </summary>
        public IntSort IntSort
        {
            get
            {
                if (m_intSort == null) m_intSort = new IntSort(this); return m_intSort;
            }
        }


        /// <summary>
        /// Retrieves the Real sort of the context.
        /// </summary>
        public RealSort RealSort
        {
            get
            {
                if (m_realSort == null) m_realSort = new RealSort(this); return m_realSort;
            }
        }

        /// <summary>
        /// Retrieves the String sort of the context.
        /// </summary>
        public CharSort CharSort
        {
            get
            {
                if (m_charSort == null) m_charSort = new CharSort(this); return m_charSort;
            }
        }


        /// <summary>
        /// Retrieves the String sort of the context.
        /// </summary>
        public SeqSort StringSort
        {
            get
            {
                if (m_stringSort == null) m_stringSort = new SeqSort(this, Native.Z3_mk_string_sort(nCtx));
                return m_stringSort;
            }
        }


        /// <summary>
        /// Create a new Boolean sort.
        /// </summary>
        public BoolSort MkBoolSort()
        {
            return new BoolSort(this);
        }

        /// <summary>
        /// Create a new uninterpreted sort.
        /// </summary>
        public UninterpretedSort MkUninterpretedSort(Symbol s)
        {
            Debug.Assert(s != null);

            CheckContextMatch(s);
            return new UninterpretedSort(this, s);
        }

        /// <summary>
        /// Create a new uninterpreted sort.
        /// </summary>
        public UninterpretedSort MkUninterpretedSort(string str)
        {

            return MkUninterpretedSort(MkSymbol(str));
        }

        /// <summary>
        /// Create a new integer sort.
        /// </summary>
        public IntSort MkIntSort()
        {

            return new IntSort(this);
        }

        /// <summary>
        /// Create a real sort.
        /// </summary>
        public RealSort MkRealSort()
        {
            return new RealSort(this);
        }

        /// <summary>
        /// Create a new bit-vector sort.
        /// </summary>
        public BitVecSort MkBitVecSort(uint size)
        {
            return new BitVecSort(this, Native.Z3_mk_bv_sort(nCtx, size));
        }


        /// <summary>
        /// Create a new sequence sort.
        /// </summary>
        public SeqSort MkSeqSort(Sort s)
        {
            Debug.Assert(s != null);
            return new SeqSort(this, Native.Z3_mk_seq_sort(nCtx, s.NativeObject));
        }

        /// <summary>
        /// Create a new regular expression sort.
        /// </summary>
        public ReSort MkReSort(SeqSort s)
        {
            Debug.Assert(s != null);
            return new ReSort(this, Native.Z3_mk_re_sort(nCtx, s.NativeObject));
        }

        /// <summary>
        /// Create a new array sort.
        /// </summary>
        public ArraySort MkArraySort(Sort domain, Sort range)
        {
            Debug.Assert(domain != null);
            Debug.Assert(range != null);

            CheckContextMatch(domain);
            CheckContextMatch(range);
            return new ArraySort(this, domain, range);
        }

        /// <summary>
        /// Create a new n-ary array sort.
        /// </summary>
        public ArraySort MkArraySort(Sort[] domain, Sort range)
        {
            Debug.Assert(domain != null);
            Debug.Assert(range != null);

            CheckContextMatch<Sort>(domain);
            CheckContextMatch(range);
            return new ArraySort(this, domain, range);
        }

        /// <summary>
        /// Create a new tuple sort.
        /// </summary>
        public TupleSort MkTupleSort(Symbol name, Symbol[] fieldNames, Sort[] fieldSorts)
        {
            Debug.Assert(name != null);
            Debug.Assert(fieldNames != null);
            Debug.Assert(fieldNames.All(fn => fn != null));
            Debug.Assert(fieldSorts == null || fieldSorts.All(fs => fs != null));

            CheckContextMatch(name);
            CheckContextMatch<Symbol>(fieldNames);
            CheckContextMatch<Sort>(fieldSorts);
            return new TupleSort(this, name, (uint)fieldNames.Length, fieldNames, fieldSorts);
        }

        /// <summary>
        /// Create a new enumeration sort.
        /// </summary>
        public EnumSort MkEnumSort(Symbol name, params Symbol[] enumNames)
        {
            Debug.Assert(name != null);
            Debug.Assert(enumNames != null);
            Debug.Assert(enumNames.All(f => f != null));


            CheckContextMatch(name);
            CheckContextMatch<Symbol>(enumNames);
            return new EnumSort(this, name, enumNames);
        }

        /// <summary>
        /// Create a new enumeration sort.
        /// </summary>
        public EnumSort MkEnumSort(string name, params string[] enumNames)
        {
            Debug.Assert(enumNames != null);

            return new EnumSort(this, MkSymbol(name), MkSymbols(enumNames));
        }

        /// <summary>
        /// Create a new list sort.
        /// </summary>
        public ListSort MkListSort(Symbol name, Sort elemSort)
        {
            Debug.Assert(name != null);
            Debug.Assert(elemSort != null);

            CheckContextMatch(name);
            CheckContextMatch(elemSort);
            return new ListSort(this, name, elemSort);
        }

        /// <summary>
        /// Create a new list sort.
        /// </summary>
        public ListSort MkListSort(string name, Sort elemSort)
        {
            Debug.Assert(elemSort != null);

            CheckContextMatch(elemSort);
            return new ListSort(this, MkSymbol(name), elemSort);
        }

        /// <summary>
        /// Create a new finite domain sort.
        /// <returns>The result is a sort</returns>
        /// </summary>
        /// <param name="name">The name used to identify the sort</param>
        /// <param name="size">The size of the sort</param>
        public FiniteDomainSort MkFiniteDomainSort(Symbol name, ulong size)
        {
            Debug.Assert(name != null);

            CheckContextMatch(name);
            return new FiniteDomainSort(this, name, size);
        }

        /// <summary>
        /// Create a new finite domain sort.
        /// <returns>The result is a sort</returns>
        /// Elements of the sort are created using <seealso cref="MkNumeral(ulong, Sort)"/>,
        /// and the elements range from 0 to <tt>size-1</tt>.
        /// </summary>
        /// <param name="name">The name used to identify the sort</param>
        /// <param name="size">The size of the sort</param>
        public FiniteDomainSort MkFiniteDomainSort(string name, ulong size)
        {

            return new FiniteDomainSort(this, MkSymbol(name), size);
        }


        #region Datatypes
        /// <summary>
        /// Create a datatype constructor.
        /// </summary>
        /// <param name="name">constructor name</param>
        /// <param name="recognizer">name of recognizer function.</param>
        /// <param name="fieldNames">names of the constructor fields.</param>
        /// <param name="sorts">field sorts, 0 if the field sort refers to a recursive sort.</param>
        /// <param name="sortRefs">reference to datatype sort that is an argument to the constructor;
        /// if the corresponding sort reference is 0, then the value in sort_refs should be an index
        /// referring to one of the recursive datatypes that is declared.</param>
        public Constructor MkConstructor(Symbol name, Symbol recognizer, Symbol[] fieldNames = null, Sort[] sorts = null, uint[] sortRefs = null)
        {
            Debug.Assert(name != null);
            Debug.Assert(recognizer != null);

            return new Constructor(this, name, recognizer, fieldNames, sorts, sortRefs);
        }

        /// <summary>
        /// Create a datatype constructor.
        /// </summary>
        /// <param name="name"></param>
        /// <param name="recognizer"></param>
        /// <param name="fieldNames"></param>
        /// <param name="sorts"></param>
        /// <param name="sortRefs"></param>
        /// <returns></returns>
        public Constructor MkConstructor(string name, string recognizer, string[] fieldNames = null, Sort[] sorts = null, uint[] sortRefs = null)
        {

            return new Constructor(this, MkSymbol(name), MkSymbol(recognizer), MkSymbols(fieldNames), sorts, sortRefs);
        }

        /// <summary>
        /// Create a new datatype sort.
        /// </summary>
        public DatatypeSort MkDatatypeSort(Symbol name, Constructor[] constructors)
        {
            Debug.Assert(name != null);
            Debug.Assert(constructors != null);
            Debug.Assert(constructors.All(c => c != null));


            CheckContextMatch(name);
            CheckContextMatch<Constructor>(constructors);
            return new DatatypeSort(this, name, constructors);
        }

        /// <summary>
        /// Create a new datatype sort.
        /// </summary>
        public DatatypeSort MkDatatypeSort(string name, Constructor[] constructors)
        {
            Debug.Assert(constructors != null);
            Debug.Assert(constructors.All(c => c != null));

            CheckContextMatch<Constructor>(constructors);
            return new DatatypeSort(this, MkSymbol(name), constructors);
        }

        /// <summary>
        /// Create mutually recursive datatypes.
        /// </summary>
        /// <param name="names">names of datatype sorts</param>
        /// <param name="c">list of constructors, one list per sort.</param>
        public DatatypeSort[] MkDatatypeSorts(Symbol[] names, Constructor[][] c)
        {
            Debug.Assert(names != null);
            Debug.Assert(c != null);
            Debug.Assert(names.Length == c.Length);
            //Debug.Assert(Contract.ForAll(0, c.Length, j => c[j] != null));
            Debug.Assert(names.All(name => name != null));

            CheckContextMatch<Symbol>(names);
            uint n = (uint)names.Length;
            ConstructorList[] cla = new ConstructorList[n];
            IntPtr[] n_constr = new IntPtr[n];
            for (uint i = 0; i < n; i++)
            {
                Constructor[] constructor = c[i];
                CheckContextMatch<Constructor>(constructor);
                cla[i] = new ConstructorList(this, constructor);
                n_constr[i] = cla[i].NativeObject;
            }
            IntPtr[] n_res = new IntPtr[n];
            Native.Z3_mk_datatypes(nCtx, n, Symbol.ArrayToNative(names), n_res, n_constr);
            DatatypeSort[] res = new DatatypeSort[n];
            for (uint i = 0; i < n; i++)
                res[i] = new DatatypeSort(this, n_res[i]);
            return res;
        }

        /// <summary>
        ///  Create mutually recursive data-types.
        /// </summary>
        /// <param name="names"></param>
        /// <param name="c"></param>
        /// <returns></returns>
        public DatatypeSort[] MkDatatypeSorts(string[] names, Constructor[][] c)
        {
            Debug.Assert(names != null);
            Debug.Assert(c != null);
            Debug.Assert(names.Length == c.Length);
            //Debug.Assert(Contract.ForAll(0, c.Length, j => c[j] != null));
            //Debug.Assert(names.All(name => name != null));

            return MkDatatypeSorts(MkSymbols(names), c);
        }

        /// <summary>
        /// Update a datatype field at expression t with value v.
        /// The function performs a record update at t. The field
        /// that is passed in as argument is updated with value v,
        /// the remaining fields of t are unchanged.
            /// </summary>
        public Expr MkUpdateField(FuncDecl field, Expr t, Expr v)
        {
            return Expr.Create(this, Native.Z3_datatype_update_field(
                                        nCtx, field.NativeObject,
                                        t.NativeObject, v.NativeObject));
        }

        #endregion
        #endregion

        #region Function Declarations
        /// <summary>
        /// Creates a new function declaration.
        /// </summary>
        public FuncDecl MkFuncDecl(Symbol name, Sort[] domain, Sort range)
        {
            Debug.Assert(name != null);
            Debug.Assert(range != null);
            Debug.Assert(domain.All(d => d != null));

            CheckContextMatch(name);
            CheckContextMatch<Sort>(domain);
            CheckContextMatch(range);
            return new FuncDecl(this, name, domain, range);
        }

        /// <summary>
        /// Creates a new function declaration.
        /// </summary>
        public FuncDecl MkFuncDecl(Symbol name, Sort domain, Sort range)
        {
            Debug.Assert(name != null);
            Debug.Assert(domain != null);
            Debug.Assert(range != null);

            CheckContextMatch(name);
            CheckContextMatch(domain);
            CheckContextMatch(range);
            Sort[] q = new Sort[] { domain };
            return new FuncDecl(this, name, q, range);
        }

        /// <summary>
        /// Creates a new function declaration.
        /// </summary>
        public FuncDecl MkFuncDecl(string name, Sort[] domain, Sort range)
        {
            Debug.Assert(range != null);
            Debug.Assert(domain.All(d => d != null));

            CheckContextMatch<Sort>(domain);
            CheckContextMatch(range);
            return new FuncDecl(this, MkSymbol(name), domain, range);
        }

        /// <summary>
        /// Creates a new recursive function declaration.
        /// </summary>
        public FuncDecl MkRecFuncDecl(string name, Sort[] domain, Sort range)
        {
            Debug.Assert(range != null);
            Debug.Assert(domain.All(d => d != null));

            CheckContextMatch<Sort>(domain);
            CheckContextMatch(range);
            return new FuncDecl(this, MkSymbol(name), domain, range, true);
        }

        /// <summary>
        /// Bind a definition to a recursive function declaration.
        /// The function must have previously been created using
        /// MkRecFuncDecl. The body may contain recursive uses of the function or
        /// other mutually recursive functions. 
        /// </summary>
    public void AddRecDef(FuncDecl f, Expr[] args, Expr body) 
    {
        CheckContextMatch(f);
        CheckContextMatch<Expr>(args);
        CheckContextMatch(body);
            IntPtr[] argsNative = AST.ArrayToNative(args);
        Native.Z3_add_rec_def(nCtx, f.NativeObject, (uint)args.Length, argsNative, body.NativeObject);
    }	

        /// <summary>
        /// Creates a new function declaration.
        /// </summary>
        public FuncDecl MkFuncDecl(string name, Sort domain, Sort range)
        {
            Debug.Assert(range != null);
            Debug.Assert(domain != null);

            CheckContextMatch(domain);
            CheckContextMatch(range);
            Sort[] q = new Sort[] { domain };
            return new FuncDecl(this, MkSymbol(name), q, range);
        }

        /// <summary>
        /// Creates a fresh function declaration with a name prefixed with <paramref name="prefix"/>.
        /// </summary>
        /// <seealso cref="MkFuncDecl(string,Sort,Sort)"/>
        /// <seealso cref="MkFuncDecl(string,Sort[],Sort)"/>
        public FuncDecl MkFreshFuncDecl(string prefix, Sort[] domain, Sort range)
        {
            Debug.Assert(range != null);
            Debug.Assert(domain.All(d => d != null));

            CheckContextMatch<Sort>(domain);
            CheckContextMatch(range);
            return new FuncDecl(this, prefix, domain, range);
        }

        /// <summary>
        /// Creates a new constant function declaration.
        /// </summary>
        public FuncDecl MkConstDecl(Symbol name, Sort range)
        {
            Debug.Assert(name != null);
            Debug.Assert(range != null);

            CheckContextMatch(name);
            CheckContextMatch(range);
            return new FuncDecl(this, name, null, range);
        }

        /// <summary>
        /// Creates a new constant function declaration.
        /// </summary>
        public FuncDecl MkConstDecl(string name, Sort range)
        {
            Debug.Assert(range != null);

            CheckContextMatch(range);
            return new FuncDecl(this, MkSymbol(name), null, range);
        }

        /// <summary>
        /// Creates a fresh constant function declaration with a name prefixed with <paramref name="prefix"/>.
        /// </summary>
        /// <seealso cref="MkFuncDecl(string,Sort,Sort)"/>
        /// <seealso cref="MkFuncDecl(string,Sort[],Sort)"/>
        public FuncDecl MkFreshConstDecl(string prefix, Sort range)
        {
            Debug.Assert(range != null);

            CheckContextMatch(range);
            return new FuncDecl(this, prefix, null, range);
        }
        #endregion

        #region Bound Variables
        /// <summary>
        /// Creates a new bound variable.
        /// </summary>
        /// <param name="index">The de-Bruijn index of the variable</param>
        /// <param name="ty">The sort of the variable</param>
        public Expr MkBound(uint index, Sort ty)
        {
            Debug.Assert(ty != null);

            return Expr.Create(this, Native.Z3_mk_bound(nCtx, index, ty.NativeObject));
        }
        #endregion

        #region Quantifier Patterns
        /// <summary>
        /// Create a quantifier pattern.
        /// </summary>
        public Pattern MkPattern(params Expr[] terms)
        {
            Debug.Assert(terms != null);
            if (terms.Length == 0)
                throw new Z3Exception("Cannot create a pattern from zero terms");

            IntPtr[] termsNative = AST.ArrayToNative(terms);
            return new Pattern(this, Native.Z3_mk_pattern(nCtx, (uint)terms.Length, termsNative));
        }
        #endregion

        #region Constants
        /// <summary>
        /// Creates a new Constant of sort <paramref name="range"/> and named <paramref name="name"/>.
        /// </summary>
        public Expr MkConst(Symbol name, Sort range)
        {
            Debug.Assert(name != null);
            Debug.Assert(range != null);

            CheckContextMatch(name);
            CheckContextMatch(range);

            return Expr.Create(this, Native.Z3_mk_const(nCtx, name.NativeObject, range.NativeObject));
        }

        /// <summary>
        /// Creates a new Constant of sort <paramref name="range"/> and named <paramref name="name"/>.
        /// </summary>
        public Expr MkConst(string name, Sort range)
        {
            Debug.Assert(range != null);

            return MkConst(MkSymbol(name), range);
        }

        /// <summary>
        /// Creates a fresh Constant of sort <paramref name="range"/> and a
        /// name prefixed with <paramref name="prefix"/>.
        /// </summary>
        public Expr MkFreshConst(string prefix, Sort range)
        {
            Debug.Assert(range != null);

            CheckContextMatch(range);
            return Expr.Create(this, Native.Z3_mk_fresh_const(nCtx, prefix, range.NativeObject));
        }

        /// <summary>
        /// Creates a fresh constant from the FuncDecl <paramref name="f"/>.
        /// </summary>
        /// <param name="f">A decl of a 0-arity function</param>
        public Expr MkConst(FuncDecl f)
        {
            Debug.Assert(f != null);

            return MkApp(f);
        }

        /// <summary>
        /// Create a Boolean constant.
        /// </summary>
        public BoolExpr MkBoolConst(Symbol name)
        {
            Debug.Assert(name != null);

            return (BoolExpr)MkConst(name, BoolSort);
        }

        /// <summary>
        /// Create a Boolean constant.
        /// </summary>
        public BoolExpr MkBoolConst(string name)
        {

            return (BoolExpr)MkConst(MkSymbol(name), BoolSort);
        }

        /// <summary>
        /// Creates an integer constant.
        /// </summary>
        public IntExpr MkIntConst(Symbol name)
        {
            Debug.Assert(name != null);

            return (IntExpr)MkConst(name, IntSort);
        }

        /// <summary>
        /// Creates an integer constant.
        /// </summary>
        public IntExpr MkIntConst(string name)
        {
            Debug.Assert(name != null);

            return (IntExpr)MkConst(name, IntSort);
        }

        /// <summary>
        /// Creates a real constant.
        /// </summary>
        public RealExpr MkRealConst(Symbol name)
        {
            Debug.Assert(name != null);

            return (RealExpr)MkConst(name, RealSort);
        }

        /// <summary>
        /// Creates a real constant.
        /// </summary>
        public RealExpr MkRealConst(string name)
        {

            return (RealExpr)MkConst(name, RealSort);
        }

        /// <summary>
        /// Creates a bit-vector constant.
        /// </summary>
        public BitVecExpr MkBVConst(Symbol name, uint size)
        {
            Debug.Assert(name != null);

            return (BitVecExpr)MkConst(name, MkBitVecSort(size));
        }

        /// <summary>
        /// Creates a bit-vector constant.
        /// </summary>
        public BitVecExpr MkBVConst(string name, uint size)
        {

            return (BitVecExpr)MkConst(name, MkBitVecSort(size));
        }
        #endregion

        #region Terms
        /// <summary>
        /// Create a new function application.
        /// </summary>
        public Expr MkApp(FuncDecl f, params Expr[] args)
        {
            Debug.Assert(f != null);
            Debug.Assert(args == null || args.All(a => a != null));

            CheckContextMatch(f);
            CheckContextMatch<Expr>(args);
            return Expr.Create(this, f, args);
        }

        /// <summary>
        /// Create a new function application.
        /// </summary>
        public Expr MkApp(FuncDecl f, IEnumerable<Expr> args)
        {
            Debug.Assert(f != null);
            Debug.Assert(args == null || args.All( a => a != null));

            CheckContextMatch(f);
            CheckContextMatch(args);
            return Expr.Create(this, f, args.ToArray());
        }

        #region Propositional
        /// <summary>
        /// The true Term.
        /// </summary>
        public BoolExpr MkTrue()
        {

            return new BoolExpr(this, Native.Z3_mk_true(nCtx));
        }

        /// <summary>
        /// The false Term.
        /// </summary>
        public BoolExpr MkFalse()
        {

            return new BoolExpr(this, Native.Z3_mk_false(nCtx));
        }

        /// <summary>
        /// Creates a Boolean value.
        /// </summary>
        public BoolExpr MkBool(bool value)
        {

            return value ? MkTrue() : MkFalse();
        }

        /// <summary>
        /// Creates the equality <paramref name="x"/> = <paramref name="y"/>.
        /// </summary>
        public BoolExpr MkEq(Expr x, Expr y)
        {
            Debug.Assert(x != null);
            Debug.Assert(y != null);

            CheckContextMatch(x);
            CheckContextMatch(y);
            return new BoolExpr(this, Native.Z3_mk_eq(nCtx, x.NativeObject, y.NativeObject));
        }

        /// <summary>
        /// Creates a <c>distinct</c> term.
        /// </summary>
        public BoolExpr MkDistinct(params Expr[] args)
        {
            Debug.Assert(args != null);
            Debug.Assert(args.All(a => a != null));


            CheckContextMatch<Expr>(args);
            return new BoolExpr(this, Native.Z3_mk_distinct(nCtx, (uint)args.Length, AST.ArrayToNative(args)));
        }

        /// <summary>
        ///  Mk an expression representing <c>not(a)</c>.
        /// </summary>
        public BoolExpr MkNot(BoolExpr a)
        {
            Debug.Assert(a != null);

            CheckContextMatch(a);
            return new BoolExpr(this, Native.Z3_mk_not(nCtx, a.NativeObject));
        }

        /// <summary>
        ///  Create an expression representing an if-then-else: <c>ite(t1, t2, t3)</c>.
        /// </summary>
        /// <param name="t1">An expression with Boolean sort</param>
        /// <param name="t2">An expression </param>
        /// <param name="t3">An expression with the same sort as <paramref name="t2"/></param>
        public Expr MkITE(BoolExpr t1, Expr t2, Expr t3)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);
            Debug.Assert(t3 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            CheckContextMatch(t3);
            return Expr.Create(this, Native.Z3_mk_ite(nCtx, t1.NativeObject, t2.NativeObject, t3.NativeObject));
        }

        /// <summary>
        /// Create an expression representing <c>t1 iff t2</c>.
        /// </summary>
        public BoolExpr MkIff(BoolExpr t1, BoolExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BoolExpr(this, Native.Z3_mk_iff(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Create an expression representing <c>t1 -> t2</c>.
        /// </summary>
        public BoolExpr MkImplies(BoolExpr t1, BoolExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BoolExpr(this, Native.Z3_mk_implies(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Create an expression representing <c>t1 xor t2</c>.
        /// </summary>
        public BoolExpr MkXor(BoolExpr t1, BoolExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BoolExpr(this, Native.Z3_mk_xor(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Create an expression representing <c>t1 xor t2 xor t3 ... </c>.
        /// </summary>
        public BoolExpr MkXor(IEnumerable<BoolExpr> ts)
        {
            Debug.Assert(ts != null);
            Debug.Assert(ts.All(a => a != null));
            CheckContextMatch<BoolExpr>(ts);
            BoolExpr r = null;
            foreach (var t in ts) {
                if (r == null) 
                   r = t;
                else
                   r = MkXor(r, t);
            }
            if (r == null) 
               r = MkTrue();
            return r;
        }

        /// <summary>
        /// Create an expression representing <c>t[0] and t[1] and ...</c>.
        /// </summary>
        public BoolExpr MkAnd(params BoolExpr[] t)
        {
            Debug.Assert(t != null);
            Debug.Assert(t.All(a => a != null));

            CheckContextMatch<BoolExpr>(t);
            return new BoolExpr(this, Native.Z3_mk_and(nCtx, (uint)t.Length, AST.ArrayToNative(t)));
        }

        /// <summary>
        /// Create an expression representing <c>t[0] and t[1] and ...</c>.
        /// </summary>
        public BoolExpr MkAnd(IEnumerable<BoolExpr> t)
        {
            Debug.Assert(t != null);
            Debug.Assert(t.All(a => a != null));
            CheckContextMatch<BoolExpr>(t);
            return new BoolExpr(this, Native.Z3_mk_and(nCtx, (uint)t.Count(), AST.EnumToNative(t)));
        }

        /// <summary>
        /// Create an expression representing <c>t[0] or t[1] or ...</c>.
        /// </summary>
        public BoolExpr MkOr(params BoolExpr[] t)
        {
            Debug.Assert(t != null);
            Debug.Assert(t.All(a => a != null));

            CheckContextMatch<BoolExpr>(t);
            return new BoolExpr(this, Native.Z3_mk_or(nCtx, (uint)t.Length, AST.ArrayToNative(t)));
        }


        /// <summary>
        /// Create an expression representing <c>t[0] or t[1] or ...</c>.
        /// </summary>
        public BoolExpr MkOr(IEnumerable<BoolExpr> t)
        {
            Debug.Assert(t != null);
            Debug.Assert(t.All(a => a != null));

            CheckContextMatch(t);
            return new BoolExpr(this, Native.Z3_mk_or(nCtx, (uint)t.Count(), AST.EnumToNative(t)));
        }

        #endregion

        #region Arithmetic
        /// <summary>
        /// Create an expression representing <c>t[0] + t[1] + ...</c>.
        /// </summary>
        public ArithExpr MkAdd(params ArithExpr[] t)
        {
            Debug.Assert(t != null);
            Debug.Assert(t.All(a => a != null));

            CheckContextMatch<ArithExpr>(t);
            return (ArithExpr)Expr.Create(this, Native.Z3_mk_add(nCtx, (uint)t.Length, AST.ArrayToNative(t)));
        }

        /// <summary>
        /// Create an expression representing <c>t[0] + t[1] + ...</c>.
        /// </summary>
        public ArithExpr MkAdd(IEnumerable<ArithExpr> t)
        {
            Debug.Assert(t != null);
            Debug.Assert(t.All(a => a != null));

            CheckContextMatch(t);
            return (ArithExpr)Expr.Create(this, Native.Z3_mk_add(nCtx, (uint)t.Count(), AST.EnumToNative(t)));
        }

        /// <summary>
        /// Create an expression representing <c>t[0] * t[1] * ...</c>.
        /// </summary>
        public ArithExpr MkMul(params ArithExpr[] t)
        {
            Debug.Assert(t != null);
            Debug.Assert(t.All(a => a != null));

            CheckContextMatch<ArithExpr>(t);
            return (ArithExpr)Expr.Create(this, Native.Z3_mk_mul(nCtx, (uint)t.Length, AST.ArrayToNative(t)));
        }

        /// <summary>
        /// Create an expression representing <c>t[0] * t[1] * ...</c>.
        /// </summary>
        public ArithExpr MkMul(IEnumerable<ArithExpr> t)
        {
            Debug.Assert(t != null);
            Debug.Assert(t.All(a => a != null));

            CheckContextMatch<ArithExpr>(t);
            return (ArithExpr)Expr.Create(this, Native.Z3_mk_mul(nCtx, (uint)t.Count(), AST.EnumToNative(t)));
        }

        /// <summary>
        /// Create an expression representing <c>t[0] - t[1] - ...</c>.
        /// </summary>
        public ArithExpr MkSub(params ArithExpr[] t)
        {
            Debug.Assert(t != null);
            Debug.Assert(t.All(a => a != null));

            CheckContextMatch<ArithExpr>(t);
            return (ArithExpr)Expr.Create(this, Native.Z3_mk_sub(nCtx, (uint)t.Length, AST.ArrayToNative(t)));
        }

        /// <summary>
        /// Create an expression representing <c>-t</c>.
        /// </summary>
        public ArithExpr MkUnaryMinus(ArithExpr t)
        {
            Debug.Assert(t != null);

            CheckContextMatch(t);
            return (ArithExpr)Expr.Create(this, Native.Z3_mk_unary_minus(nCtx, t.NativeObject));
        }

        /// <summary>
        /// Create an expression representing <c>t1 / t2</c>.
        /// </summary>
        public ArithExpr MkDiv(ArithExpr t1, ArithExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return (ArithExpr)Expr.Create(this, Native.Z3_mk_div(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Create an expression representing <c>t1 mod t2</c>.
        /// </summary>
        /// <remarks>The arguments must have int type.</remarks>
        public IntExpr MkMod(IntExpr t1, IntExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new IntExpr(this, Native.Z3_mk_mod(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Create an expression representing <c>t1 rem t2</c>.
        /// </summary>
        /// <remarks>The arguments must have int type.</remarks>
        public IntExpr MkRem(IntExpr t1, IntExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new IntExpr(this, Native.Z3_mk_rem(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Create an expression representing <c>t1 ^ t2</c>.
        /// </summary>
        public ArithExpr MkPower(ArithExpr t1, ArithExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return (ArithExpr)Expr.Create(this, Native.Z3_mk_power(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Create an expression representing <c>t1 &lt; t2</c>
        /// </summary>
        public BoolExpr MkLt(ArithExpr t1, ArithExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BoolExpr(this, Native.Z3_mk_lt(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Create an expression representing <c>t1 &lt;= t2</c>
        /// </summary>
        public BoolExpr MkLe(ArithExpr t1, ArithExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BoolExpr(this, Native.Z3_mk_le(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Create an expression representing <c>t1 &gt; t2</c>
        /// </summary>
        public BoolExpr MkGt(ArithExpr t1, ArithExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BoolExpr(this, Native.Z3_mk_gt(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Create an expression representing <c>t1 &gt;= t2</c>
        /// </summary>
        public BoolExpr MkGe(ArithExpr t1, ArithExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BoolExpr(this, Native.Z3_mk_ge(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Coerce an integer to a real.
        /// </summary>
        /// <remarks>
        /// There is also a converse operation exposed. It follows the semantics prescribed by the SMT-LIB standard.
        ///
        /// You can take the floor of a real by creating an auxiliary integer Term <c>k</c> and
        /// and asserting <c>MakeInt2Real(k) &lt;= t1 &lt; MkInt2Real(k)+1</c>.
        /// The argument must be of integer sort.
        /// </remarks>
        public RealExpr MkInt2Real(IntExpr t)
        {
            Debug.Assert(t != null);

            CheckContextMatch(t);
            return new RealExpr(this, Native.Z3_mk_int2real(nCtx, t.NativeObject));
        }

        /// <summary>
        /// Coerce a real to an integer.
        /// </summary>
        /// <remarks>
        /// The semantics of this function follows the SMT-LIB standard for the function to_int.
        /// The argument must be of real sort.
        /// </remarks>
        public IntExpr MkReal2Int(RealExpr t)
        {
            Debug.Assert(t != null);

            CheckContextMatch(t);
            return new IntExpr(this, Native.Z3_mk_real2int(nCtx, t.NativeObject));
        }

        /// <summary>
        /// Creates an expression that checks whether a real number is an integer.
        /// </summary>
        public BoolExpr MkIsInteger(RealExpr t)
        {
            Debug.Assert(t != null);

            CheckContextMatch(t);
            return new BoolExpr(this, Native.Z3_mk_is_int(nCtx, t.NativeObject));
        }
        #endregion

        #region Bit-vectors
        /// <summary>
        /// Bitwise negation.
        /// </summary>
        /// <remarks>The argument must have a bit-vector sort.</remarks>
        public BitVecExpr MkBVNot(BitVecExpr t)
        {
            Debug.Assert(t != null);

            CheckContextMatch(t);
            return new BitVecExpr(this, Native.Z3_mk_bvnot(nCtx, t.NativeObject));
        }

        /// <summary>
        /// Take conjunction of bits in a vector, return vector of length 1.
        /// </summary>
        /// <remarks>The argument must have a bit-vector sort.</remarks>
        public BitVecExpr MkBVRedAND(BitVecExpr t)
        {
            Debug.Assert(t != null);

            CheckContextMatch(t);
            return new BitVecExpr(this, Native.Z3_mk_bvredand(nCtx, t.NativeObject));
        }

        /// <summary>
        /// Take disjunction of bits in a vector, return vector of length 1.
        /// </summary>
        /// <remarks>The argument must have a bit-vector sort.</remarks>
        public BitVecExpr MkBVRedOR(BitVecExpr t)
        {
            Debug.Assert(t != null);

            CheckContextMatch(t);
            return new BitVecExpr(this, Native.Z3_mk_bvredor(nCtx, t.NativeObject));
        }

        /// <summary>
        /// Bitwise conjunction.
        /// </summary>
        /// <remarks>The arguments must have a bit-vector sort.</remarks>
        public BitVecExpr MkBVAND(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BitVecExpr(this, Native.Z3_mk_bvand(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Bitwise disjunction.
        /// </summary>
        /// <remarks>The arguments must have a bit-vector sort.</remarks>
        public BitVecExpr MkBVOR(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BitVecExpr(this, Native.Z3_mk_bvor(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Bitwise XOR.
        /// </summary>
        /// <remarks>The arguments must have a bit-vector sort.</remarks>
        public BitVecExpr MkBVXOR(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BitVecExpr(this, Native.Z3_mk_bvxor(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Bitwise NAND.
        /// </summary>
        /// <remarks>The arguments must have a bit-vector sort.</remarks>
        public BitVecExpr MkBVNAND(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BitVecExpr(this, Native.Z3_mk_bvnand(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Bitwise NOR.
        /// </summary>
        /// <remarks>The arguments must have a bit-vector sort.</remarks>
        public BitVecExpr MkBVNOR(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BitVecExpr(this, Native.Z3_mk_bvnor(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Bitwise XNOR.
        /// </summary>
        /// <remarks>The arguments must have a bit-vector sort.</remarks>
        public BitVecExpr MkBVXNOR(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BitVecExpr(this, Native.Z3_mk_bvxnor(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Standard two's complement unary minus.
        /// </summary>
        /// <remarks>The arguments must have a bit-vector sort.</remarks>
        public BitVecExpr MkBVNeg(BitVecExpr t)
        {
            Debug.Assert(t != null);

            CheckContextMatch(t);
            return new BitVecExpr(this, Native.Z3_mk_bvneg(nCtx, t.NativeObject));
        }

        /// <summary>
        /// Two's complement addition.
        /// </summary>
        /// <remarks>The arguments must have the same bit-vector sort.</remarks>
        public BitVecExpr MkBVAdd(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BitVecExpr(this, Native.Z3_mk_bvadd(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Two's complement subtraction.
        /// </summary>
        /// <remarks>The arguments must have the same bit-vector sort.</remarks>
        public BitVecExpr MkBVSub(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BitVecExpr(this, Native.Z3_mk_bvsub(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Two's complement multiplication.
        /// </summary>
        /// <remarks>The arguments must have the same bit-vector sort.</remarks>
        public BitVecExpr MkBVMul(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BitVecExpr(this, Native.Z3_mk_bvmul(nCtx, t1.NativeObject, t2.NativeObject));
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
        public BitVecExpr MkBVUDiv(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BitVecExpr(this, Native.Z3_mk_bvudiv(nCtx, t1.NativeObject, t2.NativeObject));
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
        public BitVecExpr MkBVSDiv(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BitVecExpr(this, Native.Z3_mk_bvsdiv(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Unsigned remainder.
        /// </summary>
        /// <remarks>
        /// It is defined as <c>t1 - (t1 /u t2) * t2</c>, where <c>/u</c> represents unsigned division.
        /// If <c>t2</c> is zero, then the result is undefined.
        /// The arguments must have the same bit-vector sort.
        /// </remarks>
        public BitVecExpr MkBVURem(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BitVecExpr(this, Native.Z3_mk_bvurem(nCtx, t1.NativeObject, t2.NativeObject));
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
        public BitVecExpr MkBVSRem(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BitVecExpr(this, Native.Z3_mk_bvsrem(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Two's complement signed remainder (sign follows divisor).
        /// </summary>
        /// <remarks>
        /// If <c>t2</c> is zero, then the result is undefined.
        /// The arguments must have the same bit-vector sort.
        /// </remarks>
        public BitVecExpr MkBVSMod(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BitVecExpr(this, Native.Z3_mk_bvsmod(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Unsigned less-than
        /// </summary>
        /// <remarks>
        /// The arguments must have the same bit-vector sort.
        /// </remarks>
        public BoolExpr MkBVULT(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BoolExpr(this, Native.Z3_mk_bvult(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Two's complement signed less-than
        /// </summary>
        /// <remarks>
        /// The arguments must have the same bit-vector sort.
        /// </remarks>
        public BoolExpr MkBVSLT(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BoolExpr(this, Native.Z3_mk_bvslt(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Unsigned less-than or equal to.
        /// </summary>
        /// <remarks>
        /// The arguments must have the same bit-vector sort.
        /// </remarks>
        public BoolExpr MkBVULE(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BoolExpr(this, Native.Z3_mk_bvule(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Two's complement signed less-than or equal to.
        /// </summary>
        /// <remarks>
        /// The arguments must have the same bit-vector sort.
        /// </remarks>
        public BoolExpr MkBVSLE(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BoolExpr(this, Native.Z3_mk_bvsle(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Unsigned greater than or equal to.
        /// </summary>
        /// <remarks>
        /// The arguments must have the same bit-vector sort.
        /// </remarks>
        public BoolExpr MkBVUGE(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BoolExpr(this, Native.Z3_mk_bvuge(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        ///  Two's complement signed greater than or equal to.
        /// </summary>
        /// <remarks>
        /// The arguments must have the same bit-vector sort.
        /// </remarks>
        public BoolExpr MkBVSGE(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BoolExpr(this, Native.Z3_mk_bvsge(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Unsigned greater-than.
        /// </summary>
        /// <remarks>
        /// The arguments must have the same bit-vector sort.
        /// </remarks>
        public BoolExpr MkBVUGT(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BoolExpr(this, Native.Z3_mk_bvugt(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Two's complement signed greater-than.
        /// </summary>
        /// <remarks>
        /// The arguments must have the same bit-vector sort.
        /// </remarks>
        public BoolExpr MkBVSGT(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BoolExpr(this, Native.Z3_mk_bvsgt(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Bit-vector concatenation.
        /// </summary>
        /// <remarks>
        /// The arguments must have a bit-vector sort.
        /// </remarks>
        /// <returns>
        /// The result is a bit-vector of size <c>n1+n2</c>, where <c>n1</c> (<c>n2</c>)
        /// is the size of <c>t1</c> (<c>t2</c>).
        /// </returns>
        public BitVecExpr MkConcat(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BitVecExpr(this, Native.Z3_mk_concat(nCtx, t1.NativeObject, t2.NativeObject));
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
        public BitVecExpr MkExtract(uint high, uint low, BitVecExpr t)
        {
            Debug.Assert(t != null);

            CheckContextMatch(t);
            return new BitVecExpr(this, Native.Z3_mk_extract(nCtx, high, low, t.NativeObject));
        }

        /// <summary>
        /// Bit-vector sign extension.
        /// </summary>
        /// <remarks>
        /// Sign-extends the given bit-vector to the (signed) equivalent bitvector of
        /// size <c>m+i</c>, where \c m is the size of the given bit-vector.
        /// The argument <paramref name="t"/> must have a bit-vector sort.
        /// </remarks>
        public BitVecExpr MkSignExt(uint i, BitVecExpr t)
        {
            Debug.Assert(t != null);

            CheckContextMatch(t);
            return new BitVecExpr(this, Native.Z3_mk_sign_ext(nCtx, i, t.NativeObject));
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
        public BitVecExpr MkZeroExt(uint i, BitVecExpr t)
        {
            Debug.Assert(t != null);

            CheckContextMatch(t);
            return new BitVecExpr(this, Native.Z3_mk_zero_ext(nCtx, i, t.NativeObject));
        }

        /// <summary>
        /// Bit-vector repetition.
        /// </summary>
        /// <remarks>
        /// The argument <paramref name="t"/> must have a bit-vector sort.
        /// </remarks>
        public BitVecExpr MkRepeat(uint i, BitVecExpr t)
        {
            Debug.Assert(t != null);

            CheckContextMatch(t);
            return new BitVecExpr(this, Native.Z3_mk_repeat(nCtx, i, t.NativeObject));
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
        public BitVecExpr MkBVSHL(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BitVecExpr(this, Native.Z3_mk_bvshl(nCtx, t1.NativeObject, t2.NativeObject));
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
        public BitVecExpr MkBVLSHR(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BitVecExpr(this, Native.Z3_mk_bvlshr(nCtx, t1.NativeObject, t2.NativeObject));
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
        public BitVecExpr MkBVASHR(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BitVecExpr(this, Native.Z3_mk_bvashr(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Rotate Left.
        /// </summary>
        /// <remarks>
        /// Rotate bits of \c t to the left \c i times.
        /// The argument <paramref name="t"/> must have a bit-vector sort.
        /// </remarks>
        public BitVecExpr MkBVRotateLeft(uint i, BitVecExpr t)
        {
            Debug.Assert(t != null);

            CheckContextMatch(t);
            return new BitVecExpr(this, Native.Z3_mk_rotate_left(nCtx, i, t.NativeObject));
        }

        /// <summary>
        /// Rotate Right.
        /// </summary>
        /// <remarks>
        /// Rotate bits of \c t to the right \c i times.
        /// The argument <paramref name="t"/> must have a bit-vector sort.
        /// </remarks>
        public BitVecExpr MkBVRotateRight(uint i, BitVecExpr t)
        {
            Debug.Assert(t != null);

            CheckContextMatch(t);
            return new BitVecExpr(this, Native.Z3_mk_rotate_right(nCtx, i, t.NativeObject));
        }

        /// <summary>
        /// Rotate Left.
        /// </summary>
        /// <remarks>
        /// Rotate bits of <paramref name="t1"/> to the left <paramref name="t2"/> times.
        /// The arguments must have the same bit-vector sort.
        /// </remarks>
        public BitVecExpr MkBVRotateLeft(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BitVecExpr(this, Native.Z3_mk_ext_rotate_left(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Rotate Right.
        /// </summary>
        /// <remarks>
        /// Rotate bits of <paramref name="t1"/> to the right<paramref name="t2"/> times.
        /// The arguments must have the same bit-vector sort.
        /// </remarks>
        public BitVecExpr MkBVRotateRight(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BitVecExpr(this, Native.Z3_mk_ext_rotate_right(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Create an <paramref name="n"/> bit bit-vector from the integer argument <paramref name="t"/>.
        /// </summary>
        /// <remarks>
        /// NB. This function is essentially treated as uninterpreted.
        /// So you cannot expect Z3 to precisely reflect the semantics of this function
        /// when solving constraints with this function.
        ///
        /// The argument must be of integer sort.
        /// </remarks>
        public BitVecExpr MkInt2BV(uint n, IntExpr t)
        {
            Debug.Assert(t != null);

            CheckContextMatch(t);
            return new BitVecExpr(this, Native.Z3_mk_int2bv(nCtx, n, t.NativeObject));
        }

        /// <summary>
        /// Create an integer from the bit-vector argument <paramref name="t"/>.
        /// </summary>
        /// <remarks>
        /// If \c is_signed is false, then the bit-vector \c t1 is treated as unsigned.
        /// So the result is non-negative and in the range <c>[0..2^N-1]</c>, where
        /// N are the number of bits in <paramref name="t"/>.
        /// If \c is_signed is true, \c t1 is treated as a signed bit-vector.
        ///
        /// NB. This function is essentially treated as uninterpreted.
        /// So you cannot expect Z3 to precisely reflect the semantics of this function
        /// when solving constraints with this function.
        ///
        /// The argument must be of bit-vector sort.
        /// </remarks>
        public IntExpr MkBV2Int(BitVecExpr t, bool signed)
        {
            Debug.Assert(t != null);

            CheckContextMatch(t);
            return new IntExpr(this, Native.Z3_mk_bv2int(nCtx, t.NativeObject, (byte)(signed ? 1 : 0)));
        }

        /// <summary>
        /// Create a predicate that checks that the bit-wise addition does not overflow.
        /// </summary>
        /// <remarks>
        /// The arguments must be of bit-vector sort.
        /// </remarks>
        public BoolExpr MkBVAddNoOverflow(BitVecExpr t1, BitVecExpr t2, bool isSigned)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BoolExpr(this, Native.Z3_mk_bvadd_no_overflow(nCtx, t1.NativeObject, t2.NativeObject, (byte)(isSigned ? 1 : 0)));
        }

        /// <summary>
        /// Create a predicate that checks that the bit-wise addition does not underflow.
        /// </summary>
        /// <remarks>
        /// The arguments must be of bit-vector sort.
        /// </remarks>
        public BoolExpr MkBVAddNoUnderflow(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BoolExpr(this, Native.Z3_mk_bvadd_no_underflow(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Create a predicate that checks that the bit-wise subtraction does not overflow.
        /// </summary>
        /// <remarks>
        /// The arguments must be of bit-vector sort.
        /// </remarks>
        public BoolExpr MkBVSubNoOverflow(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BoolExpr(this, Native.Z3_mk_bvsub_no_overflow(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Create a predicate that checks that the bit-wise subtraction does not underflow.
        /// </summary>
        /// <remarks>
        /// The arguments must be of bit-vector sort.
        /// </remarks>
        public BoolExpr MkBVSubNoUnderflow(BitVecExpr t1, BitVecExpr t2, bool isSigned)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BoolExpr(this, Native.Z3_mk_bvsub_no_underflow(nCtx, t1.NativeObject, t2.NativeObject, (byte)(isSigned ? 1 : 0)));
        }

        /// <summary>
        /// Create a predicate that checks that the bit-wise signed division does not overflow.
        /// </summary>
        /// <remarks>
        /// The arguments must be of bit-vector sort.
        /// </remarks>
        public BoolExpr MkBVSDivNoOverflow(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BoolExpr(this, Native.Z3_mk_bvsdiv_no_overflow(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Create a predicate that checks that the bit-wise negation does not overflow.
        /// </summary>
        /// <remarks>
        /// The arguments must be of bit-vector sort.
        /// </remarks>
        public BoolExpr MkBVNegNoOverflow(BitVecExpr t)
        {
            Debug.Assert(t != null);

            CheckContextMatch(t);
            return new BoolExpr(this, Native.Z3_mk_bvneg_no_overflow(nCtx, t.NativeObject));
        }

        /// <summary>
        /// Create a predicate that checks that the bit-wise multiplication does not overflow.
        /// </summary>
        /// <remarks>
        /// The arguments must be of bit-vector sort.
        /// </remarks>
        public BoolExpr MkBVMulNoOverflow(BitVecExpr t1, BitVecExpr t2, bool isSigned)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BoolExpr(this, Native.Z3_mk_bvmul_no_overflow(nCtx, t1.NativeObject, t2.NativeObject, (byte)(isSigned ? 1 : 0)));
        }

        /// <summary>
        /// Create a predicate that checks that the bit-wise multiplication does not underflow.
        /// </summary>
        /// <remarks>
        /// The arguments must be of bit-vector sort.
        /// </remarks>
        public BoolExpr MkBVMulNoUnderflow(BitVecExpr t1, BitVecExpr t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new BoolExpr(this, Native.Z3_mk_bvmul_no_underflow(nCtx, t1.NativeObject, t2.NativeObject));
        }
        #endregion

        #region Arrays
        /// <summary>
        /// Create an array constant.
        /// </summary>
        public ArrayExpr MkArrayConst(Symbol name, Sort domain, Sort range)
        {
            Debug.Assert(name != null);
            Debug.Assert(domain != null);
            Debug.Assert(range != null);

            return (ArrayExpr)MkConst(name, MkArraySort(domain, range));
        }

        /// <summary>
        /// Create an array constant.
        /// </summary>
        public ArrayExpr MkArrayConst(string name, Sort domain, Sort range)
        {
            Debug.Assert(domain != null);
            Debug.Assert(range != null);

            return (ArrayExpr)MkConst(MkSymbol(name), MkArraySort(domain, range));
        }


        /// <summary>
        /// Array read.
        /// </summary>
        /// <remarks>
        /// The argument <c>a</c> is the array and <c>i</c> is the index
        /// of the array that gets read.
        ///
        /// The node <c>a</c> must have an array sort <c>[domain -> range]</c>,
        /// and <c>i</c> must have the sort <c>domain</c>.
        /// The sort of the result is <c>range</c>.
        /// <seealso cref="MkArraySort(Sort, Sort)"/>
        /// <seealso cref="MkStore(ArrayExpr, Expr, Expr)"/>
        /// </remarks>
        public Expr MkSelect(ArrayExpr a, Expr i)
        {
            Debug.Assert(a != null);
            Debug.Assert(i != null);

            CheckContextMatch(a);
            CheckContextMatch(i);
            return Expr.Create(this, Native.Z3_mk_select(nCtx, a.NativeObject, i.NativeObject));
        }

        /// <summary>
        /// Array read.
        /// </summary>
        /// <remarks>
        /// The argument <c>a</c> is the array and <c>args</c> are the indices
        /// of the array that gets read.
        ///
        /// The node <c>a</c> must have an array sort <c>[domain1,..,domaink -> range]</c>,
        /// and <c>args</c> must have the sort <c>domain1,..,domaink</c>.
        /// The sort of the result is <c>range</c>.
        /// <seealso cref="MkArraySort(Sort, Sort)"/>
        /// <seealso cref="MkStore(ArrayExpr, Expr, Expr)"/>
        /// </remarks>
        public Expr MkSelect(ArrayExpr a, params Expr[] args)
        {
            Debug.Assert(a != null);
            Debug.Assert(args != null && args.All(n => n != null));

            CheckContextMatch(a);
            CheckContextMatch<Expr>(args);
            return Expr.Create(this, Native.Z3_mk_select_n(nCtx, a.NativeObject, AST.ArrayLength(args), AST.ArrayToNative(args)));
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
        /// <seealso cref="MkArraySort(Sort, Sort)"/>
        /// <seealso cref="MkSelect(ArrayExpr, Expr)"/>
        /// <seealso cref="MkSelect(ArrayExpr, Expr[])"/>
        /// </remarks>
        public ArrayExpr MkStore(ArrayExpr a, Expr i, Expr v)
        {
            Debug.Assert(a != null);
            Debug.Assert(i != null);
            Debug.Assert(v != null);

            CheckContextMatch(a);
            CheckContextMatch(i);
            CheckContextMatch(v);
            return new ArrayExpr(this, Native.Z3_mk_store(nCtx, a.NativeObject, i.NativeObject, v.NativeObject));
        }

        /// <summary>
        /// Array update.
        /// </summary>
        /// <remarks>
        /// The node <c>a</c> must have an array sort <c>[domain1,..,domaink -> range]</c>,
        /// <c>args</c> must have sort <c>domain1,..,domaink</c>,
        /// <c>v</c> must have sort range. The sort of the result is <c>[domain -> range]</c>.
        /// The semantics of this function is given by the theory of arrays described in the SMT-LIB
        /// standard. See http://smtlib.org for more details.
        /// The result of this function is an array that is equal to <c>a</c>
        /// (with respect to <c>select</c>)
        /// on all indices except for <c>args</c>, where it maps to <c>v</c>
        /// (and the <c>select</c> of <c>a</c> with
        /// respect to <c>args</c> may be a different value).
        /// <seealso cref="MkArraySort(Sort, Sort)"/>
        /// <seealso cref="MkSelect(ArrayExpr, Expr)"/>
        /// <seealso cref="MkSelect(ArrayExpr, Expr[])"/>
        /// </remarks>
        public ArrayExpr MkStore(ArrayExpr a, Expr[] args, Expr v)
        {
            Debug.Assert(a != null);
            Debug.Assert(args != null);
            Debug.Assert(v != null);

            CheckContextMatch<Expr>(args);
            CheckContextMatch(a);
            CheckContextMatch(v);
            return new ArrayExpr(this, Native.Z3_mk_store_n(nCtx, a.NativeObject, AST.ArrayLength(args), AST.ArrayToNative(args), v.NativeObject));
        }

        /// <summary>
        /// Create a constant array.
        /// </summary>
        /// <remarks>
        /// The resulting term is an array, such that a <c>select</c>on an arbitrary index
        /// produces the value <c>v</c>.
        /// <seealso cref="MkArraySort(Sort, Sort)"/>
        /// <seealso cref="MkSelect(ArrayExpr, Expr)"/>
        /// </remarks>
        public ArrayExpr MkConstArray(Sort domain, Expr v)
        {
            Debug.Assert(domain != null);
            Debug.Assert(v != null);

            CheckContextMatch(domain);
            CheckContextMatch(v);
            return new ArrayExpr(this, Native.Z3_mk_const_array(nCtx, domain.NativeObject, v.NativeObject));
        }

        /// <summary>
        /// Maps f on the argument arrays.
        /// </summary>
        /// <remarks>
        /// Each element of <c>args</c> must be of an array sort <c>[domain_i -> range_i]</c>.
        /// The function declaration <c>f</c> must have type <c> range_1 .. range_n -> range</c>.
        /// <c>v</c> must have sort range. The sort of the result is <c>[domain_i -> range]</c>.
        /// <seealso cref="MkArraySort(Sort, Sort)"/>
        /// <seealso cref="MkSelect(ArrayExpr, Expr)"/>
        /// <seealso cref="MkStore(ArrayExpr, Expr, Expr)"/>
        /// </remarks>
        public ArrayExpr MkMap(FuncDecl f, params ArrayExpr[] args)
        {
            Debug.Assert(f != null);
            Debug.Assert(args == null || args.All(a => a != null));

            CheckContextMatch(f);
            CheckContextMatch<ArrayExpr>(args);
            return (ArrayExpr)Expr.Create(this, Native.Z3_mk_map(nCtx, f.NativeObject, AST.ArrayLength(args), AST.ArrayToNative(args)));
        }

        /// <summary>
        /// Access the array default value.
        /// </summary>
        /// <remarks>
        /// Produces the default range value, for arrays that can be represented as
        /// finite maps with a default range value.
        /// </remarks>
        public Expr MkTermArray(ArrayExpr array)
        {
            Debug.Assert(array != null);

            CheckContextMatch(array);
            return Expr.Create(this, Native.Z3_mk_array_default(nCtx, array.NativeObject));
        }

        /// <summary>
        /// Create Extentionality index. Two arrays are equal if and only if they are equal on the index returned by MkArrayExt.
        /// </summary>
        public Expr MkArrayExt(ArrayExpr arg1, ArrayExpr arg2)
        {
            Debug.Assert(arg1 != null);
            Debug.Assert(arg2 != null);

            CheckContextMatch(arg1);
            CheckContextMatch(arg2);
            return Expr.Create(this, Native.Z3_mk_array_ext(nCtx, arg1.NativeObject, arg2.NativeObject));
        }

        #endregion

        #region Sets
        /// <summary>
        /// Create a set type.
        /// </summary>
        public SetSort MkSetSort(Sort ty)
        {
            Debug.Assert(ty != null);

            CheckContextMatch(ty);
            return new SetSort(this, ty);
        }

        /// <summary>
        /// Create an empty set.
        /// </summary>
        public ArrayExpr MkEmptySet(Sort domain)
        {
            Debug.Assert(domain != null);

            CheckContextMatch(domain);
            return (ArrayExpr)Expr.Create(this, Native.Z3_mk_empty_set(nCtx, domain.NativeObject));
        }

        /// <summary>
        /// Create the full set.
        /// </summary>
        public ArrayExpr MkFullSet(Sort domain)
        {
            Debug.Assert(domain != null);

            CheckContextMatch(domain);
            return (ArrayExpr)Expr.Create(this, Native.Z3_mk_full_set(nCtx, domain.NativeObject));
        }

        /// <summary>
        /// Add an element to the set.
        /// </summary>
        public ArrayExpr MkSetAdd(ArrayExpr set, Expr element)
        {
            Debug.Assert(set != null);
            Debug.Assert(element != null);

            CheckContextMatch(set);
            CheckContextMatch(element);
            return (ArrayExpr)Expr.Create(this, Native.Z3_mk_set_add(nCtx, set.NativeObject, element.NativeObject));
        }


        /// <summary>
        /// Remove an element from a set.
        /// </summary>
        public ArrayExpr MkSetDel(ArrayExpr set, Expr element)
        {
            Debug.Assert(set != null);
            Debug.Assert(element != null);

            CheckContextMatch(set);
            CheckContextMatch(element);
            return (ArrayExpr)Expr.Create(this, Native.Z3_mk_set_del(nCtx, set.NativeObject, element.NativeObject));
        }

        /// <summary>
        /// Take the union of a list of sets.
        /// </summary>
        public ArrayExpr MkSetUnion(params ArrayExpr[] args)
        {
            Debug.Assert(args != null);
            Debug.Assert(args.All(a => a != null));

            CheckContextMatch<ArrayExpr>(args);
            return (ArrayExpr)Expr.Create(this, Native.Z3_mk_set_union(nCtx, (uint)args.Length, AST.ArrayToNative(args)));
        }

        /// <summary>
        /// Take the intersection of a list of sets.
        /// </summary>
        public ArrayExpr MkSetIntersection(params ArrayExpr[] args)
        {
            Debug.Assert(args != null);
            Debug.Assert(args.All(a => a != null));

            CheckContextMatch<ArrayExpr>(args);
            return (ArrayExpr)Expr.Create(this, Native.Z3_mk_set_intersect(nCtx, (uint)args.Length, AST.ArrayToNative(args)));
        }

        /// <summary>
        /// Take the difference between two sets.
        /// </summary>
        public ArrayExpr MkSetDifference(ArrayExpr arg1, ArrayExpr arg2)
        {
            Debug.Assert(arg1 != null);
            Debug.Assert(arg2 != null);

            CheckContextMatch(arg1);
            CheckContextMatch(arg2);
            return (ArrayExpr)Expr.Create(this, Native.Z3_mk_set_difference(nCtx, arg1.NativeObject, arg2.NativeObject));
        }

        /// <summary>
        /// Take the complement of a set.
        /// </summary>
        public ArrayExpr MkSetComplement(ArrayExpr arg)
        {
            Debug.Assert(arg != null);

            CheckContextMatch(arg);
            return (ArrayExpr)Expr.Create(this, Native.Z3_mk_set_complement(nCtx, arg.NativeObject));
        }

        /// <summary>
        /// Check for set membership.
        /// </summary>
        public BoolExpr MkSetMembership(Expr elem, ArrayExpr set)
        {
            Debug.Assert(elem != null);
            Debug.Assert(set != null);

            CheckContextMatch(elem);
            CheckContextMatch(set);
            return (BoolExpr) Expr.Create(this, Native.Z3_mk_set_member(nCtx, elem.NativeObject, set.NativeObject));
        }

        /// <summary>
        /// Check for subsetness of sets.
        /// </summary>
        public BoolExpr MkSetSubset(ArrayExpr arg1, ArrayExpr arg2)
        {
            Debug.Assert(arg1 != null);
            Debug.Assert(arg2 != null);

            CheckContextMatch(arg1);
            CheckContextMatch(arg2);
            return (BoolExpr) Expr.Create(this, Native.Z3_mk_set_subset(nCtx, arg1.NativeObject, arg2.NativeObject));
        }

        #endregion

        #region Sequence, string and regular expressions

        /// <summary>
        /// Create the empty sequence.
        /// </summary>
        public SeqExpr MkEmptySeq(Sort s) 
        {
            Debug.Assert(s != null);
            return new SeqExpr(this, Native.Z3_mk_seq_empty(nCtx, s.NativeObject));
        }

        /// <summary>
        /// Create the singleton sequence.
        /// </summary>
        public SeqExpr MkUnit(Expr elem) 
        {
            Debug.Assert(elem != null);
            return new SeqExpr(this, Native.Z3_mk_seq_unit(nCtx, elem.NativeObject));
        }

        /// <summary>
        /// Create a string constant.
        /// </summary>
        public SeqExpr MkString(string s) 
        {
            Debug.Assert(s != null);
            return new SeqExpr(this, Native.Z3_mk_string(nCtx, s));
        }

        /// <summary>
        /// Convert an integer expression to a string.
        /// </summary>
        public SeqExpr IntToString(Expr e) 
        {
            Debug.Assert(e != null);
            Debug.Assert(e is ArithExpr);
            return new SeqExpr(this, Native.Z3_mk_int_to_str(nCtx, e.NativeObject));
        }

        /// <summary>
        /// Convert a bit-vector expression, represented as an unsigned number, to a string.
        /// </summary>
        public SeqExpr UbvToString(Expr e)
        {
            Debug.Assert(e != null);
            Debug.Assert(e is ArithExpr);
            return new SeqExpr(this, Native.Z3_mk_ubv_to_str(nCtx, e.NativeObject));
        }

        /// <summary>
        /// Convert a bit-vector expression, represented as an signed number, to a string.
        /// </summary>
        public SeqExpr SbvToString(Expr e) {
            Debug.Assert(e != null);
            Debug.Assert(e is ArithExpr);
            return new SeqExpr(this, Native.Z3_mk_sbv_to_str(nCtx, e.NativeObject));
        }

        /// <summary>
        /// Convert an integer expression to a string.
        /// </summary>
        public IntExpr StringToInt(Expr e) 
        {
            Debug.Assert(e != null);
            Debug.Assert(e is SeqExpr);
            return new IntExpr(this, Native.Z3_mk_str_to_int(nCtx, e.NativeObject));
        }


        /// <summary>
        /// Concatenate sequences.
        /// </summary>
        public SeqExpr MkConcat(params SeqExpr[] t)
        {
            Debug.Assert(t != null);
            Debug.Assert(t.All(a => a != null));

            CheckContextMatch<SeqExpr>(t);
            return new SeqExpr(this, Native.Z3_mk_seq_concat(nCtx, (uint)t.Length, AST.ArrayToNative(t)));
        }


        /// <summary>
        /// Retrieve the length of a given sequence.
        /// </summary>
        public IntExpr MkLength(SeqExpr s)
        {
            Debug.Assert(s != null);
            return (IntExpr) Expr.Create(this, Native.Z3_mk_seq_length(nCtx, s.NativeObject));
        }

        /// <summary>
        /// Check for sequence prefix.
        /// </summary>
        public BoolExpr MkPrefixOf(SeqExpr s1, SeqExpr s2) 
        {
            Debug.Assert(s1 != null);
            Debug.Assert(s2 != null);
            CheckContextMatch(s1, s2);
            return new BoolExpr(this, Native.Z3_mk_seq_prefix(nCtx, s1.NativeObject, s2.NativeObject));
        }

        /// <summary>
        /// Check for sequence suffix.
        /// </summary>
        public BoolExpr MkSuffixOf(SeqExpr s1, SeqExpr s2) 
        {
            Debug.Assert(s1 != null);
            Debug.Assert(s2 != null);
            CheckContextMatch(s1, s2);
            return new BoolExpr(this, Native.Z3_mk_seq_suffix(nCtx, s1.NativeObject, s2.NativeObject));
        }

        /// <summary>
        /// Check for sequence containment of s2 in s1.
        /// </summary>
        public BoolExpr MkContains(SeqExpr s1, SeqExpr s2) 
        {
            Debug.Assert(s1 != null);
            Debug.Assert(s2 != null);
            CheckContextMatch(s1, s2);
            return new BoolExpr(this, Native.Z3_mk_seq_contains(nCtx, s1.NativeObject, s2.NativeObject));
        }

        /// <summary>
        /// Check if the string s1 is lexicographically strictly less than s2.
        /// </summary>
        public BoolExpr MkStringLt(SeqExpr s1, SeqExpr s2) 
        {
            Debug.Assert(s1 != null);
            Debug.Assert(s2 != null);
            CheckContextMatch(s1, s2);
            return new BoolExpr(this, Native.Z3_mk_str_lt(nCtx, s1.NativeObject, s2.NativeObject));
        }

        /// <summary>
        /// Check if the string s1 is lexicographically strictly less than s2.
        /// </summary>
        public BoolExpr MkStringLe(SeqExpr s1, SeqExpr s2) 
        {
            Debug.Assert(s1 != null);
            Debug.Assert(s2 != null);
            CheckContextMatch(s1, s2);
            return new BoolExpr(this, Native.Z3_mk_str_le(nCtx, s1.NativeObject, s2.NativeObject));
        }

        /// <summary>
        /// Retrieve sequence of length one at index.
        /// </summary>
        public SeqExpr MkAt(SeqExpr s, Expr index)
        {
            Debug.Assert(s != null);
            Debug.Assert(index != null);
            CheckContextMatch(s, index);
            return new SeqExpr(this, Native.Z3_mk_seq_at(nCtx, s.NativeObject, index.NativeObject));
        }

        /// <summary>
        /// Retrieve element at index.
        /// </summary>
        public Expr MkNth(SeqExpr s, Expr index)
        {
            Debug.Assert(s != null);
            Debug.Assert(index != null);
            CheckContextMatch(s, index);
            return Expr.Create(this, Native.Z3_mk_seq_nth(nCtx, s.NativeObject, index.NativeObject));
        }

        /// <summary>
        /// Extract subsequence.
        /// </summary>
        public SeqExpr MkExtract(SeqExpr s, IntExpr offset, IntExpr length)
        {
            Debug.Assert(s != null);
            Debug.Assert(offset != null);
            Debug.Assert(length != null);
            CheckContextMatch(s, offset, length);
            return new SeqExpr(this, Native.Z3_mk_seq_extract(nCtx, s.NativeObject, offset.NativeObject, length.NativeObject));
        }

        /// <summary>
        /// Extract index of sub-string starting at offset.
        /// </summary>
        public IntExpr MkIndexOf(SeqExpr s, SeqExpr substr, ArithExpr offset)
        {
            Debug.Assert(s != null);
            Debug.Assert(offset != null);
            Debug.Assert(substr != null);
            CheckContextMatch(s, substr, offset);
            return new IntExpr(this, Native.Z3_mk_seq_index(nCtx, s.NativeObject, substr.NativeObject, offset.NativeObject));
        }

        /// <summary>
        /// Replace the first occurrence of src by dst in s.
        /// </summary>
        public SeqExpr MkReplace(SeqExpr s, SeqExpr src, SeqExpr dst)
        {
            Debug.Assert(s != null);
            Debug.Assert(src != null);
            Debug.Assert(dst != null);
            CheckContextMatch(s, src, dst);
            return new SeqExpr(this, Native.Z3_mk_seq_replace(nCtx, s.NativeObject, src.NativeObject, dst.NativeObject));
        }

        /// <summary>
        /// Convert a regular expression that accepts sequence s.
        /// </summary>
        public ReExpr MkToRe(SeqExpr s) 
        {
            Debug.Assert(s != null);
            return new ReExpr(this, Native.Z3_mk_seq_to_re(nCtx, s.NativeObject));            
        }


        /// <summary>
        /// Check for regular expression membership.
        /// </summary>
        public BoolExpr MkInRe(SeqExpr s, ReExpr re)
        {
            Debug.Assert(s != null);
            Debug.Assert(re != null);
            CheckContextMatch(s, re);
            return new BoolExpr(this, Native.Z3_mk_seq_in_re(nCtx, s.NativeObject, re.NativeObject));            
        }

        /// <summary>
        /// Take the Kleene star of a regular expression.
        /// </summary>
        public ReExpr MkStar(ReExpr re)
        {
            Debug.Assert(re != null);
            return new ReExpr(this, Native.Z3_mk_re_star(nCtx, re.NativeObject));            
        }

        /// <summary>
        /// Take the bounded Kleene star of a regular expression.
        /// </summary>
        public ReExpr MkLoop(ReExpr re, uint lo, uint hi = 0)
        {
            Debug.Assert(re != null);
            return new ReExpr(this, Native.Z3_mk_re_loop(nCtx, re.NativeObject, lo, hi));            
        }

        /// <summary>
        /// Take the Kleene plus of a regular expression.
        /// </summary>
        public ReExpr MkPlus(ReExpr re)
        {
            Debug.Assert(re != null);
            return new ReExpr(this, Native.Z3_mk_re_plus(nCtx, re.NativeObject));            
        }

        /// <summary>
        /// Create the optional regular expression.
        /// </summary>
        public ReExpr MkOption(ReExpr re)
        {
            Debug.Assert(re != null);
            return new ReExpr(this, Native.Z3_mk_re_option(nCtx, re.NativeObject));            
        }

        /// <summary>
        /// Create the complement regular expression.
        /// </summary>
        public ReExpr MkComplement(ReExpr re)
        {
            Debug.Assert(re != null);
            return new ReExpr(this, Native.Z3_mk_re_complement(nCtx, re.NativeObject));            
        }

        /// <summary>
        /// Create the concatenation of regular languages.
        /// </summary>
        public ReExpr MkConcat(params ReExpr[] t)
        {
            Debug.Assert(t != null);
            Debug.Assert(t.All(a => a != null));

            CheckContextMatch<ReExpr>(t);
            return new ReExpr(this, Native.Z3_mk_re_concat(nCtx, (uint)t.Length, AST.ArrayToNative(t)));
        }

        /// <summary>
        /// Create the union of regular languages.
        /// </summary>
        public ReExpr MkUnion(params ReExpr[] t)
        {
            Debug.Assert(t != null);
            Debug.Assert(t.All(a => a != null));

            CheckContextMatch<ReExpr>(t);
            return new ReExpr(this, Native.Z3_mk_re_union(nCtx, (uint)t.Length, AST.ArrayToNative(t)));
        }

        /// <summary>
        /// Create the intersection of regular languages.
        /// </summary>
        public ReExpr MkIntersect(params ReExpr[] t)
        {
            Debug.Assert(t != null);
            Debug.Assert(t.All(a => a != null));

            CheckContextMatch<ReExpr>(t);
            return new ReExpr(this, Native.Z3_mk_re_intersect(nCtx, (uint)t.Length, AST.ArrayToNative(t)));
        }

        /// <summary>
        /// Create the empty regular expression.
        /// The sort s should be a regular expression.
        /// </summary>
        public ReExpr MkEmptyRe(Sort s) 
        {
            Debug.Assert(s != null);
            return new ReExpr(this, Native.Z3_mk_re_empty(nCtx, s.NativeObject));
        }

        /// <summary>
        /// Create the full regular expression.
        /// The sort s should be a regular expression.
        /// </summary>
        public ReExpr MkFullRe(Sort s) 
        {
            Debug.Assert(s != null);
            return new ReExpr(this, Native.Z3_mk_re_full(nCtx, s.NativeObject));
        }


        /// <summary>
        /// Create a range expression.
        /// </summary>
        public ReExpr MkRange(SeqExpr lo, SeqExpr hi) 
        {
            Debug.Assert(lo != null);
            Debug.Assert(hi != null);
            CheckContextMatch(lo, hi);
            return new ReExpr(this, Native.Z3_mk_re_range(nCtx, lo.NativeObject, hi.NativeObject));
        }
    
        #endregion

        #region Pseudo-Boolean constraints

        /// <summary>
        /// Create an at-most-k constraint.
        /// </summary>
        public BoolExpr MkAtMost(IEnumerable<BoolExpr> args, uint k)
        {
           Debug.Assert(args != null);
           CheckContextMatch<BoolExpr>(args);
           return new BoolExpr(this, Native.Z3_mk_atmost(nCtx, (uint) args.Count(),
                                                          AST.EnumToNative(args), k));
        }

        /// <summary>
        /// Create an at-least-k constraint.
        /// </summary>
        public BoolExpr MkAtLeast(IEnumerable<BoolExpr> args, uint k)
        {
           Debug.Assert(args != null);
           CheckContextMatch<BoolExpr>(args);
           return new BoolExpr(this, Native.Z3_mk_atleast(nCtx, (uint) args.Count(),
                                                          AST.EnumToNative(args), k));
        }

        /// <summary>
        /// Create a pseudo-Boolean less-or-equal constraint.
        /// </summary>
        public BoolExpr MkPBLe(int[] coeffs, BoolExpr[] args, int k)
        {
           Debug.Assert(args != null);
           Debug.Assert(coeffs != null);
           Debug.Assert(args.Length == coeffs.Length);
           CheckContextMatch<BoolExpr>(args);
           return new BoolExpr(this, Native.Z3_mk_pble(nCtx, (uint) args.Length,
                                                          AST.ArrayToNative(args),
                                                          coeffs, k));
        }

        /// <summary>
        /// Create a pseudo-Boolean greater-or-equal constraint.
        /// </summary>
        public BoolExpr MkPBGe(int[] coeffs, BoolExpr[] args, int k)
        {
           Debug.Assert(args != null);
           Debug.Assert(coeffs != null);
           Debug.Assert(args.Length == coeffs.Length);
           CheckContextMatch<BoolExpr>(args);
           return new BoolExpr(this, Native.Z3_mk_pbge(nCtx, (uint) args.Length,
                                                          AST.ArrayToNative(args),
                                                          coeffs, k));
        }
        /// <summary>
        /// Create a pseudo-Boolean equal constraint.
        /// </summary>
        public BoolExpr MkPBEq(int[] coeffs, BoolExpr[] args, int k)
        {
           Debug.Assert(args != null);
           Debug.Assert(coeffs != null);
           Debug.Assert(args.Length == coeffs.Length);
           CheckContextMatch<BoolExpr>(args);
           return new BoolExpr(this, Native.Z3_mk_pbeq(nCtx, (uint) args.Length,
                                                          AST.ArrayToNative(args),
                                                          coeffs, k));
        }
        #endregion

        #region Numerals

        #region General Numerals
        /// <summary>
        /// Create a Term of a given sort.
        /// </summary>
        /// <param name="v">A string representing the Term value in decimal notation. If the given sort is a real, then the Term can be a rational, that is, a string of the form <c>[num]* / [num]*</c>.</param>
        /// <param name="ty">The sort of the numeral. In the current implementation, the given sort can be an int, real, or bit-vectors of arbitrary size. </param>
        /// <returns>A Term with value <paramref name="v"/> and sort <paramref name="ty"/> </returns>
        public Expr MkNumeral(string v, Sort ty)
        {
            Debug.Assert(ty != null);

            CheckContextMatch(ty);
            return Expr.Create(this, Native.Z3_mk_numeral(nCtx, v, ty.NativeObject));
        }

        /// <summary>
        /// Create a Term of a given sort. This function can be used to create numerals that fit in a machine integer.
        /// It is slightly faster than <c>MakeNumeral</c> since it is not necessary to parse a string.
        /// </summary>
        /// <param name="v">Value of the numeral</param>
        /// <param name="ty">Sort of the numeral</param>
        /// <returns>A Term with value <paramref name="v"/> and type <paramref name="ty"/></returns>
        public Expr MkNumeral(int v, Sort ty)
        {
            Debug.Assert(ty != null);

            CheckContextMatch(ty);
            return Expr.Create(this, Native.Z3_mk_int(nCtx, v, ty.NativeObject));
        }

        /// <summary>
        /// Create a Term of a given sort. This function can be used to create numerals that fit in a machine integer.
        /// It is slightly faster than <c>MakeNumeral</c> since it is not necessary to parse a string.
        /// </summary>
        /// <param name="v">Value of the numeral</param>
        /// <param name="ty">Sort of the numeral</param>
        /// <returns>A Term with value <paramref name="v"/> and type <paramref name="ty"/></returns>
        public Expr MkNumeral(uint v, Sort ty)
        {
            Debug.Assert(ty != null);

            CheckContextMatch(ty);
            return Expr.Create(this, Native.Z3_mk_unsigned_int(nCtx, v, ty.NativeObject));
        }

        /// <summary>
        /// Create a Term of a given sort. This function can be used to create numerals that fit in a machine integer.
        /// It is slightly faster than <c>MakeNumeral</c> since it is not necessary to parse a string.
        /// </summary>
        /// <param name="v">Value of the numeral</param>
        /// <param name="ty">Sort of the numeral</param>
        /// <returns>A Term with value <paramref name="v"/> and type <paramref name="ty"/></returns>
        public Expr MkNumeral(long v, Sort ty)
        {
            Debug.Assert(ty != null);

            CheckContextMatch(ty);
            return Expr.Create(this, Native.Z3_mk_int64(nCtx, v, ty.NativeObject));
        }

        /// <summary>
        /// Create a Term of a given sort. This function can be used to create numerals that fit in a machine integer.
        /// It is slightly faster than <c>MakeNumeral</c> since it is not necessary to parse a string.
        /// </summary>
        /// <param name="v">Value of the numeral</param>
        /// <param name="ty">Sort of the numeral</param>
        /// <returns>A Term with value <paramref name="v"/> and type <paramref name="ty"/></returns>
        public Expr MkNumeral(ulong v, Sort ty)
        {
            Debug.Assert(ty != null);

            CheckContextMatch(ty);
            return Expr.Create(this, Native.Z3_mk_unsigned_int64(nCtx, v, ty.NativeObject));
        }
        #endregion

        #region Reals
        /// <summary>
        /// Create a real from a fraction.
        /// </summary>
        /// <param name="num">numerator of rational.</param>
        /// <param name="den">denominator of rational.</param>
        /// <returns>A Term with value <paramref name="num"/>/<paramref name="den"/> and sort Real</returns>
        /// <seealso cref="MkNumeral(string, Sort)"/>
        public RatNum MkReal(int num, int den)
        {
            if (den == 0)
                throw new Z3Exception("Denominator is zero");

            return new RatNum(this, Native.Z3_mk_real(nCtx, num, den));
        }

        /// <summary>
        /// Create a real numeral.
        /// </summary>
        /// <param name="v">A string representing the Term value in decimal notation.</param>
        /// <returns>A Term with value <paramref name="v"/> and sort Real</returns>
        public RatNum MkReal(string v)
        {

            return new RatNum(this, Native.Z3_mk_numeral(nCtx, v, RealSort.NativeObject));
        }

        /// <summary>
        /// Create a real numeral.
        /// </summary>
        /// <param name="v">value of the numeral.</param>
        /// <returns>A Term with value <paramref name="v"/> and sort Real</returns>
        public RatNum MkReal(int v)
        {

            return new RatNum(this, Native.Z3_mk_int(nCtx, v, RealSort.NativeObject));
        }

        /// <summary>
        /// Create a real numeral.
        /// </summary>
        /// <param name="v">value of the numeral.</param>
        /// <returns>A Term with value <paramref name="v"/> and sort Real</returns>
        public RatNum MkReal(uint v)
        {

            return new RatNum(this, Native.Z3_mk_unsigned_int(nCtx, v, RealSort.NativeObject));
        }

        /// <summary>
        /// Create a real numeral.
        /// </summary>
        /// <param name="v">value of the numeral.</param>
        /// <returns>A Term with value <paramref name="v"/> and sort Real</returns>
        public RatNum MkReal(long v)
        {

            return new RatNum(this, Native.Z3_mk_int64(nCtx, v, RealSort.NativeObject));
        }

        /// <summary>
        /// Create a real numeral.
        /// </summary>
        /// <param name="v">value of the numeral.</param>
        /// <returns>A Term with value <paramref name="v"/> and sort Real</returns>
        public RatNum MkReal(ulong v)
        {

            return new RatNum(this, Native.Z3_mk_unsigned_int64(nCtx, v, RealSort.NativeObject));
        }
        #endregion

        #region Integers
        /// <summary>
        /// Create an integer numeral.
        /// </summary>
        /// <param name="v">A string representing the Term value in decimal notation.</param>
        public IntNum MkInt(string v)
        {

            return new IntNum(this, Native.Z3_mk_numeral(nCtx, v, IntSort.NativeObject));
        }

        /// <summary>
        /// Create an integer numeral.
        /// </summary>
        /// <param name="v">value of the numeral.</param>
        /// <returns>A Term with value <paramref name="v"/> and sort Integer</returns>
        public IntNum MkInt(int v)
        {

            return new IntNum(this, Native.Z3_mk_int(nCtx, v, IntSort.NativeObject));
        }

        /// <summary>
        /// Create an integer numeral.
        /// </summary>
        /// <param name="v">value of the numeral.</param>
        /// <returns>A Term with value <paramref name="v"/> and sort Integer</returns>
        public IntNum MkInt(uint v)
        {

            return new IntNum(this, Native.Z3_mk_unsigned_int(nCtx, v, IntSort.NativeObject));
        }

        /// <summary>
        /// Create an integer numeral.
        /// </summary>
        /// <param name="v">value of the numeral.</param>
        /// <returns>A Term with value <paramref name="v"/> and sort Integer</returns>
        public IntNum MkInt(long v)
        {

            return new IntNum(this, Native.Z3_mk_int64(nCtx, v, IntSort.NativeObject));
        }

        /// <summary>
        /// Create an integer numeral.
        /// </summary>
        /// <param name="v">value of the numeral.</param>
        /// <returns>A Term with value <paramref name="v"/> and sort Integer</returns>
        public IntNum MkInt(ulong v)
        {

            return new IntNum(this, Native.Z3_mk_unsigned_int64(nCtx, v, IntSort.NativeObject));
        }
        #endregion

        #region Bit-vectors
        /// <summary>
        /// Create a bit-vector numeral.
        /// </summary>
        /// <param name="v">A string representing the value in decimal notation.</param>
        /// <param name="size">the size of the bit-vector</param>
        public BitVecNum MkBV(string v, uint size)
        {

            return (BitVecNum)MkNumeral(v, MkBitVecSort(size));
        }

        /// <summary>
        /// Create a bit-vector numeral.
        /// </summary>
        /// <param name="v">value of the numeral.</param>
        /// <param name="size">the size of the bit-vector</param>
        public BitVecNum MkBV(int v, uint size)
        {

            return (BitVecNum)MkNumeral(v, MkBitVecSort(size));
        }

        /// <summary>
        /// Create a bit-vector numeral.
        /// </summary>
        /// <param name="v">value of the numeral.</param>
        /// <param name="size">the size of the bit-vector</param>
        public BitVecNum MkBV(uint v, uint size)
        {

            return (BitVecNum)MkNumeral(v, MkBitVecSort(size));
        }

        /// <summary>
        /// Create a bit-vector numeral.
        /// </summary>
        /// <param name="v">value of the numeral.</param>
        /// <param name="size">the size of the bit-vector</param>
        public BitVecNum MkBV(long v, uint size)
        {

            return (BitVecNum)MkNumeral(v, MkBitVecSort(size));
        }

        /// <summary>
        /// Create a bit-vector numeral.
        /// </summary>
        /// <param name="v">value of the numeral.</param>
        /// <param name="size">the size of the bit-vector</param>
        public BitVecNum MkBV(ulong v, uint size)
        {

            return (BitVecNum)MkNumeral(v, MkBitVecSort(size));
        }

        /// <summary>
        /// Create a bit-vector numeral.
        /// </summary>
        /// <param name="bits">An array of bits representing the bit-vector. Least significant bit is at position 0.</param>
        public BitVecNum MkBV(bool[] bits)
        {
            byte[] _bits = new byte[bits.Length];
            for (int i = 0; i < bits.Length; ++i) _bits[i] = (byte)(bits[i] ? 1 : 0);
            return (BitVecNum)Expr.Create(this, Native.Z3_mk_bv_numeral(nCtx, (uint)bits.Length, _bits));
        }


        #endregion

        #endregion // Numerals

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
        public Quantifier MkForall(Sort[] sorts, Symbol[] names, Expr body, uint weight = 1, Pattern[] patterns = null, Expr[] noPatterns = null, Symbol quantifierID = null, Symbol skolemID = null)
        {
            Debug.Assert(sorts != null);
            Debug.Assert(names != null);
            Debug.Assert(body != null);
            Debug.Assert(sorts.Length == names.Length);
            Debug.Assert(sorts.All(s => s != null));
            Debug.Assert(names.All(n => n != null));
            Debug.Assert(patterns == null || patterns.All(p => p != null));
            Debug.Assert(noPatterns == null || noPatterns.All(np => np != null));


            return new Quantifier(this, true, sorts, names, body, weight, patterns, noPatterns, quantifierID, skolemID);
        }


        /// <summary>
        /// Create a universal Quantifier.
        /// </summary>
        /// <remarks>
        /// Creates a universal quantifier using a list of constants that will
        /// form the set of bound variables.
        /// <seealso cref="MkForall(Sort[], Symbol[], Expr, uint, Pattern[], Expr[], Symbol, Symbol)"/>
        /// </remarks>
        public Quantifier MkForall(Expr[] boundConstants, Expr body, uint weight = 1, Pattern[] patterns = null, Expr[] noPatterns = null, Symbol quantifierID = null, Symbol skolemID = null)
        {
            Debug.Assert(body != null);
            Debug.Assert(boundConstants == null || boundConstants.All(b => b != null));
            Debug.Assert(patterns == null || patterns.All(p => p != null));
            Debug.Assert(noPatterns == null || noPatterns.All(np => np != null));


            return new Quantifier(this, true, boundConstants, body, weight, patterns, noPatterns, quantifierID, skolemID);
        }

        /// <summary>
        /// Create an existential Quantifier.
        /// </summary>
        /// <remarks>
        /// Creates an existential quantifier using de-Bruijn indexed variables.
        /// (<see cref="MkForall(Sort[], Symbol[], Expr, uint, Pattern[], Expr[], Symbol, Symbol)"/>).
        /// </remarks>
        public Quantifier MkExists(Sort[] sorts, Symbol[] names, Expr body, uint weight = 1, Pattern[] patterns = null, Expr[] noPatterns = null, Symbol quantifierID = null, Symbol skolemID = null)
        {
            Debug.Assert(sorts != null);
            Debug.Assert(names != null);
            Debug.Assert(body != null);
            Debug.Assert(sorts.Length == names.Length);
            Debug.Assert(sorts.All(s => s != null));
            Debug.Assert(names.All(n => n != null));
            Debug.Assert(patterns == null || patterns.All(p => p != null));
            Debug.Assert(noPatterns == null || noPatterns.All(np => np != null));

            return new Quantifier(this, false, sorts, names, body, weight, patterns, noPatterns, quantifierID, skolemID);
        }

        /// <summary>
        /// Create an existential Quantifier.
        /// </summary>
        /// <remarks>
        /// Creates an existential quantifier using a list of constants that will
        /// form the set of bound variables.
        /// <seealso cref="MkForall(Sort[], Symbol[], Expr, uint, Pattern[], Expr[], Symbol, Symbol)"/>
        /// </remarks>
        public Quantifier MkExists(Expr[] boundConstants, Expr body, uint weight = 1, Pattern[] patterns = null, Expr[] noPatterns = null, Symbol quantifierID = null, Symbol skolemID = null)
        {
            Debug.Assert(body != null);
            Debug.Assert(boundConstants == null || boundConstants.All(n => n != null));
            Debug.Assert(patterns == null || patterns.All(p => p != null));
            Debug.Assert(noPatterns == null || noPatterns.All(np => np != null));

            return new Quantifier(this, false, boundConstants, body, weight, patterns, noPatterns, quantifierID, skolemID);
        }


        /// <summary>
        /// Create a Quantifier.
        /// </summary>
        /// <see cref="MkForall(Sort[], Symbol[], Expr, uint, Pattern[], Expr[], Symbol, Symbol)"/>
        public Quantifier MkQuantifier(bool universal, Sort[] sorts, Symbol[] names, Expr body, uint weight = 1, Pattern[] patterns = null, Expr[] noPatterns = null, Symbol quantifierID = null, Symbol skolemID = null)
        {
            Debug.Assert(body != null);
            Debug.Assert(names != null);
            Debug.Assert(sorts != null);
            Debug.Assert(sorts.Length == names.Length);
            Debug.Assert(sorts.All(s => s != null));
            Debug.Assert(names.All(n => n != null));
            Debug.Assert(patterns == null || patterns.All(p => p != null));
            Debug.Assert(noPatterns == null || noPatterns.All(np => np != null));


            if (universal)
                return MkForall(sorts, names, body, weight, patterns, noPatterns, quantifierID, skolemID);
            else
                return MkExists(sorts, names, body, weight, patterns, noPatterns, quantifierID, skolemID);
        }


        /// <summary>
        /// Create a Quantifier.
        /// </summary>
        /// <see cref="MkForall(Sort[], Symbol[], Expr, uint, Pattern[], Expr[], Symbol, Symbol)"/>
        public Quantifier MkQuantifier(bool universal, Expr[] boundConstants, Expr body, uint weight = 1, Pattern[] patterns = null, Expr[] noPatterns = null, Symbol quantifierID = null, Symbol skolemID = null)
        {
            Debug.Assert(body != null);
            Debug.Assert(boundConstants == null || boundConstants.All(n => n != null));
            Debug.Assert(patterns == null || patterns.All(p => p != null));
            Debug.Assert(noPatterns == null || noPatterns.All(np => np != null));


            if (universal)
                return MkForall(boundConstants, body, weight, patterns, noPatterns, quantifierID, skolemID);
            else
                return MkExists(boundConstants, body, weight, patterns, noPatterns, quantifierID, skolemID);
        }

        /// <summary>
        /// Create a lambda expression.
        /// </summary>
        /// <remarks>
        /// Creates a lambda expression.
        /// <paramref name="sorts"/> is an array
        /// with the sorts of the bound variables, <paramref name="names"/> is an array with the
        /// 'names' of the bound variables, and <paramref name="body"/> is the body of the
        /// lambda. 
        /// Note that the bound variables are de-Bruijn indices created using <see cref="MkBound"/>.
        /// Z3 applies the convention that the last element in <paramref name="names"/> and
        /// <paramref name="sorts"/> refers to the variable with index 0, the second to last element
        /// of <paramref name="names"/> and <paramref name="sorts"/> refers to the variable
        /// with index 1, etc.
        /// </remarks>
        /// <param name="sorts">the sorts of the bound variables.</param>
        /// <param name="names">names of the bound variables</param>
        /// <param name="body">the body of the quantifier.</param>
        public Lambda MkLambda(Sort[] sorts, Symbol[] names, Expr body)
        {
            Debug.Assert(sorts != null);
            Debug.Assert(names != null);
            Debug.Assert(body != null);
            Debug.Assert(sorts.Length == names.Length);
            Debug.Assert(sorts.All(s => s != null));
            Debug.Assert(names.All(n => n != null));
            return new Lambda(this, sorts, names, body);
        }

        /// <summary>
        /// Create a lambda expression.
        /// </summary>
        /// <remarks>
        /// Creates a lambda expression using a list of constants that will
        /// form the set of bound variables.
        /// <seealso cref="MkLambda(Sort[], Symbol[], Expr)"/>
        /// </remarks>
        public Lambda MkLambda(Expr[] boundConstants, Expr body)
        {
            Debug.Assert(body != null);
            Debug.Assert(boundConstants != null && boundConstants.All(b => b != null));
            return new Lambda(this, boundConstants, body);
        }


        #endregion

        #endregion // Expr

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

        #region SMT Files & Strings

        /// <summary>
        /// Parse the given string using the SMT-LIB2 parser.
        /// </summary>
        /// <returns>A conjunction of assertions in the scope (up to push/pop) at the end of the string.</returns>
        public BoolExpr[] ParseSMTLIB2String(string str, Symbol[] sortNames = null, Sort[] sorts = null, Symbol[] declNames = null, FuncDecl[] decls = null)
        {

            uint csn = Symbol.ArrayLength(sortNames);
            uint cs = Sort.ArrayLength(sorts);
            uint cdn = Symbol.ArrayLength(declNames);
            uint cd = AST.ArrayLength(decls);
            if (csn != cs || cdn != cd)
                throw new Z3Exception("Argument size mismatch");
            ASTVector assertions = new ASTVector(this, Native.Z3_parse_smtlib2_string(nCtx, str,
                AST.ArrayLength(sorts), Symbol.ArrayToNative(sortNames), AST.ArrayToNative(sorts),
                AST.ArrayLength(decls), Symbol.ArrayToNative(declNames), AST.ArrayToNative(decls)));
            return assertions.ToBoolExprArray();
        }

        /// <summary>
        /// Parse the given file using the SMT-LIB2 parser.
        /// </summary>
        /// <seealso cref="ParseSMTLIB2String"/>
        public BoolExpr[] ParseSMTLIB2File(string fileName, Symbol[] sortNames = null, Sort[] sorts = null, Symbol[] declNames = null, FuncDecl[] decls = null)
        {

            uint csn = Symbol.ArrayLength(sortNames);
            uint cs = Sort.ArrayLength(sorts);
            uint cdn = Symbol.ArrayLength(declNames);
            uint cd = AST.ArrayLength(decls);
            if (csn != cs || cdn != cd)
                throw new Z3Exception("Argument size mismatch");
            ASTVector assertions = new ASTVector(this, Native.Z3_parse_smtlib2_file(nCtx, fileName,
                AST.ArrayLength(sorts), Symbol.ArrayToNative(sortNames), AST.ArrayToNative(sorts),
                AST.ArrayLength(decls), Symbol.ArrayToNative(declNames), AST.ArrayToNative(decls)));
            return assertions.ToBoolExprArray();
        }
        #endregion

        #region Goals
        /// <summary>
        /// Creates a new Goal.
        /// </summary>
        /// <remarks>
        /// Note that the Context must have been created with proof generation support if
        /// <paramref name="proofs"/> is set to true here.
        /// </remarks>
        /// <param name="models">Indicates whether model generation should be enabled.</param>
        /// <param name="unsatCores">Indicates whether unsat core generation should be enabled.</param>
        /// <param name="proofs">Indicates whether proof generation should be enabled.</param>
        public Goal MkGoal(bool models = true, bool unsatCores = false, bool proofs = false)
        {

            return new Goal(this, models, unsatCores, proofs);
        }
        #endregion

        #region ParameterSets
        /// <summary>
        /// Creates a new ParameterSet.
        /// </summary>
        public Params MkParams()
        {

            return new Params(this);
        }
        #endregion

        #region Tactics
        /// <summary>
        /// The number of supported tactics.
        /// </summary>
        public uint NumTactics
        {
            get { return Native.Z3_get_num_tactics(nCtx); }
        }

        /// <summary>
        /// The names of all supported tactics.
        /// </summary>
        public string[] TacticNames
        {
            get
            {

                uint n = NumTactics;
                string[] res = new string[n];
                for (uint i = 0; i < n; i++)
                    res[i] = Native.Z3_get_tactic_name(nCtx, i);
                return res;
            }
        }

        /// <summary>
        /// Returns a string containing a description of the tactic with the given name.
        /// </summary>
        public string TacticDescription(string name)
        {

            return Native.Z3_tactic_get_descr(nCtx, name);
        }

        /// <summary>
        /// Creates a new Tactic.
        /// </summary>
        public Tactic MkTactic(string name)
        {

            return new Tactic(this, name);
        }

        /// <summary>
        /// Create a tactic that applies <paramref name="t1"/> to a Goal and
        /// then <paramref name="t2"/> to every subgoal produced by <paramref name="t1"/>.
        /// </summary>
        public Tactic AndThen(Tactic t1, Tactic t2, params Tactic[] ts)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);
            // Debug.Assert(ts == null || Contract.ForAll(0, ts.Length, j => ts[j] != null));


            CheckContextMatch(t1);
            CheckContextMatch(t2);
            CheckContextMatch<Tactic>(ts);

            IntPtr last = IntPtr.Zero;
            if (ts != null && ts.Length > 0)
            {
                last = ts[ts.Length - 1].NativeObject;
                for (int i = ts.Length - 2; i >= 0; i--)
                    last = Native.Z3_tactic_and_then(nCtx, ts[i].NativeObject, last);
            }
            if (last != IntPtr.Zero)
            {
                last = Native.Z3_tactic_and_then(nCtx, t2.NativeObject, last);
                return new Tactic(this, Native.Z3_tactic_and_then(nCtx, t1.NativeObject, last));
            }
            else
                return new Tactic(this, Native.Z3_tactic_and_then(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Create a tactic that applies <paramref name="t1"/> to a Goal and
        /// then <paramref name="t2"/> to every subgoal produced by <paramref name="t1"/>.
        /// </summary>
        /// <remarks>
        /// Shorthand for <c>AndThen</c>.
        /// </remarks>
        public Tactic Then(Tactic t1, Tactic t2, params Tactic[] ts)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);
            //  Debug.Assert(ts == null || Contract.ForAll(0, ts.Length, j => ts[j] != null));

            return AndThen(t1, t2, ts);
        }

        /// <summary>
        /// Create a tactic that first applies <paramref name="t1"/> to a Goal and
        /// if it fails then returns the result of <paramref name="t2"/> applied to the Goal.
        /// </summary>
        public Tactic OrElse(Tactic t1, Tactic t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new Tactic(this, Native.Z3_tactic_or_else(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Create a tactic that applies <paramref name="t"/> to a goal for <paramref name="ms"/> milliseconds.
        /// </summary>
        /// <remarks>
        /// If <paramref name="t"/> does not terminate within <paramref name="ms"/> milliseconds, then it fails.
        /// </remarks>
        public Tactic TryFor(Tactic t, uint ms)
        {
            Debug.Assert(t != null);

            CheckContextMatch(t);
            return new Tactic(this, Native.Z3_tactic_try_for(nCtx, t.NativeObject, ms));
        }

        /// <summary>
        /// Create a tactic that applies <paramref name="t"/> to a given goal if the probe
        /// <paramref name="p"/> evaluates to true.
        /// </summary>
        /// <remarks>
        /// If <paramref name="p"/> evaluates to false, then the new tactic behaves like the <c>skip</c> tactic.
        /// </remarks>
        public Tactic When(Probe p, Tactic t)
        {
            Debug.Assert(p != null);
            Debug.Assert(t != null);

            CheckContextMatch(t);
            CheckContextMatch(p);
            return new Tactic(this, Native.Z3_tactic_when(nCtx, p.NativeObject, t.NativeObject));
        }

        /// <summary>
        /// Create a tactic that applies <paramref name="t1"/> to a given goal if the probe
        /// <paramref name="p"/> evaluates to true and <paramref name="t2"/> otherwise.
        /// </summary>
        public Tactic Cond(Probe p, Tactic t1, Tactic t2)
        {
            Debug.Assert(p != null);
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(p);
            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new Tactic(this, Native.Z3_tactic_cond(nCtx, p.NativeObject, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Create a tactic that keeps applying <paramref name="t"/> until the goal is not
        /// modified anymore or the maximum number of iterations <paramref name="max"/> is reached.
        /// </summary>
        public Tactic Repeat(Tactic t, uint max = uint.MaxValue)
        {
            Debug.Assert(t != null);

            CheckContextMatch(t);
            return new Tactic(this, Native.Z3_tactic_repeat(nCtx, t.NativeObject, max));
        }

        /// <summary>
        /// Create a tactic that just returns the given goal.
        /// </summary>
        public Tactic Skip()
        {

            return new Tactic(this, Native.Z3_tactic_skip(nCtx));
        }

        /// <summary>
        /// Create a tactic always fails.
        /// </summary>
        public Tactic Fail()
        {

            return new Tactic(this, Native.Z3_tactic_fail(nCtx));
        }

        /// <summary>
        /// Create a tactic that fails if the probe <paramref name="p"/> evaluates to false.
        /// </summary>
        public Tactic FailIf(Probe p)
        {
            Debug.Assert(p != null);

            CheckContextMatch(p);
            return new Tactic(this, Native.Z3_tactic_fail_if(nCtx, p.NativeObject));
        }

        /// <summary>
        /// Create a tactic that fails if the goal is not trivially satisfiable (i.e., empty)
        /// or trivially unsatisfiable (i.e., contains `false').
        /// </summary>
        public Tactic FailIfNotDecided()
        {

            return new Tactic(this, Native.Z3_tactic_fail_if_not_decided(nCtx));
        }

        /// <summary>
        /// Create a tactic that applies <paramref name="t"/> using the given set of parameters <paramref name="p"/>.
        /// </summary>
        public Tactic UsingParams(Tactic t, Params p)
        {
            Debug.Assert(t != null);
            Debug.Assert(p != null);

            CheckContextMatch(t);
            CheckContextMatch(p);
            return new Tactic(this, Native.Z3_tactic_using_params(nCtx, t.NativeObject, p.NativeObject));
        }

        /// <summary>
        /// Create a tactic that applies <paramref name="t"/> using the given set of parameters <paramref name="p"/>.
        /// </summary>
        /// <remarks>Alias for <c>UsingParams</c></remarks>
        public Tactic With(Tactic t, Params p)
        {
            Debug.Assert(t != null);
            Debug.Assert(p != null);

            return UsingParams(t, p);
        }

        /// <summary>
        /// Create a tactic that applies the given tactics in parallel until one of them succeeds (i.e., the first that doesn't fail).
        /// </summary>
        public Tactic ParOr(params Tactic[] t)
        {
            Debug.Assert(t == null || t.All(tactic => tactic != null));

            CheckContextMatch<Tactic>(t);
            return new Tactic(this, Native.Z3_tactic_par_or(nCtx, Tactic.ArrayLength(t), Tactic.ArrayToNative(t)));
        }

        /// <summary>
        /// Create a tactic that applies <paramref name="t1"/> to a given goal and then <paramref name="t2"/>
        /// to every subgoal produced by <paramref name="t1"/>. The subgoals are processed in parallel.
        /// </summary>
        public Tactic ParAndThen(Tactic t1, Tactic t2)
        {
            Debug.Assert(t1 != null);
            Debug.Assert(t2 != null);

            CheckContextMatch(t1);
            CheckContextMatch(t2);
            return new Tactic(this, Native.Z3_tactic_par_and_then(nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Interrupt the execution of a Z3 procedure.
        /// </summary>
        /// <remarks>This procedure can be used to interrupt: solvers, simplifiers and tactics.</remarks>
        public void Interrupt()
        {
            Native.Z3_interrupt(nCtx);
        }
        #endregion

        #region Probes
        /// <summary>
        /// The number of supported Probes.
        /// </summary>
        public uint NumProbes
        {
            get { return Native.Z3_get_num_probes(nCtx); }
        }

        /// <summary>
        /// The names of all supported Probes.
        /// </summary>
        public string[] ProbeNames
        {
            get
            {

                uint n = NumProbes;
                string[] res = new string[n];
                for (uint i = 0; i < n; i++)
                    res[i] = Native.Z3_get_probe_name(nCtx, i);
                return res;
            }
        }

        /// <summary>
        /// Returns a string containing a description of the probe with the given name.
        /// </summary>
        public string ProbeDescription(string name)
        {

            return Native.Z3_probe_get_descr(nCtx, name);
        }

        /// <summary>
        /// Creates a new Probe.
        /// </summary>
        public Probe MkProbe(string name)
        {

            return new Probe(this, name);
        }

        /// <summary>
        /// Create a probe that always evaluates to <paramref name="val"/>.
        /// </summary>
        public Probe ConstProbe(double val)
        {

            return new Probe(this, Native.Z3_probe_const(nCtx, val));
        }

        /// <summary>
        /// Create a probe that evaluates to "true" when the value returned by <paramref name="p1"/>
        /// is less than the value returned by <paramref name="p2"/>
        /// </summary>
        public Probe Lt(Probe p1, Probe p2)
        {
            Debug.Assert(p1 != null);
            Debug.Assert(p2 != null);

            CheckContextMatch(p1);
            CheckContextMatch(p2);
            return new Probe(this, Native.Z3_probe_lt(nCtx, p1.NativeObject, p2.NativeObject));
        }

        /// <summary>
        /// Create a probe that evaluates to "true" when the value returned by <paramref name="p1"/>
        /// is greater than the value returned by <paramref name="p2"/>
        /// </summary>
        public Probe Gt(Probe p1, Probe p2)
        {
            Debug.Assert(p1 != null);
            Debug.Assert(p2 != null);

            CheckContextMatch(p1);
            CheckContextMatch(p2);
            return new Probe(this, Native.Z3_probe_gt(nCtx, p1.NativeObject, p2.NativeObject));
        }

        /// <summary>
        /// Create a probe that evaluates to "true" when the value returned by <paramref name="p1"/>
        /// is less than or equal the value returned by <paramref name="p2"/>
        /// </summary>
        public Probe Le(Probe p1, Probe p2)
        {
            Debug.Assert(p1 != null);
            Debug.Assert(p2 != null);

            CheckContextMatch(p1);
            CheckContextMatch(p2);
            return new Probe(this, Native.Z3_probe_le(nCtx, p1.NativeObject, p2.NativeObject));
        }

        /// <summary>
        /// Create a probe that evaluates to "true" when the value returned by <paramref name="p1"/>
        /// is greater than or equal the value returned by <paramref name="p2"/>
        /// </summary>
        public Probe Ge(Probe p1, Probe p2)
        {
            Debug.Assert(p1 != null);
            Debug.Assert(p2 != null);

            CheckContextMatch(p1);
            CheckContextMatch(p2);
            return new Probe(this, Native.Z3_probe_ge(nCtx, p1.NativeObject, p2.NativeObject));
        }

        /// <summary>
        /// Create a probe that evaluates to "true" when the value returned by <paramref name="p1"/>
        /// is equal to the value returned by <paramref name="p2"/>
        /// </summary>
        public Probe Eq(Probe p1, Probe p2)
        {
            Debug.Assert(p1 != null);
            Debug.Assert(p2 != null);

            CheckContextMatch(p1);
            CheckContextMatch(p2);
            return new Probe(this, Native.Z3_probe_eq(nCtx, p1.NativeObject, p2.NativeObject));
        }

        /// <summary>
        /// Create a probe that evaluates to "true" when the value <paramref name="p1"/>
        /// and <paramref name="p2"/> evaluate to "true".
        /// </summary>
        public Probe And(Probe p1, Probe p2)
        {
            Debug.Assert(p1 != null);
            Debug.Assert(p2 != null);

            CheckContextMatch(p1);
            CheckContextMatch(p2);
            return new Probe(this, Native.Z3_probe_and(nCtx, p1.NativeObject, p2.NativeObject));
        }

        /// <summary>
        /// Create a probe that evaluates to "true" when the value <paramref name="p1"/>
        /// or <paramref name="p2"/> evaluate to "true".
        /// </summary>
        public Probe Or(Probe p1, Probe p2)
        {
            Debug.Assert(p1 != null);
            Debug.Assert(p2 != null);

            CheckContextMatch(p1);
            CheckContextMatch(p2);
            return new Probe(this, Native.Z3_probe_or(nCtx, p1.NativeObject, p2.NativeObject));
        }

        /// <summary>
        /// Create a probe that evaluates to "true" when the value <paramref name="p"/>
        /// does not evaluate to "true".
        /// </summary>
        public Probe Not(Probe p)
        {
            Debug.Assert(p != null);

            CheckContextMatch(p);
            return new Probe(this, Native.Z3_probe_not(nCtx, p.NativeObject));
        }
        #endregion

        #region Solvers
        /// <summary>
        /// Creates a new (incremental) solver.
        /// </summary>
        /// <remarks>
        /// This solver also uses a set of builtin tactics for handling the first
        /// check-sat command, and check-sat commands that take more than a given
        /// number of milliseconds to be solved.
        /// </remarks>
        public Solver MkSolver(Symbol logic = null)
        {

            if (logic == null)
                return new Solver(this, Native.Z3_mk_solver(nCtx));
            else
                return new Solver(this, Native.Z3_mk_solver_for_logic(nCtx, logic.NativeObject));
        }

        /// <summary>
        /// Creates a new (incremental) solver.
        /// </summary>
        /// <seealso cref="MkSolver(Symbol)"/>
        public Solver MkSolver(string logic)
        {

            return MkSolver(MkSymbol(logic));
        }

        /// <summary>
        /// Creates a new (incremental) solver.
        /// </summary>
        public Solver MkSimpleSolver()
        {

            return new Solver(this, Native.Z3_mk_simple_solver(nCtx));
        }

        /// <summary>
        /// Creates a solver that is implemented using the given tactic.
        /// </summary>
        /// <remarks>
        /// The solver supports the commands <c>Push</c> and <c>Pop</c>, but it
        /// will always solve each check from scratch.
        /// </remarks>
        public Solver MkSolver(Tactic t)
        {
            Debug.Assert(t != null);

            return new Solver(this, Native.Z3_mk_solver_from_tactic(nCtx, t.NativeObject));
        }
        #endregion

        #region Fixedpoints
        /// <summary>
        /// Create a Fixedpoint context.
        /// </summary>
        public Fixedpoint MkFixedpoint()
        {

            return new Fixedpoint(this);
        }
        #endregion

        #region Optimization
        /// <summary>
        /// Create an Optimization context.
        /// </summary>
        public Optimize MkOptimize()
        {

            return new Optimize(this);
        }
        #endregion

        #region Floating-Point Arithmetic

        #region Rounding Modes
        #region RoundingMode Sort
        /// <summary>
        /// Create the floating-point RoundingMode sort.
        /// </summary>
        public FPRMSort MkFPRoundingModeSort()
        {
            return new FPRMSort(this);
        }
        #endregion

        #region Numerals
        /// <summary>
        /// Create a numeral of RoundingMode sort which represents the NearestTiesToEven rounding mode.
        /// </summary>
        public FPRMExpr MkFPRoundNearestTiesToEven()
        {
            return new FPRMExpr(this, Native.Z3_mk_fpa_round_nearest_ties_to_even(nCtx));
        }

        /// <summary>
        /// Create a numeral of RoundingMode sort which represents the NearestTiesToEven rounding mode.
        /// </summary>
        public FPRMNum MkFPRNE()
        {
            return new FPRMNum(this, Native.Z3_mk_fpa_rne(nCtx));
        }

        /// <summary>
        /// Create a numeral of RoundingMode sort which represents the NearestTiesToAway rounding mode.
        /// </summary>
        public FPRMNum MkFPRoundNearestTiesToAway()
        {
            return new FPRMNum(this, Native.Z3_mk_fpa_round_nearest_ties_to_away(nCtx));
        }

        /// <summary>
        /// Create a numeral of RoundingMode sort which represents the NearestTiesToAway rounding mode.
        /// </summary>
        public FPRMNum MkFPRNA()
        {
            return new FPRMNum(this, Native.Z3_mk_fpa_rna(nCtx));
        }

        /// <summary>
        /// Create a numeral of RoundingMode sort which represents the RoundTowardPositive rounding mode.
        /// </summary>
        public FPRMNum MkFPRoundTowardPositive()
        {
            return new FPRMNum(this, Native.Z3_mk_fpa_round_toward_positive(nCtx));
        }

        /// <summary>
        /// Create a numeral of RoundingMode sort which represents the RoundTowardPositive rounding mode.
        /// </summary>
        public FPRMNum MkFPRTP()
        {
            return new FPRMNum(this, Native.Z3_mk_fpa_rtp(nCtx));
        }

        /// <summary>
        /// Create a numeral of RoundingMode sort which represents the RoundTowardNegative rounding mode.
        /// </summary>
        public FPRMNum MkFPRoundTowardNegative()
        {
            return new FPRMNum(this, Native.Z3_mk_fpa_round_toward_negative(nCtx));
        }

        /// <summary>
        /// Create a numeral of RoundingMode sort which represents the RoundTowardNegative rounding mode.
        /// </summary>
        public FPRMNum MkFPRTN()
        {
            return new FPRMNum(this, Native.Z3_mk_fpa_rtn(nCtx));
        }

        /// <summary>
        /// Create a numeral of RoundingMode sort which represents the RoundTowardZero rounding mode.
        /// </summary>
        public FPRMNum MkFPRoundTowardZero()
        {
            return new FPRMNum(this, Native.Z3_mk_fpa_round_toward_zero(nCtx));
        }

        /// <summary>
        /// Create a numeral of RoundingMode sort which represents the RoundTowardZero rounding mode.
        /// </summary>
        public FPRMNum MkFPRTZ()
        {
            return new FPRMNum(this, Native.Z3_mk_fpa_rtz(nCtx));
        }
        #endregion
        #endregion

        #region FloatingPoint Sorts
        /// <summary>
        /// Create a FloatingPoint sort.
        /// </summary>
        /// <param name="ebits">exponent bits in the FloatingPoint sort.</param>
        /// <param name="sbits">significand bits in the FloatingPoint sort.</param>
        public FPSort MkFPSort(uint ebits, uint sbits)
        {
            return new FPSort(this, ebits, sbits);
        }

        /// <summary>
        /// Create the half-precision (16-bit) FloatingPoint sort.
        /// </summary>
        public FPSort MkFPSortHalf()
        {
            return new FPSort(this, Native.Z3_mk_fpa_sort_half(nCtx));
        }

        /// <summary>
        /// Create the half-precision (16-bit) FloatingPoint sort.
        /// </summary>
        public FPSort MkFPSort16()
        {
            return new FPSort(this, Native.Z3_mk_fpa_sort_16(nCtx));
        }

        /// <summary>
        /// Create the single-precision (32-bit) FloatingPoint sort.
        /// </summary>
        public FPSort MkFPSortSingle()
        {
            return new FPSort(this, Native.Z3_mk_fpa_sort_single(nCtx));
        }

        /// <summary>
        /// Create the single-precision (32-bit) FloatingPoint sort.
        /// </summary>
        public FPSort MkFPSort32()
        {
            return new FPSort(this, Native.Z3_mk_fpa_sort_32(nCtx));
        }

        /// <summary>
        /// Create the double-precision (64-bit) FloatingPoint sort.
        /// </summary>
        public FPSort MkFPSortDouble()
        {
            return new FPSort(this, Native.Z3_mk_fpa_sort_double(nCtx));
        }

        /// <summary>
        /// Create the double-precision (64-bit) FloatingPoint sort.
        /// </summary>
        public FPSort MkFPSort64()
        {
            return new FPSort(this, Native.Z3_mk_fpa_sort_64(nCtx));
        }

        /// <summary>
        /// Create the quadruple-precision (128-bit) FloatingPoint sort.
        /// </summary>
        public FPSort MkFPSortQuadruple()
        {
            return new FPSort(this, Native.Z3_mk_fpa_sort_quadruple(nCtx));
        }

        /// <summary>
        /// Create the quadruple-precision (128-bit) FloatingPoint sort.
        /// </summary>
        public FPSort MkFPSort128()
        {
            return new FPSort(this, Native.Z3_mk_fpa_sort_128(nCtx));
        }
        #endregion

        #region Numerals
        /// <summary>
        /// Create a NaN of sort s.
        /// </summary>
        /// <param name="s">FloatingPoint sort.</param>
        public FPNum MkFPNaN(FPSort s)
        {
            return new FPNum(this, Native.Z3_mk_fpa_nan(nCtx, s.NativeObject));
        }

        /// <summary>
        /// Create a floating-point infinity of sort s.
        /// </summary>
        /// <param name="s">FloatingPoint sort.</param>
        /// <param name="negative">indicates whether the result should be negative.</param>
        public FPNum MkFPInf(FPSort s, bool negative)
        {
            return new FPNum(this, Native.Z3_mk_fpa_inf(nCtx, s.NativeObject, (byte)(negative ? 1 : 0)));
        }

        /// <summary>
        /// Create a floating-point zero of sort s.
        /// </summary>
        /// <param name="s">FloatingPoint sort.</param>
        /// <param name="negative">indicates whether the result should be negative.</param>
        public FPNum MkFPZero(FPSort s, bool negative)
        {
            return new FPNum(this, Native.Z3_mk_fpa_zero(nCtx, s.NativeObject, (byte)(negative  ? 1 : 0)));
        }

        /// <summary>
        /// Create a numeral of FloatingPoint sort from a float.
        /// </summary>
        /// <param name="v">numeral value.</param>
        /// <param name="s">FloatingPoint sort.</param>
        public FPNum MkFPNumeral(float v, FPSort s)
        {
            return new FPNum(this, Native.Z3_mk_fpa_numeral_float(nCtx, v, s.NativeObject));
        }

        /// <summary>
        /// Create a numeral of FloatingPoint sort from a float.
        /// </summary>
        /// <param name="v">numeral value.</param>
        /// <param name="s">FloatingPoint sort.</param>
        public FPNum MkFPNumeral(double v, FPSort s)
        {
            return new FPNum(this, Native.Z3_mk_fpa_numeral_double(nCtx, v, s.NativeObject));
        }

        /// <summary>
        /// Create a numeral of FloatingPoint sort from an int.
        /// </summary>
        /// <param name="v">numeral value.</param>
        /// <param name="s">FloatingPoint sort.</param>
        public FPNum MkFPNumeral(int v, FPSort s)
        {
            return new FPNum(this, Native.Z3_mk_fpa_numeral_int(nCtx, v, s.NativeObject));
        }

        /// <summary>
        /// Create a numeral of FloatingPoint sort from a sign bit and two integers.
        /// </summary>
        /// <param name="sgn">the sign.</param>
        /// <param name="sig">the significand.</param>
        /// <param name="exp">the exponent.</param>
        /// <param name="s">FloatingPoint sort.</param>
        public FPNum MkFPNumeral(bool sgn, uint sig, int exp, FPSort s)
        {
            return new FPNum(this, Native.Z3_mk_fpa_numeral_int_uint(nCtx, (byte)(sgn  ? 1 : 0), exp, sig, s.NativeObject));
        }

        /// <summary>
        /// Create a numeral of FloatingPoint sort from a sign bit and two 64-bit integers.
        /// </summary>
        /// <param name="sgn">the sign.</param>
        /// <param name="sig">the significand.</param>
        /// <param name="exp">the exponent.</param>
        /// <param name="s">FloatingPoint sort.</param>
        public FPNum MkFPNumeral(bool sgn, Int64 exp, UInt64 sig, FPSort s)
        {
            return new FPNum(this, Native.Z3_mk_fpa_numeral_int64_uint64(nCtx, (byte)(sgn  ? 1 : 0), exp, sig, s.NativeObject));
        }

        /// <summary>
        /// Create a numeral of FloatingPoint sort from a float.
        /// </summary>
        /// <param name="v">numeral value.</param>
        /// <param name="s">FloatingPoint sort.</param>
        public FPNum MkFP(float v, FPSort s)
        {
            return MkFPNumeral(v, s);
        }

        /// <summary>
        /// Create a numeral of FloatingPoint sort from a float.
        /// </summary>
        /// <param name="v">numeral value.</param>
        /// <param name="s">FloatingPoint sort.</param>
        public FPNum MkFP(double v, FPSort s)
        {
            return MkFPNumeral(v, s);
        }

        /// <summary>
        /// Create a numeral of FloatingPoint sort from an int.
        /// </summary>
        /// <param name="v">numeral value.</param>
        /// <param name="s">FloatingPoint sort.</param>
        public FPNum MkFP(int v, FPSort s)
        {
            return MkFPNumeral(v, s);
        }

        /// <summary>
        /// Create a numeral of FloatingPoint sort from a sign bit and two integers.
        /// </summary>
        /// <param name="sgn">the sign.</param>
        /// <param name="exp">the exponent.</param>
        /// <param name="sig">the significand.</param>
        /// <param name="s">FloatingPoint sort.</param>
        public FPNum MkFP(bool sgn, int exp, uint sig, FPSort s)
        {
            return MkFPNumeral(sgn, exp, sig, s);
        }

        /// <summary>
        /// Create a numeral of FloatingPoint sort from a sign bit and two 64-bit integers.
        /// </summary>
        /// <param name="sgn">the sign.</param>
        /// <param name="exp">the exponent.</param>
        /// <param name="sig">the significand.</param>
        /// <param name="s">FloatingPoint sort.</param>
        public FPNum MkFP(bool sgn, Int64 exp, UInt64 sig, FPSort s)
        {
            return MkFPNumeral(sgn, exp, sig, s);
        }

        #endregion

        #region Operators
        /// <summary>
        /// Floating-point absolute value
        /// </summary>
        /// <param name="t">floating-point term</param>
        public FPExpr MkFPAbs(FPExpr t)
        {
            return new FPExpr(this, Native.Z3_mk_fpa_abs(this.nCtx, t.NativeObject));
        }

        /// <summary>
        /// Floating-point negation
        /// </summary>
        /// <param name="t">floating-point term</param>
        public FPExpr MkFPNeg(FPExpr t)
        {
            return new FPExpr(this, Native.Z3_mk_fpa_neg(this.nCtx, t.NativeObject));
        }

        /// <summary>
        /// Floating-point addition
        /// </summary>
        /// <param name="rm">rounding mode term</param>
        /// <param name="t1">floating-point term</param>
        /// <param name="t2">floating-point term</param>
        public FPExpr MkFPAdd(FPRMExpr rm, FPExpr t1, FPExpr t2)
        {
            return new FPExpr(this, Native.Z3_mk_fpa_add(this.nCtx, rm.NativeObject, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Floating-point subtraction
        /// </summary>
        /// <param name="rm">rounding mode term</param>
        /// <param name="t1">floating-point term</param>
        /// <param name="t2">floating-point term</param>
        public FPExpr MkFPSub(FPRMExpr rm, FPExpr t1, FPExpr t2)
        {
            return new FPExpr(this, Native.Z3_mk_fpa_sub(this.nCtx, rm.NativeObject, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Floating-point multiplication
        /// </summary>
        /// <param name="rm">rounding mode term</param>
        /// <param name="t1">floating-point term</param>
        /// <param name="t2">floating-point term</param>
        public FPExpr MkFPMul(FPRMExpr rm, FPExpr t1, FPExpr t2)
        {
            return new FPExpr(this, Native.Z3_mk_fpa_mul(this.nCtx, rm.NativeObject, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Floating-point division
        /// </summary>
        /// <param name="rm">rounding mode term</param>
        /// <param name="t1">floating-point term</param>
        /// <param name="t2">floating-point term</param>
        public FPExpr MkFPDiv(FPRMExpr rm, FPExpr t1, FPExpr t2)
        {
            return new FPExpr(this, Native.Z3_mk_fpa_div(this.nCtx, rm.NativeObject, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Floating-point fused multiply-add
        /// </summary>
        /// <remarks>
        /// The result is round((t1 * t2) + t3)
        /// </remarks>
        /// <param name="rm">rounding mode term</param>
        /// <param name="t1">floating-point term</param>
        /// <param name="t2">floating-point term</param>
        /// <param name="t3">floating-point term</param>
        public FPExpr MkFPFMA(FPRMExpr rm, FPExpr t1, FPExpr t2, FPExpr t3)
        {
            return new FPExpr(this, Native.Z3_mk_fpa_fma(this.nCtx, rm.NativeObject, t1.NativeObject, t2.NativeObject, t3.NativeObject));
        }

        /// <summary>
        /// Floating-point square root
        /// </summary>
        /// <param name="rm">rounding mode term</param>
        /// <param name="t">floating-point term</param>
        public FPExpr MkFPSqrt(FPRMExpr rm, FPExpr t)
        {
            return new FPExpr(this, Native.Z3_mk_fpa_sqrt(this.nCtx, rm.NativeObject, t.NativeObject));
        }

        /// <summary>
        /// Floating-point remainder
        /// </summary>
        /// <param name="t1">floating-point term</param>
        /// <param name="t2">floating-point term</param>
        public FPExpr MkFPRem(FPExpr t1, FPExpr t2)
        {
            return new FPExpr(this, Native.Z3_mk_fpa_rem(this.nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Floating-point roundToIntegral. Rounds a floating-point number to
        /// the closest integer, again represented as a floating-point number.
        /// </summary>
        /// <param name="rm">term of RoundingMode sort</param>
        /// <param name="t">floating-point term</param>
        public FPExpr MkFPRoundToIntegral(FPRMExpr rm, FPExpr t)
        {
            return new FPExpr(this, Native.Z3_mk_fpa_round_to_integral(this.nCtx, rm.NativeObject, t.NativeObject));
        }

        /// <summary>
        /// Minimum of floating-point numbers.
        /// </summary>
        /// <param name="t1">floating-point term</param>
        /// <param name="t2">floating-point term</param>
        public FPExpr MkFPMin(FPExpr t1, FPExpr t2)
        {
            return new FPExpr(this, Native.Z3_mk_fpa_min(this.nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Maximum of floating-point numbers.
        /// </summary>
        /// <param name="t1">floating-point term</param>
        /// <param name="t2">floating-point term</param>
        public FPExpr MkFPMax(FPExpr t1, FPExpr t2)
        {
            return new FPExpr(this, Native.Z3_mk_fpa_max(this.nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Floating-point less than or equal.
        /// </summary>
        /// <param name="t1">floating-point term</param>
        /// <param name="t2">floating-point term</param>
        public BoolExpr MkFPLEq(FPExpr t1, FPExpr t2)
        {
            return new BoolExpr(this, Native.Z3_mk_fpa_leq(this.nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Floating-point less than.
        /// </summary>
        /// <param name="t1">floating-point term</param>
        /// <param name="t2">floating-point term</param>
        public BoolExpr MkFPLt(FPExpr t1, FPExpr t2)
        {
            return new BoolExpr(this, Native.Z3_mk_fpa_lt(this.nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Floating-point greater than or equal.
        /// </summary>
        /// <param name="t1">floating-point term</param>
        /// <param name="t2">floating-point term</param>
        public BoolExpr MkFPGEq(FPExpr t1, FPExpr t2)
        {
            return new BoolExpr(this, Native.Z3_mk_fpa_geq(this.nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Floating-point greater than.
        /// </summary>
        /// <param name="t1">floating-point term</param>
        /// <param name="t2">floating-point term</param>
        public BoolExpr MkFPGt(FPExpr t1, FPExpr t2)
        {
            return new BoolExpr(this, Native.Z3_mk_fpa_gt(this.nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Floating-point equality.
        /// </summary>
        /// <remarks>
        /// Note that this is IEEE 754 equality (as opposed to standard =).
        /// </remarks>
        /// <param name="t1">floating-point term</param>
        /// <param name="t2">floating-point term</param>
        public BoolExpr MkFPEq(FPExpr t1, FPExpr t2)
        {
            return new BoolExpr(this, Native.Z3_mk_fpa_eq(this.nCtx, t1.NativeObject, t2.NativeObject));
        }

        /// <summary>
        /// Predicate indicating whether t is a normal floating-point number.
        /// </summary>
        /// <param name="t">floating-point term</param>
        public BoolExpr MkFPIsNormal(FPExpr t)
        {
            return new BoolExpr(this, Native.Z3_mk_fpa_is_normal(this.nCtx, t.NativeObject));
        }

        /// <summary>
        /// Predicate indicating whether t is a subnormal floating-point number.
        /// </summary>
        /// <param name="t">floating-point term</param>
        public BoolExpr MkFPIsSubnormal(FPExpr t)
        {
            return new BoolExpr(this, Native.Z3_mk_fpa_is_subnormal(this.nCtx, t.NativeObject));
        }

        /// <summary>
        /// Predicate indicating whether t is a floating-point number with zero value, i.e., +0 or -0.
        /// </summary>
        /// <param name="t">floating-point term</param>
        public BoolExpr MkFPIsZero(FPExpr t)
        {
            return new BoolExpr(this, Native.Z3_mk_fpa_is_zero(this.nCtx, t.NativeObject));
        }

        /// <summary>
        /// Predicate indicating whether t is a floating-point number representing +oo or -oo.
        /// </summary>
        /// <param name="t">floating-point term</param>
        public BoolExpr MkFPIsInfinite(FPExpr t)
        {
            return new BoolExpr(this, Native.Z3_mk_fpa_is_infinite(this.nCtx, t.NativeObject));
        }

        /// <summary>
        /// Predicate indicating whether t is a NaN.
        /// </summary>
        /// <param name="t">floating-point term</param>
        public BoolExpr MkFPIsNaN(FPExpr t)
        {
            return new BoolExpr(this, Native.Z3_mk_fpa_is_nan(this.nCtx, t.NativeObject));
        }

        /// <summary>
        /// Predicate indicating whether t is a negative floating-point number.
        /// </summary>
        /// <param name="t">floating-point term</param>
        public BoolExpr MkFPIsNegative(FPExpr t)
        {
            return new BoolExpr(this, Native.Z3_mk_fpa_is_negative(this.nCtx, t.NativeObject));
        }

        /// <summary>
        /// Predicate indicating whether t is a positive floating-point number.
        /// </summary>
        /// <param name="t">floating-point term</param>
        public BoolExpr MkFPIsPositive(FPExpr t)
        {
            return new BoolExpr(this, Native.Z3_mk_fpa_is_positive(this.nCtx, t.NativeObject));
        }
        #endregion

        #region Conversions to FloatingPoint terms
        /// <summary>
        /// Create an expression of FloatingPoint sort from three bit-vector expressions.
        /// </summary>
        /// <remarks>
        /// This is the operator named `fp' in the SMT FP theory definition.
        /// Note that sgn is required to be a bit-vector of size 1. Significand and exponent
        /// are required to be greater than 1 and 2 respectively. The FloatingPoint sort
        /// of the resulting expression is automatically determined from the bit-vector sizes
        /// of the arguments.
        /// </remarks>
        /// <param name="sgn">bit-vector term (of size 1) representing the sign.</param>
        /// <param name="sig">bit-vector term representing the significand.</param>
        /// <param name="exp">bit-vector term representing the exponent.</param>
        public FPExpr MkFP(BitVecExpr sgn, BitVecExpr sig, BitVecExpr exp)
        {
            return new FPExpr(this, Native.Z3_mk_fpa_fp(this.nCtx, sgn.NativeObject, sig.NativeObject, exp.NativeObject));
        }

        /// <summary>
        /// Conversion of a single IEEE 754-2008 bit-vector into a floating-point number.
        /// </summary>
        /// <remarks>
        /// Produces a term that represents the conversion of a bit-vector term bv to a
        /// floating-point term of sort s. The bit-vector size of bv (m) must be equal
        /// to ebits+sbits of s. The format of the bit-vector is as defined by the
        /// IEEE 754-2008 interchange format.
        /// </remarks>
        /// <param name="bv">bit-vector value (of size m).</param>
        /// <param name="s">FloatingPoint sort (ebits+sbits == m)</param>
        public FPExpr MkFPToFP(BitVecExpr bv, FPSort s)
        {
            return new FPExpr(this, Native.Z3_mk_fpa_to_fp_bv(this.nCtx, bv.NativeObject, s.NativeObject));
        }

        /// <summary>
        /// Conversion of a FloatingPoint term into another term of different FloatingPoint sort.
        /// </summary>
        /// <remarks>
        /// Produces a term that represents the conversion of a floating-point term t to a
        /// floating-point term of sort s. If necessary, the result will be rounded according
        /// to rounding mode rm.
        /// </remarks>
        /// <param name="rm">RoundingMode term.</param>
        /// <param name="t">FloatingPoint term.</param>
        /// <param name="s">FloatingPoint sort.</param>
        public FPExpr MkFPToFP(FPRMExpr rm, FPExpr t, FPSort s)
        {
            return new FPExpr(this, Native.Z3_mk_fpa_to_fp_float(this.nCtx, rm.NativeObject, t.NativeObject, s.NativeObject));
        }

        /// <summary>
        /// Conversion of a term of real sort into a term of FloatingPoint sort.
        /// </summary>
        /// <remarks>
        /// Produces a term that represents the conversion of term t of real sort into a
        /// floating-point term of sort s. If necessary, the result will be rounded according
        /// to rounding mode rm.
        /// </remarks>
        /// <param name="rm">RoundingMode term.</param>
        /// <param name="t">term of Real sort.</param>
        /// <param name="s">FloatingPoint sort.</param>
        public FPExpr MkFPToFP(FPRMExpr rm, RealExpr t, FPSort s)
        {
            return new FPExpr(this, Native.Z3_mk_fpa_to_fp_real(this.nCtx, rm.NativeObject, t.NativeObject, s.NativeObject));
        }

        /// <summary>
        /// Conversion of a 2's complement signed bit-vector term into a term of FloatingPoint sort.
        /// </summary>
        /// <remarks>
        /// Produces a term that represents the conversion of the bit-vector term t into a
        /// floating-point term of sort s. The bit-vector t is taken to be in signed
        /// 2's complement format (when signed==true, otherwise unsigned). If necessary, the
        /// result will be rounded according to rounding mode rm.
        /// </remarks>
        /// <param name="rm">RoundingMode term.</param>
        /// <param name="t">term of bit-vector sort.</param>
        /// <param name="s">FloatingPoint sort.</param>
        /// <param name="signed">flag indicating whether t is interpreted as signed or unsigned bit-vector.</param>
        public FPExpr MkFPToFP(FPRMExpr rm, BitVecExpr t, FPSort s, bool signed)
        {
            if (signed)
                return new FPExpr(this, Native.Z3_mk_fpa_to_fp_signed(this.nCtx, rm.NativeObject, t.NativeObject, s.NativeObject));
            else
                return new FPExpr(this, Native.Z3_mk_fpa_to_fp_unsigned(this.nCtx, rm.NativeObject, t.NativeObject, s.NativeObject));
        }

        /// <summary>
        /// Conversion of a floating-point number to another FloatingPoint sort s.
        /// </summary>
        /// <remarks>
        /// Produces a term that represents the conversion of a floating-point term t to a different
        /// FloatingPoint sort s. If necessary, rounding according to rm is applied.
        /// </remarks>
        /// <param name="s">FloatingPoint sort</param>
        /// <param name="rm">floating-point rounding mode term</param>
        /// <param name="t">floating-point term</param>
        public FPExpr MkFPToFP(FPSort s, FPRMExpr rm, FPExpr t)
        {
            return new FPExpr(this, Native.Z3_mk_fpa_to_fp_float(this.nCtx, s.NativeObject, rm.NativeObject, t.NativeObject));
        }
        #endregion

        #region Conversions from FloatingPoint terms
        /// <summary>
        /// Conversion of a floating-point term into a bit-vector.
        /// </summary>
        /// <remarks>
        /// Produces a term that represents the conversion of the floating-point term t into a
        /// bit-vector term of size sz in 2's complement format (signed when signed==true). If necessary,
        /// the result will be rounded according to rounding mode rm.
        /// </remarks>
        /// <param name="rm">RoundingMode term.</param>
        /// <param name="t">FloatingPoint term</param>
        /// <param name="sz">Size of the resulting bit-vector.</param>
        /// <param name="signed">Indicates whether the result is a signed or unsigned bit-vector.</param>
        public BitVecExpr MkFPToBV(FPRMExpr rm, FPExpr t, uint sz, bool signed)
        {
            if (signed)
                return new BitVecExpr(this, Native.Z3_mk_fpa_to_sbv(this.nCtx, rm.NativeObject, t.NativeObject, sz));
            else
                return new BitVecExpr(this, Native.Z3_mk_fpa_to_ubv(this.nCtx, rm.NativeObject, t.NativeObject, sz));
        }

        /// <summary>
        /// Conversion of a floating-point term into a real-numbered term.
        /// </summary>
        /// <remarks>
        /// Produces a term that represents the conversion of the floating-point term t into a
        /// real number. Note that this type of conversion will often result in non-linear
        /// constraints over real terms.
        /// </remarks>
        /// <param name="t">FloatingPoint term</param>
        public RealExpr MkFPToReal(FPExpr t)
        {
            return new RealExpr(this, Native.Z3_mk_fpa_to_real(this.nCtx, t.NativeObject));
        }
        #endregion

        #region Z3-specific extensions
        /// <summary>
        /// Conversion of a floating-point term into a bit-vector term in IEEE 754-2008 format.
        /// </summary>
        /// <remarks>
        /// The size of the resulting bit-vector is automatically determined. Note that
        /// IEEE 754-2008 allows multiple different representations of NaN. This conversion
        /// knows only one NaN and it will always produce the same bit-vector representation of
        /// that NaN.
        /// </remarks>
        /// <param name="t">FloatingPoint term.</param>
        public BitVecExpr MkFPToIEEEBV(FPExpr t)
        {
            return new BitVecExpr(this, Native.Z3_mk_fpa_to_ieee_bv(this.nCtx, t.NativeObject));
        }

        /// <summary>
        /// Conversion of a real-sorted significand and an integer-sorted exponent into a term of FloatingPoint sort.
        /// </summary>
        /// <remarks>
        /// Produces a term that represents the conversion of sig * 2^exp into a
        /// floating-point term of sort s. If necessary, the result will be rounded
        /// according to rounding mode rm.
        /// </remarks>
        /// <param name="rm">RoundingMode term.</param>
        /// <param name="exp">Exponent term of Int sort.</param>
        /// <param name="sig">Significand term of Real sort.</param>
        /// <param name="s">FloatingPoint sort.</param>
        public BitVecExpr MkFPToFP(FPRMExpr rm, IntExpr exp, RealExpr sig, FPSort s)
        {
            return new BitVecExpr(this, Native.Z3_mk_fpa_to_fp_int_real(this.nCtx, rm.NativeObject, exp.NativeObject, sig.NativeObject, s.NativeObject));
        }
        #endregion
        #endregion // Floating-point Arithmetic

        #region Miscellaneous
        /// <summary>
        /// Wraps an AST.
        /// </summary>
        /// <remarks>This function is used for transitions between native and
        /// managed objects. Note that <paramref name="nativeObject"/> must be a
        /// native object obtained from Z3 (e.g., through <seealso cref="UnwrapAST"/>)
        /// and that it must have a correct reference count (see e.g.,
        /// <seealso cref="Native.Z3_inc_ref"/>.</remarks>
        /// <seealso cref="UnwrapAST"/>
        /// <param name="nativeObject">The native pointer to wrap.</param>
        public AST WrapAST(IntPtr nativeObject)
        {
            return AST.Create(this, nativeObject);
        }

        /// <summary>
        /// Unwraps an AST.
        /// </summary>
        /// <remarks>This function is used for transitions between native and
        /// managed objects. It returns the native pointer to the AST. Note that
        /// AST objects are reference counted and unwrapping an AST disables automatic
        /// reference counting, i.e., all references to the IntPtr that is returned
        /// must be handled externally and through native calls (see e.g.,
        /// <seealso cref="Native.Z3_inc_ref"/>).</remarks>
        /// <seealso cref="WrapAST"/>
        /// <param name="a">The AST to unwrap.</param>
        public IntPtr UnwrapAST(AST a)
        {
            return a.NativeObject;
        }

        /// <summary>
        /// Return a string describing all available parameters to <c>Expr.Simplify</c>.
        /// </summary>
        public string SimplifyHelp()
        {

            return Native.Z3_simplify_get_help(nCtx);
        }

        /// <summary>
        /// Retrieves parameter descriptions for simplifier.
        /// </summary>
        public ParamDescrs SimplifyParameterDescriptions
        {
            get { return new ParamDescrs(this, Native.Z3_simplify_get_param_descrs(nCtx)); }
        }
        #endregion

        #region Error Handling
        ///// <summary>
        ///// A delegate which is executed when an error is raised.
        ///// </summary>
        ///// <remarks>
        ///// Note that it is possible for memory leaks to occur if error handlers
        ///// throw exceptions.
        ///// </remarks>
        //public delegate void ErrorHandler(Context ctx, Z3_error_code errorCode, string errorString);

        ///// <summary>
        ///// The OnError event.
        ///// </summary>
        //public event ErrorHandler OnError = null;
        #endregion

        #region Parameters
        /// <summary>
        /// Update a mutable configuration parameter.
        /// </summary>
        /// <remarks>
        /// The list of all configuration parameters can be obtained using the Z3 executable:
        /// <c>z3.exe -p</c>
        /// Only a few configuration parameters are mutable once the context is created.
        /// An exception is thrown when trying to modify an immutable parameter.
        /// </remarks>
        public void UpdateParamValue(string id, string value)
        {
            Native.Z3_update_param_value(nCtx, id, value);
        }

        #endregion

        #region Internal
        internal IntPtr m_ctx = IntPtr.Zero;
        internal Native.Z3_error_handler m_n_err_handler = null;
        internal static Object creation_lock = new Object();
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

        internal void CheckContextMatch(Z3Object other)
        {
            Debug.Assert(other != null);

            if (!ReferenceEquals(this, other.Context))
                throw new Z3Exception("Context mismatch");
        }

        internal void CheckContextMatch(Z3Object other1, Z3Object other2)
        {
            Debug.Assert(other1 != null);
            Debug.Assert(other2 != null);
            CheckContextMatch(other1);
            CheckContextMatch(other2);
        }

        internal void CheckContextMatch(Z3Object other1, Z3Object other2, Z3Object other3)
        {
            Debug.Assert(other1 != null);
            Debug.Assert(other2 != null);
            Debug.Assert(other3 != null);
            CheckContextMatch(other1);
            CheckContextMatch(other2);
            CheckContextMatch(other3);
        }

        internal void CheckContextMatch(Z3Object[] arr)
        {
            Debug.Assert(arr == null || arr.All(a => a != null));

            if (arr != null)
            {
                foreach (Z3Object a in arr)
                {
                    Debug.Assert(a != null); // It was an assume, now we added the precondition, and we made it into an assert
                    CheckContextMatch(a);
                }
            }
        }

        internal void CheckContextMatch<T>(IEnumerable<T> arr) where T : Z3Object
        {
            Debug.Assert(arr == null || arr.All(a => a != null));

            if (arr != null)
            {
                foreach (Z3Object a in arr)
                {
                    Debug.Assert(a != null); // It was an assume, now we added the precondition, and we made it into an assert
                    CheckContextMatch(a);
                }
            }
        }

        private void ObjectInvariant()
        {
            Debug.Assert(m_AST_DRQ != null);
            Debug.Assert(m_ASTMap_DRQ != null);
            Debug.Assert(m_ASTVector_DRQ != null);
            Debug.Assert(m_ApplyResult_DRQ != null);
            Debug.Assert(m_FuncEntry_DRQ != null);
            Debug.Assert(m_FuncInterp_DRQ != null);
            Debug.Assert(m_Goal_DRQ != null);
            Debug.Assert(m_Model_DRQ != null);
            Debug.Assert(m_Params_DRQ != null);
            Debug.Assert(m_ParamDescrs_DRQ != null);
            Debug.Assert(m_Probe_DRQ != null);
            Debug.Assert(m_Solver_DRQ != null);
            Debug.Assert(m_Statistics_DRQ != null);
            Debug.Assert(m_Tactic_DRQ != null);
            Debug.Assert(m_Fixedpoint_DRQ != null);
            Debug.Assert(m_Optimize_DRQ != null);
        }

        readonly private AST.DecRefQueue m_AST_DRQ = new AST.DecRefQueue();
        readonly private ASTMap.DecRefQueue m_ASTMap_DRQ = new ASTMap.DecRefQueue(10);
        readonly private ASTVector.DecRefQueue m_ASTVector_DRQ = new ASTVector.DecRefQueue(10);
        readonly private ApplyResult.DecRefQueue m_ApplyResult_DRQ = new ApplyResult.DecRefQueue(10);
        readonly private FuncInterp.Entry.DecRefQueue m_FuncEntry_DRQ = new FuncInterp.Entry.DecRefQueue(10);
        readonly private FuncInterp.DecRefQueue m_FuncInterp_DRQ = new FuncInterp.DecRefQueue(10);
        readonly private Goal.DecRefQueue m_Goal_DRQ = new Goal.DecRefQueue(10);
        readonly private Model.DecRefQueue m_Model_DRQ = new Model.DecRefQueue(10);
        readonly private Params.DecRefQueue m_Params_DRQ = new Params.DecRefQueue(10);
        readonly private ParamDescrs.DecRefQueue m_ParamDescrs_DRQ = new ParamDescrs.DecRefQueue(10);
        readonly private Probe.DecRefQueue m_Probe_DRQ = new Probe.DecRefQueue(10);
        readonly private Solver.DecRefQueue m_Solver_DRQ = new Solver.DecRefQueue(10);
        readonly private Statistics.DecRefQueue m_Statistics_DRQ = new Statistics.DecRefQueue(10);
        readonly private Tactic.DecRefQueue m_Tactic_DRQ = new Tactic.DecRefQueue(10);
        readonly private Fixedpoint.DecRefQueue m_Fixedpoint_DRQ = new Fixedpoint.DecRefQueue(10);
        readonly private Optimize.DecRefQueue m_Optimize_DRQ = new Optimize.DecRefQueue(10);

        /// <summary>
        /// AST DRQ
        /// </summary>
        public IDecRefQueue AST_DRQ { get { return m_AST_DRQ; } }

        /// <summary>
        /// ASTMap DRQ
        /// </summary>
        public IDecRefQueue ASTMap_DRQ { get { return m_ASTMap_DRQ; } }

        /// <summary>
        /// ASTVector DRQ
        /// </summary>
        public IDecRefQueue ASTVector_DRQ { get {  return m_ASTVector_DRQ; } }

        /// <summary>
        /// ApplyResult DRQ
        /// </summary>
        public IDecRefQueue ApplyResult_DRQ { get {  return m_ApplyResult_DRQ; } }

        /// <summary>
        /// FuncEntry DRQ
        /// </summary>
        public IDecRefQueue FuncEntry_DRQ { get { return m_FuncEntry_DRQ; } }

        /// <summary>
        /// FuncInterp DRQ
        /// </summary>
        public IDecRefQueue FuncInterp_DRQ { get { return m_FuncInterp_DRQ; } }

        /// <summary>
        /// Goal DRQ
        /// </summary>
        public IDecRefQueue Goal_DRQ { get { return m_Goal_DRQ; } }

        /// <summary>
        /// Model DRQ
        /// </summary>
        public IDecRefQueue Model_DRQ { get { return m_Model_DRQ; } }

        /// <summary>
        /// Params DRQ
        /// </summary>
        public IDecRefQueue Params_DRQ { get { return m_Params_DRQ; } }

        /// <summary>
        /// ParamDescrs DRQ
        /// </summary>
        public IDecRefQueue ParamDescrs_DRQ { get { return m_ParamDescrs_DRQ; } }

        /// <summary>
        /// Probe DRQ
        /// </summary>
        public IDecRefQueue Probe_DRQ { get { return m_Probe_DRQ; } }

        /// <summary>
        /// Solver DRQ
        /// </summary>
        public IDecRefQueue Solver_DRQ { get { return m_Solver_DRQ; } }

        /// <summary>
        /// Statistics DRQ
        /// </summary>
        public IDecRefQueue Statistics_DRQ { get { return m_Statistics_DRQ; } }

        /// <summary>
        /// Tactic DRQ
        /// </summary>
        public IDecRefQueue Tactic_DRQ { get { return m_Tactic_DRQ; } }

        /// <summary>
        /// FixedPoint DRQ
        /// </summary>
        public IDecRefQueue Fixedpoint_DRQ { get { return m_Fixedpoint_DRQ; } }

        /// <summary>
        /// Optimize DRQ
        /// </summary>
        public IDecRefQueue Optimize_DRQ { get { return m_Fixedpoint_DRQ; } }

        internal long refCount = 0;

        /// <summary>
        /// Finalizer.
        /// </summary>
        ~Context()
        {
            // Console.WriteLine("Context Finalizer from " + System.Threading.Thread.CurrentThread.ManagedThreadId);
            Dispose();
        }

        /// <summary>
        /// Disposes of the context.
        /// </summary>
        public void Dispose()
        {
            // Console.WriteLine("Context Dispose from " + System.Threading.Thread.CurrentThread.ManagedThreadId);
            AST_DRQ.Clear(this);
            ASTMap_DRQ.Clear(this);
            ASTVector_DRQ.Clear(this);
            ApplyResult_DRQ.Clear(this);
            FuncEntry_DRQ.Clear(this);
            FuncInterp_DRQ.Clear(this);
            Goal_DRQ.Clear(this);
            Model_DRQ.Clear(this);
            Params_DRQ.Clear(this);
            ParamDescrs_DRQ.Clear(this);
            Probe_DRQ.Clear(this);
            Solver_DRQ.Clear(this);
            Statistics_DRQ.Clear(this);
            Tactic_DRQ.Clear(this);
            Fixedpoint_DRQ.Clear(this);
            Optimize_DRQ.Clear(this);

            m_boolSort = null;
            m_intSort = null;
            m_realSort = null;
            m_stringSort = null;
            if (refCount == 0 && m_ctx != IntPtr.Zero)
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
    }
}
