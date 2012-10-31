/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    Sort.cs

Abstract:

    Z3 Managed API: Sorts

Author:

    Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
--*/

using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// The Sort class implements type information for ASTs.
    /// </summary>
    [ContractVerification(true)]
    public class Sort : AST
    {
        /// <summary>
        /// Comparison operator.
        /// </summary>
        /// <param name="a">A Sort</param>
        /// <param name="b">A Sort</param>
        /// <returns>True if <paramref name="a"/> and <paramref name="b"/> are from the same context 
        /// and represent the same sort; false otherwise.</returns>
        public static bool operator ==(Sort a, Sort b)
        {
            return Object.ReferenceEquals(a, b) ||
                   (!Object.ReferenceEquals(a, null) &&
                    !Object.ReferenceEquals(b, null) &&
                    a.Context == b.Context &&
                    Native.Z3_is_eq_sort(a.Context.nCtx, a.NativeObject, b.NativeObject) != 0);
        }

        /// <summary>
        /// Comparison operator.
        /// </summary>
        /// <param name="a">A Sort</param>
        /// <param name="b">A Sort</param>
        /// <returns>True if <paramref name="a"/> and <paramref name="b"/> are not from the same context 
        /// or represent different sorts; false otherwise.</returns>
        public static bool operator !=(Sort a, Sort b)
        {
            return !(a == b);
        }

        /// <summary>
        /// Equality operator for objects of type Sort.
        /// </summary>
        /// <param name="o"></param>
        /// <returns></returns>
        public override bool Equals(object o)
        {
            Sort casted = o as Sort;
            if (casted == null) return false;
            return this == casted;
        }

        /// <summary>
        /// Hash code generation for Sorts
        /// </summary>
        /// <returns>A hash code</returns>
        public override int GetHashCode()
        {
            return base.GetHashCode();
        }

        /// <summary>
        /// Returns a unique identifier for the sort.
        /// </summary>
        new public uint Id
        {
            get { return Native.Z3_get_sort_id(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// The kind of the sort.
        /// </summary>
        public Z3_sort_kind SortKind
        {
            get { return (Z3_sort_kind)Native.Z3_get_sort_kind(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// The name of the sort
        /// </summary>
        public Symbol Name
        {
            get {
                Contract.Ensures(Contract.Result<Symbol>() != null);
                return Symbol.Create(Context, Native.Z3_get_sort_name(Context.nCtx, NativeObject)); }
        }

        /// <summary>
        /// A string representation of the sort.
        /// </summary>
        public override string ToString()
        {
            return Native.Z3_sort_to_string(Context.nCtx, NativeObject);
        }

        #region Internal
        /// <summary>
        /// Sort constructor
        /// </summary>
        internal protected Sort(Context ctx) : base(ctx) { Contract.Requires(ctx != null); }
        internal Sort(Context ctx, IntPtr obj) : base(ctx, obj) { Contract.Requires(ctx != null); }

        #if DEBUG
        internal override void CheckNativeObject(IntPtr obj)
        {
            if (Native.Z3_get_ast_kind(Context.nCtx, obj) != (uint)Z3_ast_kind.Z3_SORT_AST)
                throw new Z3Exception("Underlying object is not a sort");
            base.CheckNativeObject(obj);
        }
        #endif

        [ContractVerification(true)]
        new internal static Sort Create(Context ctx, IntPtr obj)
        {
            Contract.Requires(ctx != null);
            Contract.Ensures(Contract.Result<Sort>() != null);

            switch ((Z3_sort_kind)Native.Z3_get_sort_kind(ctx.nCtx, obj))
            {
                case Z3_sort_kind.Z3_ARRAY_SORT: return new ArraySort(ctx, obj);
                case Z3_sort_kind.Z3_BOOL_SORT: return new BoolSort(ctx, obj);
                case Z3_sort_kind.Z3_BV_SORT: return new BitVecSort(ctx, obj);
                case Z3_sort_kind.Z3_DATATYPE_SORT: return new DatatypeSort(ctx, obj);
                case Z3_sort_kind.Z3_INT_SORT: return new IntSort(ctx, obj);
                case Z3_sort_kind.Z3_REAL_SORT: return new RealSort(ctx, obj);
                case Z3_sort_kind.Z3_UNINTERPRETED_SORT: return new UninterpretedSort(ctx, obj);
                case Z3_sort_kind.Z3_FINITE_DOMAIN_SORT: return new FiniteDomainSort(ctx, obj);
                case Z3_sort_kind.Z3_RELATION_SORT: return new RelationSort(ctx, obj);
                default:
                    throw new Z3Exception("Unknown sort kind");
            }
        }
        #endregion
    }

    /// <summary>
    /// A Boolean sort.
    /// </summary>
    public class BoolSort : Sort
    {
        #region Internal
        internal BoolSort(Context ctx, IntPtr obj) : base(ctx, obj) { Contract.Requires(ctx != null); }
        internal BoolSort(Context ctx) : base(ctx, Native.Z3_mk_bool_sort(ctx.nCtx)) { Contract.Requires(ctx != null); }
        #endregion
    };

    /// <summary>
    /// An arithmetic sort, i.e., Int or Real.
    /// </summary>
    public class ArithSort : Sort
    {
        #region Internal
        internal ArithSort(Context ctx, IntPtr obj) : base(ctx, obj) { Contract.Requires(ctx != null); }
        #endregion
    };

    /// <summary>
    ///  An Integer sort
    /// </summary>
    public class IntSort : ArithSort
    {
        #region Internal
        internal IntSort(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }
        internal IntSort(Context ctx)
            : base(ctx, Native.Z3_mk_int_sort(ctx.nCtx))
        {
            Contract.Requires(ctx != null);
        }
        #endregion
    }

    /// <summary>
    /// A real sort
    /// </summary>
    public class RealSort : ArithSort
    {
        #region Internal
        internal RealSort(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }
        internal RealSort(Context ctx)
            : base(ctx, Native.Z3_mk_real_sort(ctx.nCtx))
        {
            Contract.Requires(ctx != null);
        }
        #endregion
    }

    /// <summary>
    /// Bit-vector sorts.
    /// </summary>
    public class BitVecSort : Sort
    {
        /// <summary>
        /// The size of the bit-vector sort.
        /// </summary>
        public uint Size
        {
            get { return Native.Z3_get_bv_sort_size(Context.nCtx, NativeObject); }
        }

        #region Internal
        internal BitVecSort(Context ctx, IntPtr obj) : base(ctx, obj) { Contract.Requires(ctx != null); }
        internal BitVecSort(Context ctx, uint size) : base(ctx, Native.Z3_mk_bv_sort(ctx.nCtx, size)) { Contract.Requires(ctx != null); }
        #endregion
    };

    /// <summary>
    /// Array sorts.
    /// </summary>
    [ContractVerification(true)]
    public class ArraySort : Sort
    {
        /// <summary>
        /// The domain of the array sort.
        /// </summary>
        public Sort Domain
        {
            get {
                Contract.Ensures(Contract.Result<Sort>() != null);

                return Sort.Create(Context, Native.Z3_get_array_sort_domain(Context.nCtx, NativeObject)); }
        }

        /// <summary>
        /// The range of the array sort.
        /// </summary>
        public Sort Range
        {
            get {
                Contract.Ensures(Contract.Result<Sort>() != null);

                return Sort.Create(Context, Native.Z3_get_array_sort_range(Context.nCtx, NativeObject)); }
        }

        #region Internal
        internal ArraySort(Context ctx, IntPtr obj) : base(ctx, obj) { Contract.Requires(ctx != null); }
        internal ArraySort(Context ctx, Sort domain, Sort range)
            : base(ctx, Native.Z3_mk_array_sort(ctx.nCtx, domain.NativeObject, range.NativeObject))
        {
            Contract.Requires(ctx != null);
            Contract.Requires(domain != null);
            Contract.Requires(range != null);
        }
        #endregion
    };

    /// <summary>
    /// Datatype sorts.
    /// </summary>
    [ContractVerification(true)]
    public class DatatypeSort : Sort
    {
        /// <summary>
        /// The number of constructors of the datatype sort.
        /// </summary>
        public uint NumConstructors
        {
            get { return Native.Z3_get_datatype_sort_num_constructors(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// The constructors.
        /// </summary>
        public FuncDecl[] Constructors
        {
            get
            {
                Contract.Ensures(Contract.Result<FuncDecl[]>() != null);

                uint n = NumConstructors;
                FuncDecl[] res = new FuncDecl[n];
                for (uint i = 0; i < n; i++)
                    res[i] = new FuncDecl(Context, Native.Z3_get_datatype_sort_constructor(Context.nCtx, NativeObject, i));
                return res;
            }
        }

        /// <summary>
        /// The recognizers.
        /// </summary>
        public FuncDecl[] Recognizers
        {
            get
            {
                Contract.Ensures(Contract.Result<FuncDecl[]>() != null);

                uint n = NumConstructors;
                FuncDecl[] res = new FuncDecl[n];
                for (uint i = 0; i < n; i++)
                    res[i] = new FuncDecl(Context, Native.Z3_get_datatype_sort_recognizer(Context.nCtx, NativeObject, i));
                return res;
            }
        }

        /// <summary>
        /// The constructor accessors.
        /// </summary>
        public FuncDecl[][] Accessors
        {
            get
            {
                Contract.Ensures(Contract.Result<FuncDecl[][]>() != null);

                uint n = NumConstructors;
                FuncDecl[][] res = new FuncDecl[n][];
                for (uint i = 0; i < n; i++)
                {
                    FuncDecl fd = new FuncDecl(Context, Native.Z3_get_datatype_sort_constructor(Context.nCtx, NativeObject, i));
                    uint ds = fd.DomainSize;
                    FuncDecl[] tmp = new FuncDecl[ds];
                    for (uint j = 0; j < ds; j++)
                        tmp[j] = new FuncDecl(Context, Native.Z3_get_datatype_sort_constructor_accessor(Context.nCtx, NativeObject, i, j));
                    res[i] = tmp;
                }
                return res;
            }
        }

        #region Internal
        internal DatatypeSort(Context ctx, IntPtr obj) : base(ctx, obj) { Contract.Requires(ctx != null); }

        internal DatatypeSort(Context ctx, Symbol name, Constructor[] constructors)
            : base(ctx, Native.Z3_mk_datatype(ctx.nCtx, name.NativeObject, (uint)constructors.Length, ArrayToNative(constructors)))
        {
            Contract.Requires(ctx != null);
            Contract.Requires(name != null);
            Contract.Requires(constructors != null);
        }
        #endregion
    };

    /// <summary>
    /// Uninterpreted Sorts
    /// </summary>
    public class UninterpretedSort : Sort
    {
        #region Internal
        internal UninterpretedSort(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }
        internal UninterpretedSort(Context ctx, Symbol s)
            : base(ctx, Native.Z3_mk_uninterpreted_sort(ctx.nCtx, s.NativeObject))
        {
            Contract.Requires(ctx != null);
            Contract.Requires(s != null);
        }
        #endregion
    }

    /// <summary>
    /// Tuple sorts.
    /// </summary>
    [ContractVerification(true)]
    public class TupleSort : Sort
    {
        /// <summary>
        /// The constructor function of the tuple.
        /// </summary>
        public FuncDecl MkDecl
        {
            get {
                Contract.Ensures(Contract.Result<FuncDecl>() != null);

                return new FuncDecl(Context, Native.Z3_get_tuple_sort_mk_decl(Context.nCtx, NativeObject)); }
        }

        /// <summary>
        /// The number of fields in the tuple.
        /// </summary>
        public uint NumFields
        {
            get { return Native.Z3_get_tuple_sort_num_fields(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// The field declarations.
        /// </summary>
        public FuncDecl[] FieldDecls
        {
            get
            {
                Contract.Ensures(Contract.Result<FuncDecl[]>() != null);

                uint n = NumFields;
                FuncDecl[] res = new FuncDecl[n];
                for (uint i = 0; i < n; i++)
                    res[i] = new FuncDecl(Context, Native.Z3_get_tuple_sort_field_decl(Context.nCtx, NativeObject, i));
                return res;
            }
        }

        #region Internal
        internal TupleSort(Context ctx, Symbol name, uint numFields, Symbol[] fieldNames, Sort[] fieldSorts)
            : base(ctx)
        {
            Contract.Requires(ctx != null);
            Contract.Requires(name != null);

            IntPtr t = IntPtr.Zero;
            NativeObject = Native.Z3_mk_tuple_sort(ctx.nCtx, name.NativeObject, numFields,
                                                   Symbol.ArrayToNative(fieldNames), AST.ArrayToNative(fieldSorts),
                                                   ref t, new IntPtr[numFields]);
        }
        #endregion
    };

    /// <summary>
    /// Enumeration sorts.
    /// </summary>
    [ContractVerification(true)]
    public class EnumSort : Sort
    {
        /// <summary>
        /// The function declarations of the constants in the enumeration.
        /// </summary>
        public FuncDecl[] ConstDecls
        {
            get {
                Contract.Ensures(Contract.Result<FuncDecl[]>() != null);

                return _constdecls; }
        }

        /// <summary>
        /// The constants in the enumeration.
        /// </summary>
        public Expr[] Consts
        {
            get {
                Contract.Ensures(Contract.Result<Expr[]>() != null);

                return _consts; }
        }

        /// <summary>
        /// The test predicates for the constants in the enumeration.
        /// </summary>
        public FuncDecl[] TesterDecls
        {
            get {
                Contract.Ensures(Contract.Result<FuncDecl[]>() != null);
                
                return _testerdecls;
            }
        }

        #region Object Invariant

        [ContractInvariantMethod]
        private void ObjectInvariant()
        {
            Contract.Invariant(this._constdecls != null);
            Contract.Invariant(this._testerdecls != null);
            Contract.Invariant(this._consts != null);
        }

        
        #endregion

        #region Internal
        readonly private FuncDecl[] _constdecls = null, _testerdecls = null;
        readonly private Expr[] _consts = null;

        internal EnumSort(Context ctx, Symbol name, Symbol[] enumNames)
            : base(ctx)
        {
            Contract.Requires(ctx != null);
            Contract.Requires(name != null);
            Contract.Requires(enumNames != null);

            int n = enumNames.Length;
            IntPtr[] n_constdecls = new IntPtr[n];
            IntPtr[] n_testers = new IntPtr[n];
            NativeObject = Native.Z3_mk_enumeration_sort(ctx.nCtx, name.NativeObject, (uint)n,
                                                         Symbol.ArrayToNative(enumNames), n_constdecls, n_testers);
            _constdecls = new FuncDecl[n];            
            for (uint i = 0; i < n; i++)            
                _constdecls[i] = new FuncDecl(ctx, n_constdecls[i]);
            _testerdecls = new FuncDecl[n];
            for (uint i = 0; i < n; i++)
                _testerdecls[i] = new FuncDecl(ctx, n_testers[i]);
            _consts = new Expr[n];
            for (uint i = 0; i < n; i++)
                _consts[i] = ctx.MkApp(_constdecls[i]);
        }
        #endregion
    };

    /// <summary>
    /// List sorts.
    /// </summary>
    [ContractVerification(true)]
    public class ListSort : Sort
    {
        /// <summary>
        /// The declaration of the nil function of this list sort.
        /// </summary>
        public FuncDecl NilDecl { get {
            Contract.Ensures(Contract.Result<FuncDecl>() != null);
            return nilDecl; } }

        /// <summary>
        /// The empty list.
        /// </summary>
        public Expr Nil
        {
            get
            {
                Contract.Ensures(Contract.Result<Expr>() != null);
                return nilConst;
            }
        }

        /// <summary>
        /// The declaration of the isNil function of this list sort.
        /// </summary>
        public FuncDecl IsNilDecl
        {
            get
            {
                Contract.Ensures(Contract.Result<FuncDecl>() != null);
                return isNilDecl;
            }
        }

        /// <summary>
        /// The declaration of the cons function of this list sort.
        /// </summary>
        public FuncDecl ConsDecl
        {
            get
            {
                Contract.Ensures(Contract.Result<FuncDecl>() != null);
                return consDecl;
            }
        }

        /// <summary>
        /// The declaration of the isCons function of this list sort.
        /// </summary>
        /// 
        public FuncDecl IsConsDecl
        {
            get
            {
                Contract.Ensures(Contract.Result<FuncDecl>() != null);
                return isConsDecl;
            }
        }

        /// <summary>
        /// The declaration of the head function of this list sort.
        /// </summary>
        public FuncDecl HeadDecl
        {
            get
            {
                Contract.Ensures(Contract.Result<FuncDecl>() != null);
                return headDecl;
            }
        }

        /// <summary>
        /// The declaration of the tail function of this list sort.
        /// </summary>
        public FuncDecl TailDecl
        {
            get
            {
                Contract.Ensures(Contract.Result<FuncDecl>() != null);
                return tailDecl;
            }
        }

        #region Object Invariant

        [ContractInvariantMethod]
        private void ObjectInvariant()
        {
            Contract.Invariant(nilConst != null);
            Contract.Invariant(nilDecl != null);
            Contract.Invariant(isNilDecl != null);
            Contract.Invariant(consDecl != null);
            Contract.Invariant(isConsDecl != null);
            Contract.Invariant(headDecl != null);
            Contract.Invariant(tailDecl != null);
        }

        
        #endregion

        #region Internal
        readonly private FuncDecl nilDecl, isNilDecl, consDecl, isConsDecl, headDecl, tailDecl;
        readonly private Expr nilConst;

        internal ListSort(Context ctx, Symbol name, Sort elemSort)
            : base(ctx)
        {
            Contract.Requires(ctx != null);
            Contract.Requires(name != null);
            Contract.Requires(elemSort != null);

            IntPtr inil = IntPtr.Zero,
                   iisnil = IntPtr.Zero,
                   icons = IntPtr.Zero,
                   iiscons = IntPtr.Zero,
                   ihead = IntPtr.Zero,
                   itail = IntPtr.Zero;

            NativeObject = Native.Z3_mk_list_sort(ctx.nCtx, name.NativeObject, elemSort.NativeObject,
                                                  ref inil, ref iisnil, ref icons, ref iiscons, ref ihead, ref itail);
            nilDecl = new FuncDecl(ctx, inil);
            isNilDecl = new FuncDecl(ctx, iisnil);
            consDecl = new FuncDecl(ctx, icons);
            isConsDecl = new FuncDecl(ctx, iiscons);
            headDecl = new FuncDecl(ctx, ihead);
            tailDecl = new FuncDecl(ctx, itail);
            nilConst = ctx.MkConst(nilDecl);
        }
        #endregion
    };

    /// <summary>
    /// Relation sorts.
    /// </summary>
    [ContractVerification(true)]
    public class RelationSort : Sort
    {
        /// <summary>
        /// The arity of the relation sort.
        /// </summary>
        public uint Arity
        {
            get { return Native.Z3_get_relation_arity(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// The sorts of the columns of the relation sort.
        /// </summary>
        public Sort[] ColumnSorts
        {
            get
            {
                Contract.Ensures(Contract.Result<Sort[]>() != null);

                if (m_columnSorts != null)
                    return m_columnSorts;

                uint n = Arity;
                Sort[] res = new Sort[n];
                for (uint i = 0; i < n; i++)
                    res[i] = Sort.Create(Context, Native.Z3_get_relation_column(Context.nCtx, NativeObject, i));
                return res;
            }
        }

        #region Internal
        private Sort[] m_columnSorts = null;

        internal RelationSort(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }        
        #endregion
    }

    /// <summary>
    /// Finite domain sorts.
    /// </summary>
    [ContractVerification(true)]
    public class FiniteDomainSort : Sort
    {
        /// <summary>
        /// The size of the finite domain sort.
        /// </summary>
        public ulong Size
        {
            get { ulong res = 0; Native.Z3_get_finite_domain_sort_size(Context.nCtx, NativeObject, ref res); return res; }
        }

        #region Internal
        internal FiniteDomainSort(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }
        internal FiniteDomainSort(Context ctx, Symbol name, ulong size)
            : base(ctx, Native.Z3_mk_finite_domain_sort(ctx.nCtx, name.NativeObject, size))
        {
            Contract.Requires(ctx != null);
            Contract.Requires(name != null);

        }
        #endregion
    }

    /// <summary>
    /// Set sorts.
    /// </summary>
    [ContractVerification(true)]
    public class SetSort : Sort
    {
        #region Internal
        internal SetSort(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }
        internal SetSort(Context ctx, Sort ty)
            : base(ctx, Native.Z3_mk_set_sort(ctx.nCtx, ty.NativeObject))
        {
            Contract.Requires(ctx != null);
            Contract.Requires(ty != null);
        }
        #endregion
    }
}
