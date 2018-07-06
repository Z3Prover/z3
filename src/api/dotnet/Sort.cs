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
	            0 != Native.Z3_is_eq_sort(a.Context.nCtx, a.NativeObject, b.NativeObject));
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
            get
            {
                Contract.Ensures(Contract.Result<Symbol>() != null);
                return Symbol.Create(Context, Native.Z3_get_sort_name(Context.nCtx, NativeObject));
            }
        }

        /// <summary>
        /// A string representation of the sort.
        /// </summary>
        public override string ToString()
        {
            return Native.Z3_sort_to_string(Context.nCtx, NativeObject);
        }

        /// <summary>
        /// Translates (copies) the sort to the Context <paramref name="ctx"/>.
        /// </summary>
        /// <param name="ctx">A context</param>
        /// <returns>A copy of the sort which is associated with <paramref name="ctx"/></returns>
        new public Sort Translate(Context ctx)
        {
            return (Sort)base.Translate(ctx);
        }

        #region Internal
        /// <summary>
        /// Sort constructor
        /// </summary>
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
                case Z3_sort_kind.Z3_FLOATING_POINT_SORT: return new FPSort(ctx, obj);
                case Z3_sort_kind.Z3_ROUNDING_MODE_SORT: return new FPRMSort(ctx, obj);
                case Z3_sort_kind.Z3_SEQ_SORT: return new SeqSort(ctx, obj);
                case Z3_sort_kind.Z3_RE_SORT: return new ReSort(ctx, obj);
                default:
                    throw new Z3Exception("Unknown sort kind");
            }
        }
        #endregion
    }
}
