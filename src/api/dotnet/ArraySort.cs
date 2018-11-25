/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    ArraySort.cs

Abstract:

    Z3 Managed API: Array Sorts

Author:

    Christoph Wintersteiger (cwinter) 2012-11-23

Notes:
    
--*/

using System.Diagnostics;
using System;

namespace Microsoft.Z3
{
    /// <summary>
    /// Array sorts.
    /// </summary>
    public class ArraySort : Sort
    {
        /// <summary>
        /// The domain of the array sort.
        /// </summary>
        public Sort Domain
        {
            get
            {

                return Sort.Create(Context, Native.Z3_get_array_sort_domain(Context.nCtx, NativeObject));
            }
        }

        /// <summary>
        /// The range of the array sort.
        /// </summary>
        public Sort Range
        {
            get
            {

                return Sort.Create(Context, Native.Z3_get_array_sort_range(Context.nCtx, NativeObject));
            }
        }

        #region Internal
        internal ArraySort(Context ctx, IntPtr obj) : base(ctx, obj) { Debug.Assert(ctx != null); }
        internal ArraySort(Context ctx, Sort domain, Sort range)
            : base(ctx, Native.Z3_mk_array_sort(ctx.nCtx, domain.NativeObject, range.NativeObject))
        {
            Debug.Assert(ctx != null);
            Debug.Assert(domain != null);
            Debug.Assert(range != null);
        }
        internal ArraySort(Context ctx, Sort[] domain, Sort range)
            : base(ctx, Native.Z3_mk_array_sort_n(ctx.nCtx, (uint)domain.Length, AST.ArrayToNative(domain), range.NativeObject))
        {
            Debug.Assert(ctx != null);
            Debug.Assert(domain != null);
            Debug.Assert(range != null);
        }
        #endregion
    };

}
