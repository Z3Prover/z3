/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    IntSort.cs

Abstract:

    Z3 Managed API: Int Sorts

Author:

    Christoph Wintersteiger (cwinter) 2012-11-23

Notes:
    
--*/

using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
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
}
