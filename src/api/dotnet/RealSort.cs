/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    RealSort.cs

Abstract:

    Z3 Managed API: Real Sorts

Author:

    Christoph Wintersteiger (cwinter) 2012-11-23

Notes:
    
--*/

using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
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
}
