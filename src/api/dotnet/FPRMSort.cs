/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    FPRMSort.cs

Abstract:

    Z3 Managed API: Rounding Mode Sort

Author:

    Christoph Wintersteiger (cwinter) 2013-06-10

Notes:
    
--*/

using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// The FloatingPoint RoundingMode sort
    /// </summary>
    public class FPRMSort : Sort
    {
        #region Internal
        internal FPRMSort(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }
        internal FPRMSort(Context ctx)
            : base(ctx, Native.Z3_mk_fpa_rounding_mode_sort(ctx.nCtx))
        {
            Contract.Requires(ctx != null);
        }
        #endregion
    }
}