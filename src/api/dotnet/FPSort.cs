/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    FPSort.cs

Abstract:

    Z3 Managed API: Floating Point Sorts

Author:

    Christoph Wintersteiger (cwinter) 2013-06-10

Notes:
    
--*/

using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    ///  A floating point sort
    /// </summary>
    public class FPSort : Sort
    {
        #region Internal
        internal FPSort(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }
        internal FPSort(Context ctx, uint ebits, uint sbits)
            : base(ctx, Native.Z3_mk_fpa_sort(ctx.nCtx, ebits, sbits))
        {
            Contract.Requires(ctx != null);
        }
        #endregion
    }
}
