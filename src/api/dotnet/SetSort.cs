/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    SetSort.cs

Abstract:

    Z3 Managed API: Set Sorts

Author:

    Christoph Wintersteiger (cwinter) 2012-11-23

Notes:
    
--*/

using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
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
