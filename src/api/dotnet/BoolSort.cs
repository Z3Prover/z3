/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    BoolSort.cs

Abstract:

    Z3 Managed API: Bool Sorts

Author:

    Christoph Wintersteiger (cwinter) 2012-11-23

Notes:
    
--*/

using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
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
}
