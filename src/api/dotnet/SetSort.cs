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

using System.Diagnostics;
using System;

namespace Microsoft.Z3
{
    /// <summary>
    /// Set sorts.
    /// </summary>
    public class SetSort : Sort
    {
        #region Internal
        internal SetSort(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Debug.Assert(ctx != null);
        }
        internal SetSort(Context ctx, Sort ty)
            : base(ctx, Native.Z3_mk_set_sort(ctx.nCtx, ty.NativeObject))
        {
            Debug.Assert(ctx != null);
            Debug.Assert(ty != null);
        }
        #endregion
    }
}
