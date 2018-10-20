/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    UninterpretedSort.cs

Abstract:

    Z3 Managed API: Uninterpreted Sorts

Author:

    Christoph Wintersteiger (cwinter) 2012-11-23

Notes:
    
--*/

using System;
using System.Diagnostics;

namespace Microsoft.Z3
{
    /// <summary>
    /// Uninterpreted Sorts
    /// </summary>
    public class UninterpretedSort : Sort
    {
        #region Internal
        internal UninterpretedSort(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Debug.Assert(ctx != null);
        }
        internal UninterpretedSort(Context ctx, Symbol s)
            : base(ctx, Native.Z3_mk_uninterpreted_sort(ctx.nCtx, s.NativeObject))
        {
            Debug.Assert(ctx != null);
            Debug.Assert(s != null);
        }
        #endregion
    }
}
