/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    ReSort.cs

Abstract:

    Z3 Managed API: Regular expression Sorts

Author:

    Christoph Wintersteiger (cwinter) 2012-11-23

Notes:
    
--*/

using System.Diagnostics;
using System;

namespace Microsoft.Z3
{
    /// <summary>
    ///  A regular expression sort
    /// </summary>
    public class ReSort : Sort
    {
        #region Internal
        internal ReSort(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Debug.Assert(ctx != null);
        }
        internal ReSort(Context ctx)
            : base(ctx, Native.Z3_mk_int_sort(ctx.nCtx))
        {
            Debug.Assert(ctx != null);
        }
        #endregion
    }
}
