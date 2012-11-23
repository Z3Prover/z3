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
using System.Diagnostics.Contracts;

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
            Contract.Requires(ctx != null);
        }
        internal UninterpretedSort(Context ctx, Symbol s)
            : base(ctx, Native.Z3_mk_uninterpreted_sort(ctx.nCtx, s.NativeObject))
        {
            Contract.Requires(ctx != null);
            Contract.Requires(s != null);
        }
        #endregion
    }
}
