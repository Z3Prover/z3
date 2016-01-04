/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    SeqSort.cs

Abstract:

    Z3 Managed API: Sequence Sorts

Author:

    Christoph Wintersteiger (cwinter) 2012-11-23

Notes:
    
--*/

using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    ///  A Sequence sort
    /// </summary>
    public class SeqSort : Sort
    {
        #region Internal
        internal SeqSort(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }
        internal SeqSort(Context ctx)
            : base(ctx, Native.Z3_mk_int_sort(ctx.nCtx))
        {
            Contract.Requires(ctx != null);
        }
        #endregion
    }
}
