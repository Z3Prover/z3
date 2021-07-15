/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    CharSort.cs

Abstract:

    Z3 Managed API: Character Sorts

Author:

    Christoph Wintersteiger (cwinter) 2012-11-23

Notes:
    
--*/

using System.Diagnostics;
using System;

namespace Microsoft.Z3
{
    /// <summary>
    ///  A Character sort
    /// </summary>
    public class CharSort : Sort
    {
        #region Internal
        internal CharSort(Context ctx, IntPtr obj) : base(ctx, obj) { Debug.Assert(ctx != null); }
        internal CharSort(Context ctx) : base(ctx, Native.Z3_mk_char_sort(ctx.nCtx)) { Debug.Assert(ctx != null); }
        #endregion
    }
}
