﻿/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    SeqSort.cs

Abstract:

    Z3 Managed API: Sequence Sorts

Author:

    Christoph Wintersteiger (cwinter) 2012-11-23

Notes:
    
--*/

using System.Diagnostics;
using System;

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
            Debug.Assert(ctx != null);
        }
        #endregion
    }
}
