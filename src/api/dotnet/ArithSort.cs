﻿/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    ArithSort.cs

Abstract:

    Z3 Managed API: Arith Sorts

Author:

    Christoph Wintersteiger (cwinter) 2012-11-23

Notes:
    
--*/

using System.Diagnostics;
using System;

namespace Microsoft.Z3
{
    /// <summary>
    /// An arithmetic sort, i.e., Int or Real.
    /// </summary>
    public class ArithSort : Sort
    {
        #region Internal
        internal ArithSort(Context ctx, IntPtr obj) : base(ctx, obj) { Debug.Assert(ctx != null); }
        #endregion
    };
}
