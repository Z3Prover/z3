/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    TypeVarSort.cs

Abstract:

    Z3 Managed API: Type Variable Sorts

Author:

    Christoph Wintersteiger (cwinter) 2012-11-23

Notes:
    
--*/

using System;
using System.Diagnostics;

namespace Microsoft.Z3
{
    /// <summary>
    /// Type variable sorts for use in polymorphic functions and datatypes.
    /// </summary>
    public class TypeVarSort : Sort
    {
        #region Internal
        internal TypeVarSort(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Debug.Assert(ctx != null);
        }
        internal TypeVarSort(Context ctx, Symbol s)
            : base(ctx, Native.Z3_mk_type_variable(ctx.nCtx, s.NativeObject))
        {
            Debug.Assert(ctx != null);
            Debug.Assert(s != null);
        }
        #endregion
    }
}
