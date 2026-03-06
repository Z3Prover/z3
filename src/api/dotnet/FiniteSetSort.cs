/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    FiniteSetSort.cs

Abstract:

    Z3 Managed API: Finite Set Sorts

Author:

    GitHub Copilot

Notes:
    
--*/

using System.Diagnostics;
using System;

namespace Microsoft.Z3
{
    /// <summary>
    /// Finite set sorts.
    /// </summary>
    public class FiniteSetSort : Sort
    {
        #region Internal
        internal FiniteSetSort(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Debug.Assert(ctx != null);
        }

        internal FiniteSetSort(Context ctx, Sort elemSort)
            : base(ctx, Native.Z3_mk_finite_set_sort(ctx.nCtx, elemSort.NativeObject))
        {
            Debug.Assert(ctx != null);
            Debug.Assert(elemSort != null);
        }
        #endregion

        /// <summary>
        /// Get the element sort (basis) of this finite set sort.
        /// </summary>
        public Sort Basis
        {
            get { return Sort.Create(Context, Native.Z3_get_finite_set_sort_basis(Context.nCtx, NativeObject)); }
        }
    }
}
