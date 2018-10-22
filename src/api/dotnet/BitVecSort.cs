/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    BitVecSort.cs

Abstract:

    Z3 Managed API: BitVec Sorts

Author:

    Christoph Wintersteiger (cwinter) 2012-11-23

Notes:
    
--*/

using System.Diagnostics;
using System;

namespace Microsoft.Z3
{
    /// <summary>
    /// Bit-vector sorts.
    /// </summary>
    public class BitVecSort : Sort
    {
        /// <summary>
        /// The size of the bit-vector sort.
        /// </summary>
        public uint Size
        {
            get { return Native.Z3_get_bv_sort_size(Context.nCtx, NativeObject); }
        }

        #region Internal
        internal BitVecSort(Context ctx, IntPtr obj) : base(ctx, obj) { Debug.Assert(ctx != null); }
        #endregion
    };
}
