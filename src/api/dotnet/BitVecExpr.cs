/*++
Copyright (<c>) 2012 Microsoft Corporation

Module Name:

    BitVecExpr.cs

Abstract:

    Z3 Managed API: BitVec Expressions

Author:

    Christoph Wintersteiger (cwinter) 2012-11-23

Notes:
    
--*/
using System.Diagnostics;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;


namespace Microsoft.Z3
{
    /// <summary>
    /// Bit-vector expressions
    /// </summary>
    public class BitVecExpr : Expr
    {

        /// <summary>
        /// The size of the sort of a bit-vector term.
        /// </summary>
        public uint SortSize
        {
            get { return ((BitVecSort)Sort).Size; }
        }

        #region Internal
        /// <summary> Constructor for BitVecExpr </summary>
        internal BitVecExpr(Context ctx, IntPtr obj) : base(ctx, obj) { Debug.Assert(ctx != null); }
        #endregion
    }
}
