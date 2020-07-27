/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    FPExpr.cs

Abstract:

    Z3 Managed API: Floating Point Expressions

Author:

    Christoph Wintersteiger (cwinter) 2013-06-10

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
    /// FloatingPoint Expressions
    /// </summary>
    public class FPExpr : Expr
    {
        /// <summary>
        /// The number of exponent bits.
        /// </summary>
        public uint EBits { get { return ((FPSort)Sort).EBits; } }

        /// <summary>
        /// The number of significand bits.
        /// </summary>
        public uint SBits { get { return ((FPSort)Sort).SBits; } }

        #region Internal
        /// <summary> Constructor for FPExpr </summary>
        internal FPExpr(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Debug.Assert(ctx != null);
        }
        #endregion
    }
}
