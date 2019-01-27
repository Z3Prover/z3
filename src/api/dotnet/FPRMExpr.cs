/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    FPRMExpr.cs

Abstract:

    Z3 Managed API: Floating Point Expressions over Rounding Modes

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
    /// FloatingPoint RoundingMode Expressions
    /// </summary>
    public class FPRMExpr : Expr
    {
        #region Internal
        /// <summary> Constructor for FPRMExpr </summary>
        internal FPRMExpr(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Debug.Assert(ctx != null);
        }
        #endregion
    }
}
