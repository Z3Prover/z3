/*++
Copyright (<c>) 2012 Microsoft Corporation

Module Name:

    RealExpr.cs

Abstract:

    Z3 Managed API: Real Expressions

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
    /// Real expressions
    /// </summary>
    public class RealExpr : ArithExpr
    {
        #region Internal
        /// <summary> Constructor for RealExpr </summary>
        internal RealExpr(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Debug.Assert(ctx != null);
        }
        #endregion
    }
}
