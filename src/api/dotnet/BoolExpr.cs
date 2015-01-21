/*++
Copyright (<c>) 2012 Microsoft Corporation

Module Name:

    BoolExpr.cs

Abstract:

    Z3 Managed API: Boolean Expressions

Author:

    Christoph Wintersteiger (cwinter) 2012-11-23

Notes:
    
--*/
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// Boolean expressions
    /// </summary>
    public class BoolExpr : Expr
    {
        #region Internal
        /// <summary> Constructor for BoolExpr </summary>
        internal BoolExpr(Context ctx, IntPtr obj) : base(ctx, obj) { Contract.Requires(ctx != null); }
        #endregion
    }
}
