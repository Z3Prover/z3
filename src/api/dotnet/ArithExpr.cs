/*++
Copyright (<c>) 2012 Microsoft Corporation

Module Name:

    ArithExpr.cs

Abstract:

    Z3 Managed API: Arith Expressions

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
    /// Arithmetic expressions (int/real)
    /// </summary>
    public class ArithExpr : Expr
    {
        #region Internal
        /// <summary> Constructor for ArithExpr </summary>
        internal ArithExpr(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }
        #endregion
    }
}
