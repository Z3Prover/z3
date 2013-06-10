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
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// Floating Point Expressions
    /// </summary>
    public class FPRMExpr : Expr
    {
        #region Internal
        internal protected FPRMExpr(Context ctx)
            : base(ctx)
        {
            Contract.Requires(ctx != null);
        }
        internal FPRMExpr(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }
        #endregion
    }
}
