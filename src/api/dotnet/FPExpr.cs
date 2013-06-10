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
    public class FPExpr : Expr
    {
        #region Internal        
        internal protected FPExpr(Context ctx)
            : base(ctx)
        {
            Contract.Requires(ctx != null);
        }
        internal FPExpr(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }
        #endregion
    }
}
