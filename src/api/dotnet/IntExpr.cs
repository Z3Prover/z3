/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    IntExpr.cs

Abstract:

    Z3 Managed API: Int Expressions

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
    /// Int expressions
    /// </summary>
    public class IntExpr : ArithExpr
    {
        #region Internal
        /// <summary> Constructor for IntExpr </summary>
        internal IntExpr(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }
        #endregion
    }
}
