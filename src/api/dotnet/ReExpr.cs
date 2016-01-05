/*++
Copyright (<c>) 2016 Microsoft Corporation

Module Name:

    ReExpr.cs

Abstract:

    Z3 Managed API: Regular Expressions

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
    /// Regular expression expressions
    /// </summary>
    public class ReExpr : Expr
    {
        #region Internal
        /// <summary> Constructor for ReExpr </summary>
        internal ReExpr(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }
        #endregion
    }
}
