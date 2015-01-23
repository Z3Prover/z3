/*++
Copyright (<c>) 2012 Microsoft Corporation

Module Name:

    DatatypeExpr.cs

Abstract:

    Z3 Managed API: Datatype Expressions

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
    /// Datatype expressions
    /// </summary>
    public class DatatypeExpr : Expr
    {
        #region Internal
        /// <summary> Constructor for DatatypeExpr </summary>
        internal DatatypeExpr(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }
        #endregion
    }
}
