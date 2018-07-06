/*++
Copyright (<c>) 2012 Microsoft Corporation

Module Name:

    ArrayExpr.cs

Abstract:

    Z3 Managed API: Array Expressions

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
    /// Array expressions
    /// </summary>
    public class ArrayExpr : Expr
    {
        #region Internal
        /// <summary> Constructor for ArrayExpr </summary>
        internal ArrayExpr(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }
        #endregion	
    }
}
