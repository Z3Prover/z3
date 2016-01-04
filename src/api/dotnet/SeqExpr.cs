/*++
Copyright (<c>) 2016 Microsoft Corporation

Module Name:

    SeqExpr.cs

Abstract:

    Z3 Managed API: Sequence Expressions

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
    /// Sequence expressions
    /// </summary>
    public class SeqExpr : Expr
    {
        #region Internal
        /// <summary> Constructor for SeqExpr </summary>
        internal SeqExpr(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }
        #endregion
    }
}
