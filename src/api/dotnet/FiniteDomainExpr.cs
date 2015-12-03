/*++
Copyright (<c>) 2012 Microsoft Corporation

Module Name:

    FiniteDomainExpr.cs

Abstract:

    Z3 Managed API: Finite-domain Expressions

Author:

    Christoph Wintersteiger (cwinter) 2015-12-02

Notes:

--*/
using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// Finite-domain expressions
    /// </summary>
    public class FiniteDomainExpr : Expr
    {
        #region Internal
        /// <summary> Constructor for DatatypeExpr </summary>
        internal FiniteDomainExpr(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }
        #endregion
    }
}
