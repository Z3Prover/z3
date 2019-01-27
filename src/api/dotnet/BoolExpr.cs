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
using System.Diagnostics;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;


namespace Microsoft.Z3
{
    /// <summary>
    /// Boolean expressions
    /// </summary>
    public class BoolExpr : Expr
    {
        #region Internal
        /// <summary> Constructor for BoolExpr </summary>
        internal BoolExpr(Context ctx, IntPtr obj) : base(ctx, obj) { Debug.Assert(ctx != null); }
        #endregion

        #region Operators
        /// <summary> Disjunction of Boolean expressions </summary>
        public static BoolExpr operator|(BoolExpr a, BoolExpr b) { return a.Context.MkOr(a, b); }

        /// <summary> Conjunction of Boolean expressions </summary>
        public static BoolExpr operator &(BoolExpr a, BoolExpr b) { return a.Context.MkAnd(a, b); }
       
        /// <summary> Xor of Boolean expressions </summary>
        public static BoolExpr operator ^(BoolExpr a, BoolExpr b) { return a.Context.MkXor(a, b); }
       
        /// <summary> Negation </summary>
        public static BoolExpr operator !(BoolExpr a) { return a.Context.MkNot(a); }

        #endregion
    }
}
