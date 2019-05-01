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
using System.Diagnostics;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;


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
            Debug.Assert(ctx != null);
        }
        #endregion

        /// <summary> Access the nth element of a sequence </summary>
        public Expr this[Expr index] 
        {
            get { return Context.MkNth(this, index); }
        }
    }
}
