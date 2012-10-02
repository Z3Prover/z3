/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    Pattern.cs

Abstract:

    Z3 Managed API: Patterns

Author:

    Christoph Wintersteiger (cwinter) 2012-03-16

Notes:
    
--*/

using System;
using System.Runtime.InteropServices;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// Patterns comprise a list of terms. The list should be
    /// non-empty.  If the list comprises of more than one term, it is
    /// also called a multi-pattern.
    /// </summary>
    [ContractVerification(true)]
    public class Pattern : AST
    {
        /// <summary>
        /// The number of terms in the pattern.
        /// </summary>
        public uint NumTerms
        {
            get { return Native.Z3_get_pattern_num_terms(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// The terms in the pattern.
        /// </summary>
        public Expr[] Terms
        {
            get
            {
                Contract.Ensures(Contract.Result<Expr[]>() != null);

                uint n = NumTerms;
                Expr[] res = new Expr[n];
                for (uint i = 0; i < n; i++)
                    res[i] = Expr.Create(Context, Native.Z3_get_pattern(Context.nCtx, NativeObject, i));
                return res;
            }
        }

        /// <summary>
        /// A string representation of the pattern.
        /// </summary>
        public override string ToString()
        {
            return Native.Z3_pattern_to_string(Context.nCtx, NativeObject);
        }

        #region Internal
        internal Pattern(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }
        #endregion
    }
}
