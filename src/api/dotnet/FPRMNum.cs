/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    FPRMNum.cs

Abstract:

    Z3 Managed API: Floating Point Rounding Mode Numerals

Author:

    Christoph Wintersteiger (cwinter) 2013-06-10

Notes:
    
--*/
using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// FloatingPoint RoundingMode Numerals
    /// </summary>
    [ContractVerification(true)]
    public class FPRMNum : FPRMExpr
    {

        #region Internal
        internal FPRMNum(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }
        #endregion

        /// <summary>
        /// Returns a string representation of the numeral.
        /// </summary>        
        public override string ToString()
        {
            return Native.Z3_get_numeral_string(Context.nCtx, NativeObject);
        }
    }
}
