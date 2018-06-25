/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    AlgebraicNum.cs

Abstract:

    Z3 Managed API: Algebraic Numerals

Author:

    Christoph Wintersteiger (cwinter) 2012-03-20

Notes:
    
--*/
using System;
using System.Diagnostics.Contracts;

#if !FRAMEWORK_LT_4
using System.Numerics;
#endif

namespace Microsoft.Z3
{
    /// <summary>
    /// Algebraic numbers
    /// </summary>
    [ContractVerification(true)]
    public class AlgebraicNum : ArithExpr
    {
        /// <summary>
        /// Return a upper bound for a given real algebraic number. 
        /// The interval isolating the number is smaller than 1/10^<paramref name="precision"/>.    
        /// <seealso cref="Expr.IsAlgebraicNumber"/>   
        /// </summary>
        /// <param name="precision">the precision of the result</param>
        /// <returns>A numeral Expr of sort Real</returns>
        public RatNum ToUpper(uint precision)
        {
            Contract.Ensures(Contract.Result<RatNum>() != null);

            return new RatNum(Context, Native.Z3_get_algebraic_number_upper(Context.nCtx, NativeObject, precision));
        }

        /// <summary>
        /// Return a lower bound for the given real algebraic number. 
        /// The interval isolating the number is smaller than 1/10^<paramref name="precision"/>.    
        /// <seealso cref="Expr.IsAlgebraicNumber"/>
        /// </summary>
        /// <param name="precision"></param>
        /// <returns>A numeral Expr of sort Real</returns>
        public RatNum ToLower(uint precision)
        {
            Contract.Ensures(Contract.Result<RatNum>() != null);

            return new RatNum(Context, Native.Z3_get_algebraic_number_lower(Context.nCtx, NativeObject, precision));
        }

        /// <summary>
        /// Returns a string representation in decimal notation.
        /// </summary>
        /// <remarks>The result has at most <paramref name="precision"/> decimal places.</remarks>    
        public string ToDecimal(uint precision)
        {
            Contract.Ensures(Contract.Result<string>() != null);

            return Native.Z3_get_numeral_decimal_string(Context.nCtx, NativeObject, precision);
        }

        #region Internal
        internal AlgebraicNum(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }
        #endregion
    }
}
