/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    IntNum.cs

Abstract:

    Z3 Managed API: Int Numerals

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
    /// Rational Numerals
    /// </summary>
    [ContractVerification(true)]
    public class RatNum : RealExpr
    {
        /// <summary>
        /// The numerator of a rational numeral.
        /// </summary>
        public IntNum Numerator
        {
            get
            {
                Contract.Ensures(Contract.Result<IntNum>() != null);

                return new IntNum(Context, Native.Z3_get_numerator(Context.nCtx, NativeObject));
            }
        }

        /// <summary>
        /// The denominator of a rational numeral.
        /// </summary>
        public IntNum Denominator
        {
            get
            {
                Contract.Ensures(Contract.Result<IntNum>() != null);

                return new IntNum(Context, Native.Z3_get_denominator(Context.nCtx, NativeObject));
            }
        }

#if !FRAMEWORK_LT_4
        /// <summary>
        /// Converts the numerator of the rational to a BigInteger
        /// </summary>
        public BigInteger BigIntNumerator
        {
            get
            {
                IntNum n = Numerator;
                return BigInteger.Parse(n.ToString());
            }
        }

        /// <summary>
        /// Converts the denominator of the rational to a BigInteger
        /// </summary>
        public BigInteger BigIntDenominator
        {
            get
            {
                IntNum n = Denominator;
                return BigInteger.Parse(n.ToString());
            }
        }
#endif

        /// <summary>
        /// Returns a string representation in decimal notation.
        /// </summary>
        /// <remarks>The result has at most <paramref name="precision"/> decimal places.</remarks>    
        public string ToDecimalString(uint precision)
        {
            return Native.Z3_get_numeral_decimal_string(Context.nCtx, NativeObject, precision);
        }

        /// <summary>
        /// Returns a string representation of the numeral.
        /// </summary>        
        public override string ToString()
        {
            return Native.Z3_get_numeral_string(Context.nCtx, NativeObject);
        }

        #region Internal
        internal RatNum(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }
        #endregion
    }
}
