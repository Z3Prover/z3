/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    Numeral.cs

Abstract:

    Z3 Managed API: Numerals

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
    /// Integer Numerals
    /// </summary>
    [ContractVerification(true)]
    public class IntNum : IntExpr
    {

        #region Internal
        internal IntNum(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }
        #endregion


        /// <summary>
        /// Retrieve the 64-bit unsigned integer value.
        /// </summary>
        public UInt64 UInt64
        {
            get
            {
                UInt64 res = 0;
                if (Native.Z3_get_numeral_uint64(Context.nCtx, NativeObject, ref res) == 0)
                    throw new Z3Exception("Numeral is not a 64 bit unsigned");
                return res;
            }
        }

        /// <summary>
        /// Retrieve the int value.
        /// </summary>
        public int Int
        {
            get
            {
                int res = 0;
                if (Native.Z3_get_numeral_int(Context.nCtx, NativeObject, ref res) == 0)
                    throw new Z3Exception("Numeral is not an int");
                return res;
            }
        }

        /// <summary>
        /// Retrieve the 64-bit int value.
        /// </summary>
        public Int64 Int64
        {
            get
            {
                Int64 res = 0;
                if (Native.Z3_get_numeral_int64(Context.nCtx, NativeObject, ref res) == 0)
                    throw new Z3Exception("Numeral is not an int64");
                return res;
            }
        }

        /// <summary>
        /// Retrieve the int value.
        /// </summary>
        public uint UInt
        {
            get
            {
                uint res = 0;
                if (Native.Z3_get_numeral_uint(Context.nCtx, NativeObject, ref res) == 0)
                    throw new Z3Exception("Numeral is not a uint");
                return res;
            }
        }

#if !FRAMEWORK_LT_4
        /// <summary>
        /// Retrieve the BigInteger value.
        /// </summary>
        public BigInteger BigInteger
        {
            get
            {  
                return BigInteger.Parse(this.ToString());
            }
        }
#endif

        /// <summary>
        /// Returns a string representation of the numeral.
        /// </summary>        
        public override string ToString()
        {
            return Native.Z3_get_numeral_string(Context.nCtx, NativeObject);
        }
    }

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
            get {
                Contract.Ensures(Contract.Result<IntNum>() != null);

                return new IntNum(Context, Native.Z3_get_numerator(Context.nCtx, NativeObject)); }
        }

        /// <summary>
        /// The denominator of a rational numeral.
        /// </summary>
        public IntNum Denominator
        {
            get {
                Contract.Ensures(Contract.Result<IntNum>() != null);

                return new IntNum(Context, Native.Z3_get_denominator(Context.nCtx, NativeObject)); }
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


    /// <summary>
    /// Bit-vector numerals
    /// </summary>
    [ContractVerification(true)]
    public class BitVecNum : BitVecExpr
    {
        /// <summary>
        /// Retrieve the 64-bit unsigned integer value.
        /// </summary>
        public UInt64 UInt64
        {
            get
            {
                UInt64 res = 0;
                if (Native.Z3_get_numeral_uint64(Context.nCtx, NativeObject, ref res) == 0)
                    throw new Z3Exception("Numeral is not a 64 bit unsigned");
                return res;
            }
        }

        /// <summary>
        /// Retrieve the int value.
        /// </summary>
        public int Int
        {
            get
            {
                int res = 0;
                if (Native.Z3_get_numeral_int(Context.nCtx, NativeObject, ref res) == 0)
                    throw new Z3Exception("Numeral is not an int");
                return res;
            }
        }

        /// <summary>
        /// Retrieve the 64-bit int value.
        /// </summary>
        public Int64 Int64
        {
            get
            {
                Int64 res = 0;
                if (Native.Z3_get_numeral_int64(Context.nCtx, NativeObject, ref res) == 0)
                    throw new Z3Exception("Numeral is not an int64");
                return res;
            }
        }

        /// <summary>
        /// Retrieve the int value.
        /// </summary>
        public uint UInt
        {
            get
            {
                uint res = 0;
                if (Native.Z3_get_numeral_uint(Context.nCtx, NativeObject, ref res) == 0)
                    throw new Z3Exception("Numeral is not a uint");
                return res;
            }
        }

#if !FRAMEWORK_LT_4
        /// <summary>
        /// Retrieve the BigInteger value.
        /// </summary>
        public BigInteger BigInteger
        {
            get
            {
                return BigInteger.Parse(this.ToString());
            }
        }
#endif

        /// <summary>
        /// Returns a string representation of the numeral.
        /// </summary>        
        public override string ToString()
        {
            return Native.Z3_get_numeral_string(Context.nCtx, NativeObject);
        }

        #region Internal
        internal BitVecNum(Context ctx, IntPtr obj) : base(ctx, obj) { Contract.Requires(ctx != null); }
        #endregion
    }

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
