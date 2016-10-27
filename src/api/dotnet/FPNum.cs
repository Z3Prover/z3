/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    FPNum.cs

Abstract:

    Z3 Managed API: Floating Point Numerals

Author:

    Christoph Wintersteiger (cwinter) 2013-06-10

Notes:

--*/
using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// FloatiungPoint Numerals
    /// </summary>
    [ContractVerification(true)]
    public class FPNum : FPExpr
    {
        /// <summary>
        /// The sign of a floating-point numeral as a bit-vector expression
        /// </summary>
        /// <remarks>
        /// NaN's do not have a bit-vector sign, so they are invalid arguments.
        /// </remarks>
        public BitVecExpr SignBV
        {
            get
            {
                return new BitVecExpr(Context, Native.Z3_fpa_get_numeral_sign_bv(Context.nCtx, NativeObject));
            }
        }

        /// <summary>
        /// Retrieves the sign of a floating-point literal
        /// </summary>
        /// <remarks>
        /// Remarks: returns true if the numeral is negative
        /// </remarks>
        public bool Sign
        {
            get
            {
                int res = 0;
                if (Native.Z3_fpa_get_numeral_sign(Context.nCtx, NativeObject, ref res) == 0)
                    throw new Z3Exception("Sign is not a Boolean value");
                return res != 0;
            }
        }

        /// <summary>
        /// The significand value of a floating-point numeral as a string
        /// </summary>
        /// <remarks>
        /// The significand s is always 0 &lt; s &lt; 2.0; the resulting string is long
        /// enough to represent the real significand precisely.
        /// </remarks>
        public string Significand
        {
            get
            {
                return Native.Z3_fpa_get_numeral_significand_string(Context.nCtx, NativeObject);
            }
        }

        /// <summary>
        /// The significand value of a floating-point numeral as a UInt64
        /// </summary>
        /// <remarks>
        /// This function extracts the significand bits, without the
        /// hidden bit or normalization. Throws an exception if the
        /// significand does not fit into a UInt64.
        /// </remarks>
        public UInt64 SignificandUInt64
        {
            get
            {
                UInt64 result = 0;
                if (Native.Z3_fpa_get_numeral_significand_uint64(Context.nCtx, NativeObject, ref result) == 0)
                    throw new Z3Exception("Significand is not a 64 bit unsigned integer");
                return result;
            }
        }

        /// <summary>
        /// The significand of a floating-point numeral as a bit-vector expression
        /// </summary>
        /// <remarks>
        /// +oo, -oo and NaN's do not have a bit-vector significand, so they are invalid arguments.
        /// </remarks>
        public BitVecExpr SignificandBV
        {
            get
            {
                return new BitVecExpr(Context, Native.Z3_fpa_get_numeral_significand_bv(Context.nCtx, NativeObject));
            }
        }

        /// <summary>
        /// Return the (biased) exponent value of a floating-point numeral as a string
        /// </summary>
        public string Exponent(bool biased = true)
        {
            return Native.Z3_fpa_get_numeral_exponent_string(Context.nCtx, NativeObject, biased ? 1 : 0);
        }

        /// <summary>
        /// Return the exponent value of a floating-point numeral as a signed 64-bit integer
        /// </summary>
        public Int64 ExponentInt64(bool biased = true)
        {
            Int64 result = 0;
            if (Native.Z3_fpa_get_numeral_exponent_int64(Context.nCtx, NativeObject, ref result, biased ? 1 : 0) == 0)
                throw new Z3Exception("Exponent is not a 64 bit integer");
            return result;
        }

        /// <summary>
        /// The exponent of a floating-point numeral as a bit-vector expression
        /// </summary>
        /// <remarks>
        /// +oo, -oo and NaN's do not have a bit-vector exponent, so they are invalid arguments.
        /// </remarks>
        public BitVecExpr ExponentBV(bool biased = true)
        {
            return new BitVecExpr(Context, Native.Z3_fpa_get_numeral_exponent_bv(Context.nCtx, NativeObject, biased ? 1 : 0));
        }

        /// <summary>
        /// Indicates whether the numeral is a NaN.
        /// </summary>
        public bool IsNaN { get { return Native.Z3_fpa_is_numeral_nan(Context.nCtx, NativeObject) != 0; } }

        /// <summary>
        /// Indicates whether the numeral is a +oo or -oo.
        /// </summary>
        public bool IsInf { get { return Native.Z3_fpa_is_numeral_inf(Context.nCtx, NativeObject) != 0; } }

        /// <summary>
        /// Indicates whether the numeral is +zero or -zero.
        /// </summary>
        public bool IsZero{ get { return Native.Z3_fpa_is_numeral_zero(Context.nCtx, NativeObject) != 0; } }

        /// <summary>
        /// Indicates whether the numeral is normal.
        /// </summary>
        public bool IsNormal { get { return Native.Z3_fpa_is_numeral_normal(Context.nCtx, NativeObject) != 0; } }

        /// <summary>
        /// Indicates whether the numeral is subnormal.
        /// </summary>
        public bool IsSubnormal { get { return Native.Z3_fpa_is_numeral_subnormal(Context.nCtx, NativeObject) != 0; } }

        /// <summary>
        /// Indicates whether the numeral is positive.
        /// </summary>
        public bool IsPositive { get { return Native.Z3_fpa_is_numeral_positive(Context.nCtx, NativeObject) != 0; } }

        /// <summary>
        /// Indicates whether the numeral is negative.
        /// </summary>
        public bool IsNegative { get { return Native.Z3_fpa_is_numeral_negative(Context.nCtx, NativeObject) != 0; } }

        #region Internal
        internal FPNum(Context ctx, IntPtr obj)
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
