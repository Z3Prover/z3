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
        /// Return the exponent value of a floating-point numeral as a string
        /// </summary>
        public string Exponent
        {
            get
            {
                return Native.Z3_fpa_get_numeral_exponent_string(Context.nCtx, NativeObject);
            }
        }

        /// <summary>
        /// Return the exponent value of a floating-point numeral as a signed 64-bit integer
        /// </summary>
        public Int64 ExponentInt64
        {
            get
            {
                Int64 result = 0;
                if (Native.Z3_fpa_get_numeral_exponent_int64(Context.nCtx, NativeObject, ref result) == 0)
                    throw new Z3Exception("Exponent is not a 64 bit integer");
                return result;
            }
        }

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
