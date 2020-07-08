/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    BitVecNum.cs

Abstract:

    Z3 Managed API: BitVec Numerals

Author:

    Christoph Wintersteiger (cwinter) 2012-03-20

Notes:
    
--*/
using System.Diagnostics;
using System;

#if !FRAMEWORK_LT_4
using System.Numerics;
#endif

namespace Microsoft.Z3
{
    /// <summary>
    /// Bit-vector numerals
    /// </summary>
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
        /// Returns a decimal string representation of the numeral.
        /// </summary>        
        public override string ToString()
        {
            return Native.Z3_get_numeral_string(Context.nCtx, NativeObject);
        }

        /// <summary>
        /// Returns a binary string representation of the numeral.
        /// </summary>        
        public string ToBinaryString()
        {
            return Native.Z3_get_numeral_binary_string(Context.nCtx, NativeObject);
        }

        #region Internal
        internal BitVecNum(Context ctx, IntPtr obj) : base(ctx, obj) { Debug.Assert(ctx != null); }
        #endregion
    }
}
