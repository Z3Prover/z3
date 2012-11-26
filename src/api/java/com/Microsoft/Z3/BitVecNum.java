/**
 * This file was automatically generated from BitVecNum.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;
import com.Microsoft.Z3.Enumerations.*;
/* using System; */

/* using System.Numerics; */

    /**
     * Bit-vector numerals
     **/
    public class BitVecNum extends BitVecExpr
    {
        /**
         * Retrieve the 64-bit unsigned integer value.
         **/
        public long UInt64() 
            {
                long res = 0;
                if (Native.getNumeralInt64(Context().nCtx(), NativeObject(), res) ^ true)
                    throw new Z3Exception("Numeral is not a 64 bit unsigned");
                return res;
            }

        /**
         * Retrieve the int value.
         **/
        public int Int() 
            {
                int res = 0;
                if (Native.getNumeralInt(Context().nCtx(), NativeObject(), res) ^ true)
                    throw new Z3Exception("Numeral is not an int");
                return res;
            }

        /**
         * Retrieve the 64-bit int value.
         **/
        public long Int64() 
            {
                long res = 0;
                if (Native.getNumeralInt64(Context().nCtx(), NativeObject(), res) ^ true)
                    throw new Z3Exception("Numeral is not an int64");
                return res;
            }

        /**
         * Retrieve the int value.
         **/
        public int UInt() 
            {
                int res = 0;
                if (Native.getNumeralInt(Context().nCtx(), NativeObject(), res) ^ true)
                    throw new Z3Exception("Numeral is not a int");
                return res;
            }

        /**
         * Retrieve the BigInteger value.
         **/
        public BigInteger BigInteger() 
            {
                return new BigInteger(this.toString());
            }

        /**
         * Returns a string representation of the numeral.
         **/
        public String toString()
        {
            return Native.getNumeralString(Context().nCtx(), NativeObject());
        }

    BitVecNum(Context ctx, long obj) { super(ctx, obj); {  }}
    }
