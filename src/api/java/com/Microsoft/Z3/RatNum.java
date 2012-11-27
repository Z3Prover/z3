/**
 * This file was automatically generated from RatNum.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;
import com.Microsoft.Z3.Enumerations.*;
/* using System; */

/* using System.Numerics; */

    /**
     * Rational Numerals
     **/
    public class RatNum extends RealExpr
    {
        /**
         * The numerator of a rational numeral.
         **/
        public IntNum Numerator() 
            {
                

                return new IntNum(Context(), Native.getNumerator(Context().nCtx(), NativeObject()));
            }

        /**
         * The denominator of a rational numeral.
         **/
        public IntNum Denominator() 
            {
                

                return new IntNum(Context(), Native.getDenominator(Context().nCtx(), NativeObject()));
            }

        /**
         * Converts the numerator of the rational to a BigInteger
         **/
        public BigInteger BigIntNumerator() 
            {
                IntNum n = Numerator();
                return new BigInteger(n.toString());
            }

        /**
         * Converts the denominator of the rational to a BigInteger
         **/
        public BigInteger BigIntDenominator() 
            {
                IntNum n = Denominator();
                return new BigInteger(n.toString());
            }

        /**
         * Returns a string representation in decimal notation.
         * <remarks>The result has at most <paramref name="precision"/> decimal places.</remarks>    
         **/
        public String ToDecimalString(int precision)
        {
            return Native.getNumeralDecimalString(Context().nCtx(), NativeObject(), precision);
        }

        /**
         * Returns a string representation of the numeral.
         **/
        public String toString()
        {
            return Native.getNumeralString(Context().nCtx(), NativeObject());
        }

        RatNum(Context ctx, long obj) throws Z3Exception
        { super(ctx, obj);
            
        }
    }
