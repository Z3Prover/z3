/**
 * This file was automatically generated from RatNum.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

import java.math.BigInteger;

/**
 * Rational Numerals
 **/
public class RatNum extends RealExpr
{
    /**
     * The numerator of a rational numeral.
     **/
    public IntNum Numerator() throws Z3Exception
    {
        return new IntNum(Context(), Native.getNumerator(Context().nCtx(),
                NativeObject()));
    }

    /**
     * The denominator of a rational numeral.
     **/
    public IntNum Denominator() throws Z3Exception
    {
        return new IntNum(Context(), Native.getDenominator(Context().nCtx(),
                NativeObject()));
    }

    /**
     * Converts the numerator of the rational to a BigInteger
     **/
    public BigInteger BigIntNumerator() throws Z3Exception
    {
        IntNum n = Numerator();
        return new BigInteger(n.toString());
    }

    /**
     * Converts the denominator of the rational to a BigInteger
     **/
    public BigInteger BigIntDenominator() throws Z3Exception
    {
        IntNum n = Denominator();
        return new BigInteger(n.toString());
    }

    /**
     * Returns a string representation in decimal notation. <remarks>The result
     * has at most <paramref name="precision"/> decimal places.</remarks>
     **/
    public String ToDecimalString(int precision) throws Z3Exception
    {
        return Native.getNumeralDecimalString(Context().nCtx(), NativeObject(),
                precision);
    }

    /**
     * Returns a string representation of the numeral.
     **/
    public String toString()
    {
        try
        {
            return Native.getNumeralString(Context().nCtx(), NativeObject());
        } catch (Z3Exception e)
        {
            return "Z3Exception: " + e.getMessage();
        }
    }

    RatNum(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }
}
