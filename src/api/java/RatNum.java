/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    RatNum.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
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
    public IntNum getNumerator() throws Z3Exception
    {
        return new IntNum(getContext(), Native.getNumerator(getContext().nCtx(),
                getNativeObject()));
    }

    /**
     * The denominator of a rational numeral.
     **/
    public IntNum getDenominator() throws Z3Exception
    {
        return new IntNum(getContext(), Native.getDenominator(getContext().nCtx(),
                getNativeObject()));
    }

    /**
     * Converts the numerator of the rational to a BigInteger
     **/
    public BigInteger getBigIntNumerator() throws Z3Exception
    {
        IntNum n = getNumerator();
        return new BigInteger(n.toString());
    }

    /**
     * Converts the denominator of the rational to a BigInteger
     **/
    public BigInteger getBigIntDenominator() throws Z3Exception
    {
        IntNum n = getDenominator();
        return new BigInteger(n.toString());
    }

    /**
     * Returns a string representation in decimal notation.
     * Remarks: The result
     * has at most {@code precision} decimal places.
     **/
    public String toDecimalString(int precision) throws Z3Exception
    {
        return Native.getNumeralDecimalString(getContext().nCtx(), getNativeObject(),
                precision);
    }

    /**
     * Returns a string representation of the numeral.
     **/
    public String toString()
    {
        try
        {
            return Native.getNumeralString(getContext().nCtx(), getNativeObject());
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
