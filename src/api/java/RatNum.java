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
    public IntNum getNumerator()
    {
        return new IntNum(getContext(), Native.getNumerator(getContext().nCtx(),
                getNativeObject()));
    }

    /**
     * The denominator of a rational numeral.
     **/
    public IntNum getDenominator()
    {
        return new IntNum(getContext(), Native.getDenominator(getContext().nCtx(),
                getNativeObject()));
    }

    /**
     * Converts the numerator of the rational to a BigInteger
     **/
    public BigInteger getBigIntNumerator()
    {
        IntNum n = getNumerator();
        return new BigInteger(n.toString());
    }

    /**
     * Converts the denominator of the rational to a BigInteger
     **/
    public BigInteger getBigIntDenominator()
    {
        IntNum n = getDenominator();
        return new BigInteger(n.toString());
    }

    /**
     * Retrieve the numerator and denominator as 64-bit integers.
     * Throws if the value does not fit in 64-bit integers.
     * @return a two-element array [numerator, denominator]
     **/
    public long[] getSmall()
    {
        Native.LongPtr num = new Native.LongPtr();
        Native.LongPtr den = new Native.LongPtr();
        if (!Native.getNumeralSmall(getContext().nCtx(), getNativeObject(), num, den))
            throw new Z3Exception("Numeral does not fit in int64");
        return new long[] { num.value, den.value };
    }

    /**
     * Retrieve the numerator and denominator as 64-bit integers.
     * Returns null if the value does not fit in 64-bit integers.
     * @return a two-element array [numerator, denominator], or null
     **/
    public long[] getRationalInt64()
    {
        Native.LongPtr num = new Native.LongPtr();
        Native.LongPtr den = new Native.LongPtr();
        if (!Native.getNumeralRationalInt64(getContext().nCtx(), getNativeObject(), num, den))
            return null;
        return new long[] { num.value, den.value };
    }

    /**
     * Returns a string representation in decimal notation.
     * Remarks: The result
     * has at most {@code precision} decimal places.
     **/
    public String toDecimalString(int precision)
    {
        return Native.getNumeralDecimalString(getContext().nCtx(), getNativeObject(),
                precision);
    }

    /**
     * Returns a string representation of the numeral.
     **/
    @Override
    public String toString() {
        return Native.getNumeralString(getContext().nCtx(), getNativeObject());
    }

    RatNum(Context ctx, long obj)
    {
        super(ctx, obj);
    }
}
