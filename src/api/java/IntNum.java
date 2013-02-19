/**
 * This file was automatically generated from IntNum.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

import java.math.BigInteger;

/**
 * Integer Numerals
 **/
public class IntNum extends IntExpr
{

    IntNum(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }

    /**
     * Retrieve the int value.
     **/
    public int getInt() throws Z3Exception
    {
        Native.IntPtr res = new Native.IntPtr();
        if (Native.getNumeralInt(getContext().nCtx(), getNativeObject(), res) ^ true)
            throw new Z3Exception("Numeral is not an int");
        return res.value;
    }

    /**
     * Retrieve the 64-bit int value.
     **/
    public long getInt64() throws Z3Exception
    {
        Native.LongPtr res = new Native.LongPtr();
        if (Native.getNumeralInt64(getContext().nCtx(), getNativeObject(), res) ^ true)
            throw new Z3Exception("Numeral is not an int64");
        return res.value;
    }

    /**
     * Retrieve the BigInteger value.
     **/
    public BigInteger getBigInteger() throws Z3Exception
    {
        return new BigInteger(this.toString());
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
}
