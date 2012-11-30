/**
 * This file was automatically generated from BitVecNum.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

import java.math.BigInteger;

/**
 * Bit-vector numerals
 **/
public class BitVecNum extends BitVecExpr
{
    /**
     * Retrieve the int value.
     * 
     * @throws Z3Exception
     **/
    public int Int() throws Z3Exception
    {
        Native.IntPtr res = new Native.IntPtr();
        if (Native.getNumeralInt(Context().nCtx(), NativeObject(), res) ^ true)
            throw new Z3Exception("Numeral is not an int");
        return res.value;
    }

    /**
     * Retrieve the 64-bit int value.
     * 
     * @throws Z3Exception
     **/
    public long Long() throws Z3Exception
    {
        Native.LongPtr res = new Native.LongPtr();
        if (Native.getNumeralInt64(Context().nCtx(), NativeObject(), res) ^ true)
            throw new Z3Exception("Numeral is not an int64");
        return res.value;
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
        try
        {
            return Native.getNumeralString(Context().nCtx(), NativeObject());
        } catch (Z3Exception e)
        {
            return "Z3Exception: " + e.getMessage();
        }
    }

    BitVecNum(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }
}
