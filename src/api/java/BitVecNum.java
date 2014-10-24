/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    BitVecNum.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
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
    public int getInt() throws Z3Exception
    {
        Native.IntPtr res = new Native.IntPtr();
        if (Native.getNumeralInt(getContext().nCtx(), getNativeObject(), res) ^ true)
            throw new Z3Exception("Numeral is not an int");
        return res.value;
    }

    /**
     * Retrieve the 64-bit int value.
     * 
     * @throws Z3Exception
     **/
    public long getLong() throws Z3Exception
    {
        Native.LongPtr res = new Native.LongPtr();
        if (Native.getNumeralInt64(getContext().nCtx(), getNativeObject(), res) ^ true)
            throw new Z3Exception("Numeral is not a long");
        return res.value;
    }

    /**
     * Retrieve the BigInteger value.
     **/
    public BigInteger getBigInteger()
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

    BitVecNum(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }
}
