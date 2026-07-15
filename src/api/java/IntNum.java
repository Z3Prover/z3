/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    IntNum.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

import java.math.BigInteger;

/**
 * Integer Numerals
 **/
public class IntNum extends IntExpr
{

    IntNum(Context ctx, long obj)
    {
        super(ctx, obj);
    }

    /**
     * Retrieve the int value.
     **/
    public int getInt()
    {
        Native.IntPtr res = new Native.IntPtr();
        if (!Native.getNumeralInt(getContext().nCtx(), getNativeObject(), res))
            throw new Z3Exception("Numeral is not an int");
        return res.value;
    }

    /**
     * Retrieve the 64-bit int value.
     **/
    public long getInt64()
    {
        Native.LongPtr res = new Native.LongPtr();
        if (!Native.getNumeralInt64(getContext().nCtx(), getNativeObject(), res))
            throw new Z3Exception("Numeral is not an int64");
        return res.value;
    }

    /**
     * Retrieve the unsigned 32-bit value.
     * The returned Java {@code int} holds the raw bit pattern;
     * use {@code Integer.toUnsignedLong(v)} for unsigned interpretation.
     **/
    public int getUint()
    {
        Native.IntPtr res = new Native.IntPtr();
        if (!Native.getNumeralUint(getContext().nCtx(), getNativeObject(), res))
            throw new Z3Exception("Numeral is not a uint");
        return res.value;
    }

    /**
     * Retrieve the unsigned 64-bit value.
     * The returned Java {@code long} holds the raw bit pattern;
     * use {@code Long.toUnsignedString(v)} or {@link #getBigInteger()}
     * for values exceeding {@code Long.MAX_VALUE}.
     **/
    public long getUint64()
    {
        Native.LongPtr res = new Native.LongPtr();
        if (!Native.getNumeralUint64(getContext().nCtx(), getNativeObject(), res))
            throw new Z3Exception("Numeral is not a uint64");
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
    public String toString() {
        return Native.getNumeralString(getContext().nCtx(), getNativeObject());
    }
}
