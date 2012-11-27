/**
 * This file was automatically generated from IntNum.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.Microsoft.Z3;

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
	public int Int() throws Z3Exception
	{
		Native.IntPtr res = new Native.IntPtr();
		if (Native.getNumeralInt(Context().nCtx(), NativeObject(), res) ^ true)
			throw new Z3Exception("Numeral is not an int");
		return res.value;
	}

	/**
	 * Retrieve the 64-bit int value.
	 **/
	public long Int64() throws Z3Exception
	{
		Native.LongPtr res = new Native.LongPtr();
		if (Native.getNumeralInt64(Context().nCtx(), NativeObject(), res) ^ true)
			throw new Z3Exception("Numeral is not an int64");
		return res.value;
	}

	/**
	 * Retrieve the BigInteger value.
	 **/
	public BigInteger BigInteger() throws Z3Exception
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
}
