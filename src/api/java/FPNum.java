/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    FPNum.java

Abstract:

Author:

    Christoph Wintersteiger (cwinter) 2013-06-10

Notes:
    
--*/
package com.microsoft.z3;

/**
 * FloatingPoint Numerals
 */
public class FPNum extends FPExpr
{
    /**
     * Retrieves the sign of a floating-point literal     
     * Remarks: returns true if the numeral is negative 
     * @throws Z3Exception 
     */
    public boolean getSign() {
        Native.IntPtr res = new Native.IntPtr();
        if (!Native.fpaGetNumeralSign(getContext().nCtx(), getNativeObject(), res))
            throw new Z3Exception("Sign is not a Boolean value");
        return res.value != 0;
    }

    /**
     * The significand value of a floating-point numeral as a string
     * Remarks: The significand s is always 0 &lt; s &lt; 2.0; the resulting string is long
     * enough to represent the real significand precisely.
     * @throws Z3Exception 
     **/
    public String getSignificand() {
        return Native.fpaGetNumeralSignificandString(getContext().nCtx(), getNativeObject());
    }

    /**
     * The significand value of a floating-point numeral as a UInt64
     * Remarks: This function extracts the significand bits, without the 
     * hidden bit or normalization. Throws an exception if the
     * significand does not fit into a UInt64.
     * @throws Z3Exception
     **/
    public long getSignificandUInt64()
    {
        Native.LongPtr res = new Native.LongPtr();
        if (!Native.fpaGetNumeralSignificandUint64(getContext().nCtx(), getNativeObject(), res))
            throw new Z3Exception("Significand is not a 64 bit unsigned integer");
        return res.value;
    }
    
    /**
     * Return the exponent value of a floating-point numeral as a string
     * @throws Z3Exception 
     */
    public String getExponent() {
        return Native.fpaGetNumeralExponentString(getContext().nCtx(), getNativeObject());
    }

    /**
     * Return the exponent value of a floating-point numeral as a signed 64-bit integer
     * @throws Z3Exception 
     */
    public long getExponentInt64()  {
        Native.LongPtr res = new Native.LongPtr();
        if (!Native.fpaGetNumeralExponentInt64(getContext().nCtx(), getNativeObject(), res))
            throw new Z3Exception("Exponent is not a 64 bit integer");
        return res.value;
    }
    
    public FPNum(Context ctx, long obj)
    {
        super(ctx, obj);
    }
    
    /**
     * Returns a string representation of the numeral.
     */           
    public String toString()
    {
        return Native.getNumeralString(getContext().nCtx(), getNativeObject());
    }

}
