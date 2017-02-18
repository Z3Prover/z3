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
     * The sign of a floating-point numeral as a bit-vector expression
     * Remarks: NaN's do not have a bit-vector sign, so they are invalid arguments.
     * @throws Z3Exception 
     */
    public BitVecExpr getSignBV() {
        return new BitVecExpr(getContext(), Native.fpaGetNumeralSignBv(getContext().nCtx(), getNativeObject()));
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
     * The significand of a floating-point numeral as a bit-vector expression
     * Remarks: NaN is an invalid argument.
     * @throws Z3Exception 
     */
    public BitVecExpr getSignificandBV() {
        return new BitVecExpr(getContext(), Native.fpaGetNumeralSignificandBv(getContext().nCtx(), getNativeObject()));
    }
    
    /**
     * Return the exponent value of a floating-point numeral as a string
     * Remarks: NaN is an invalid argument.
     * @throws Z3Exception 
     */
    public String getExponent(boolean biased) {
        return Native.fpaGetNumeralExponentString(getContext().nCtx(), getNativeObject(), biased);
    }

    /**
     * Return the exponent value of a floating-point numeral as a signed 64-bit integer
     * Remarks: NaN is an invalid argument.
     * @throws Z3Exception 
     */
    public long getExponentInt64(boolean biased)  {
        Native.LongPtr res = new Native.LongPtr();
        if (!Native.fpaGetNumeralExponentInt64(getContext().nCtx(), getNativeObject(), res, biased))
            throw new Z3Exception("Exponent is not a 64 bit integer");
        return res.value;
    }

    /**
     * The exponent of a floating-point numeral as a bit-vector expression
     * Remarks: NaN is an invalid argument.
     * @throws Z3Exception 
     */
    public BitVecExpr getExponentBV(boolean biased) {
        return new BitVecExpr(getContext(), Native.fpaGetNumeralExponentBv(getContext().nCtx(), getNativeObject(), biased));
    }

    
    /**
     * Indicates whether the numeral is a NaN.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isNaN()
    {
        return Native.fpaIsNumeralNan(getContext().nCtx(), getNativeObject());
    }    

    /**
     * Indicates whether the numeral is a +oo or -oo.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isInf()
    {
        return Native.fpaIsNumeralInf(getContext().nCtx(), getNativeObject());
    }
    
    /**
     * Indicates whether the numeral is +zero or -zero.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isZero()
    {
        return Native.fpaIsNumeralZero(getContext().nCtx(), getNativeObject());
    }

    /**
     * Indicates whether the numeral is normal.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isNormal()
    {
        return Native.fpaIsNumeralNormal(getContext().nCtx(), getNativeObject());
    }
    
    /**
     * Indicates whether the numeral is subnormal.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isSubnormal()
    {
        return Native.fpaIsNumeralSubnormal(getContext().nCtx(), getNativeObject());
    }

    /**
     * Indicates whether the numeral is positive.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isPositive()
    {
        return Native.fpaIsNumeralPositive(getContext().nCtx(), getNativeObject());
    }

    /**
     * Indicates whether the numeral is negative.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isNegative()
    {
        return Native.fpaIsNumeralNegative(getContext().nCtx(), getNativeObject());
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
