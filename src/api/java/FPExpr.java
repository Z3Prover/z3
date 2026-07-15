/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    FPExpr.java

Abstract:

Author:

    Christoph Wintersteiger (cwinter) 2013-06-10

Notes:
    
--*/
package com.microsoft.z3;

/**
 * FloatingPoint Expressions
 */
public class FPExpr extends Expr<FPSort>
{   
    /**
     * The number of exponent bits.
     * @throws Z3Exception 
     */
    public int getEBits() { return ((FPSort)getSort()).getEBits(); }

    /**
     * The number of significand bits.
     * @throws Z3Exception 
     */
    public int getSBits() { return ((FPSort)getSort()).getSBits(); }

    /**
     * Indicates whether the floating-point expression is a numeral.
     * @throws Z3Exception on error
     * @return a boolean
     **/
    public boolean isNumeral()
    {
        return Native.fpaIsNumeral(getContext().nCtx(), getNativeObject());
    }

    public FPExpr(Context ctx, long obj)
    {
        super(ctx, obj); 
    }

}
