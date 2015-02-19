/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    FPSort.java

Abstract:

Author:

    Christoph Wintersteiger (cwinter) 2013-06-10

Notes:
    
--*/
package com.microsoft.z3;

/**
 * A FloatingPoint sort
 **/
public class FPSort extends Sort
{

    public FPSort(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);        
    }
    
    public FPSort(Context ctx, int ebits, int sbits) throws Z3Exception
    {
        super(ctx, Native.mkFpaSort(ctx.nCtx(), ebits, sbits));        
    }
    
    /**
     * The number of exponent bits.
     */
    public int getEBits() throws Z3Exception {
        return Native.fpaGetEbits(getContext().nCtx(), getNativeObject());        
    }
    
    /**
     * The number of significand bits.
     */
    public int getSBits() throws Z3Exception {
        return Native.fpaGetEbits(getContext().nCtx(), getNativeObject());        
    }
    
}
