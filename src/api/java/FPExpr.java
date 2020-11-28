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
    
    public FPExpr(Context ctx, long obj)
    {
        super(ctx, obj); 
    }

}
