/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    FPRMExpr.java

Abstract:

Author:

    Christoph Wintersteiger (cwinter) 2013-06-10

Notes:
    
--*/
package com.microsoft.z3;

/**
 * The FloatingPoint RoundingMode sort
 **/
public class FPRMSort extends Sort
{

    public FPRMSort(Context ctx)
    {        
        super(ctx, Native.mkFpaRoundingModeSort(ctx.nCtx()));
    }

    public FPRMSort(Context ctx, long obj)
    {
        super(ctx, obj); 
    }

}