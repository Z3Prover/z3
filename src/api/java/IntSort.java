/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    IntSort.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

/**
 * An Integer sort
 **/
public class IntSort extends ArithSort
{
    IntSort(Context ctx, long obj)
    {
        super(ctx, obj);
    }

    IntSort(Context ctx)
    {
        super(ctx, Native.mkIntSort(ctx.nCtx()));
    }
}
