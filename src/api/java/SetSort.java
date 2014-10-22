/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    SetSort.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

/**
 * Set sorts.
 **/
public class SetSort extends Sort
{
    SetSort(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }

    SetSort(Context ctx, Sort ty) throws Z3Exception
    {
        super(ctx, Native.mkSetSort(ctx.nCtx(), ty.getNativeObject()));
    }
}
