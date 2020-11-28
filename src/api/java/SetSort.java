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
public class SetSort<D extends Sort> extends ArraySort<D, BoolSort>
{
    SetSort(Context ctx, long obj)
    {
        super(ctx, obj);
    }

    SetSort(Context ctx, D ty)
    {
        super(ctx, Native.mkSetSort(ctx.nCtx(), ty.getNativeObject()));
    }
}
