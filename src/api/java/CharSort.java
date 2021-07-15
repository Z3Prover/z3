/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    CharSort.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

/**
 * A Character sort
 **/
public class CharSort extends Sort
{
    CharSort(Context ctx, long obj)
    {
        super(ctx, obj);
    }

    CharSort(Context ctx) { super(ctx, Native.mkCharSort(ctx.nCtx())); {  }}

}

