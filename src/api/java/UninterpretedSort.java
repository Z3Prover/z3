/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    UninterpretedSort.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

/**
 * Uninterpreted Sorts
 **/
public class UninterpretedSort extends Sort
{
    UninterpretedSort(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }

    UninterpretedSort(Context ctx, Symbol s) throws Z3Exception
    {
        super(ctx, Native.mkUninterpretedSort(ctx.nCtx(), s.getNativeObject()));
    }
}
