/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    SeqSort.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

/**
 * A Sequence sort
 **/
public class SeqSort<R extends Sort> extends Sort
{
    SeqSort(Context ctx, long obj)
    {
        super(ctx, obj);
    }
}
