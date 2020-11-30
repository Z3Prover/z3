/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    ArraySort.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/

package com.microsoft.z3;

/**
 * Array sorts.
 **/
@SuppressWarnings("unchecked")
public class ArraySort<D extends Sort, R extends Sort> extends Sort
{
    /**
     * The domain of the array sort.
     * @throws Z3Exception 
     * @throws Z3Exception on error
     * @return a sort
     **/
    public D getDomain()
    {
        return (D) Sort.create(getContext(),
                Native.getArraySortDomain(getContext().nCtx(), getNativeObject()));
    }

    /**
     * The range of the array sort.
     * @throws Z3Exception 
     * @throws Z3Exception on error
     * @return a sort
     **/
    public R getRange()
    {
        return (R) Sort.create(getContext(),
                Native.getArraySortRange(getContext().nCtx(), getNativeObject()));
    }

    ArraySort(Context ctx, long obj)
    {
        super(ctx, obj);
    }

    ArraySort(Context ctx, D domain, R range)
    {
        super(ctx, Native.mkArraySort(ctx.nCtx(), domain.getNativeObject(),
                range.getNativeObject()));
    }

    ArraySort(Context ctx, Sort[] domains, R range)
    {
        super(ctx, Native.mkArraySortN(ctx.nCtx(), domains.length, AST.arrayToNative(domains),
                range.getNativeObject()));
    }
};
