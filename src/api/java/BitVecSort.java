/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    BitVecSort.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/

package com.microsoft.z3;

/**
 * Bit-vector sorts.
 **/
public class BitVecSort extends Sort
{
    /**
     * The size of the bit-vector sort.
     * @throws Z3Exception on error
     * @return an int
     **/
    public int getSize() throws Z3Exception
    {
        return Native.getBvSortSize(getContext().nCtx(), getNativeObject());
    }

    BitVecSort(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }
};
