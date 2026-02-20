/**
Copyright (c) 2024 Microsoft Corporation
   
Module Name:

    FiniteSetSort.java

Abstract:

Author:

    GitHub Copilot

Notes:
    
**/ 

package com.microsoft.z3;

/**
 * Finite set sorts.
 **/
public class FiniteSetSort extends Sort
{
    FiniteSetSort(Context ctx, long obj)
    {
        super(ctx, obj);
    }

    FiniteSetSort(Context ctx, Sort elemSort)
    {
        super(ctx, Native.mkFiniteSetSort(ctx.nCtx(), elemSort.getNativeObject()));
    }

    /**
     * Get the element sort (basis) of this finite set sort.
     **/
    public Sort getBasis()
    {
        return Sort.create(getContext(), Native.getFiniteSetSortBasis(getContext().nCtx(), getNativeObject()));
    }
}
