/**
 * This file was automatically generated from SetSort.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
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
