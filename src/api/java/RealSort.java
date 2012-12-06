/**
 * This file was automatically generated from RealSort.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

/**
 * A real sort
 **/
public class RealSort extends ArithSort
{
    RealSort(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }

    RealSort(Context ctx) throws Z3Exception
    {
        super(ctx, Native.mkRealSort(ctx.nCtx()));
    }
}
