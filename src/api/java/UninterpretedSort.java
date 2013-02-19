/**
 * This file was automatically generated from UninterpretedSort.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
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
