/**
 * This file was automatically generated from BoolSort.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

/**
 * A Boolean sort.
 **/
public class BoolSort extends Sort
{
    BoolSort(Context ctx, long obj) throws Z3Exception { super(ctx, obj); {  }}
    BoolSort(Context ctx) throws Z3Exception { super(ctx, Native.mkBoolSort(ctx.nCtx())); {  }}
};
