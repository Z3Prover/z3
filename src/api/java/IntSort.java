/**
 * This file was automatically generated from IntSort.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

/**
 * An Integer sort
 **/
public class IntSort extends ArithSort
{
	IntSort(Context ctx, long obj) throws Z3Exception
	{
		super(ctx, obj);
	}

	IntSort(Context ctx) throws Z3Exception
	{
		super(ctx, Native.mkIntSort(ctx.nCtx()));
	}
}
