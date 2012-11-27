/**
 * This file was automatically generated from FiniteDomainSort.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

/**
 * Finite domain sorts.
 **/
public class FiniteDomainSort extends Sort
{
	/**
	 * The size of the finite domain sort.
	 **/
	public long Size()
	{
		Native.LongPtr res = new Native.LongPtr();
		Native.getFiniteDomainSortSize(Context().nCtx(), NativeObject(), res);
		return res.value;
	}

	FiniteDomainSort(Context ctx, long obj) throws Z3Exception
	{
		super(ctx, obj);
	}

	FiniteDomainSort(Context ctx, Symbol name, long size) throws Z3Exception
	{
		super(ctx, Native.mkFiniteDomainSort(ctx.nCtx(), name.NativeObject(),
				size));
	}
}
