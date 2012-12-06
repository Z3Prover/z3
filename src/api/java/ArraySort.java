/**
 * This file was automatically generated from ArraySort.cs
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter) 
 **/

package com.microsoft.z3;

/**
 * Array sorts.
 **/
public class ArraySort extends Sort
{
	/**
	 * The domain of the array sort.
	 * @throws Z3Exception 
	 **/
	public Sort Domain() throws Z3Exception
	{
		return Sort.Create(Context(),
				Native.getArraySortDomain(Context().nCtx(), NativeObject()));
	}

	/**
	 * The range of the array sort.
	 * @throws Z3Exception 
	 **/
	public Sort Range() throws Z3Exception
	{
		return Sort.Create(Context(),
				Native.getArraySortRange(Context().nCtx(), NativeObject()));
	}

	ArraySort(Context ctx, long obj) throws Z3Exception
	{
		super(ctx, obj);
	}

	ArraySort(Context ctx, Sort domain, Sort range) throws Z3Exception
	{
		super(ctx, Native.mkArraySort(ctx.nCtx(), domain.NativeObject(),
				range.NativeObject()));
	}
};
