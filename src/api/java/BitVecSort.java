/**
 * This file was automatically generated from BitVecSort.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/
package com.microsoft.z3;

/**
 * Bit-vector sorts.
 **/
public class BitVecSort extends Sort
{
	/**
	 * The size of the bit-vector sort.
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
