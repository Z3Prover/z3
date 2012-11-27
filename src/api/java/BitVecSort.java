/**
 * This file was automatically generated from BitVecSort.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/
package com.Microsoft.Z3;

/**
 * Bit-vector sorts.
 **/
public class BitVecSort extends Sort
{
	/**
	 * The size of the bit-vector sort.
	 **/
	public int Size()
	{
		return Native.getBvSortSize(Context().nCtx(), NativeObject());
	}

	BitVecSort(Context ctx, long obj) throws Z3Exception
	{
		super(ctx, obj);
	}
};
