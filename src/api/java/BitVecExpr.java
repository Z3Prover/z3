/**
 * This file was automatically generated from BitVecExpr.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.Microsoft.Z3;

/**
 * Bit-vector expressions
 **/
public class BitVecExpr extends Expr
{

	/**
	 * The size of the sort of a bit-vector term.
	 * @throws Z3Exception 
	 **/
	public int SortSize() throws Z3Exception
	{
		return ((BitVecSort) Sort()).Size();
	}

	/**
	 * Constructor for BitVecExpr </summary>
	 **/
	protected BitVecExpr(Context ctx)
	{
		super(ctx);
	}

	BitVecExpr(Context ctx, long obj) throws Z3Exception
	{
		super(ctx, obj);
	}
}
