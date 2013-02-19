/**
 * This file was automatically generated from BitVecExpr.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

/**
 * Bit-vector expressions
 **/
public class BitVecExpr extends Expr
{

	/**
	 * The size of the sort of a bit-vector term.
	 * @throws Z3Exception 
	 **/
	public int getSortSize() throws Z3Exception
	{
		return ((BitVecSort) getSort()).getSize();
	}

	/**
	 * Constructor for BitVecExpr </summary>
	 **/
	BitVecExpr(Context ctx)
	{
		super(ctx);
	}

	BitVecExpr(Context ctx, long obj) throws Z3Exception
	{
		super(ctx, obj);
	}
}
