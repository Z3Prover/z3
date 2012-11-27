/**
 * This file was automatically generated from BoolExpr.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

/**
 * Boolean expressions
 **/
public class BoolExpr extends Expr
{
	/**
	 * Constructor for BoolExpr </summary>
	 **/
	protected BoolExpr(Context ctx)
	{
		super(ctx);
	}

	/**
	 * Constructor for BoolExpr </summary>
	 * @throws Z3Exception 
	 **/
	BoolExpr(Context ctx, long obj) throws Z3Exception
	{
		super(ctx, obj);
	}
}
