/**
 * This file was automatically generated from ArithExpr.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 * **/

package com.microsoft.z3;

/**
 * Arithmetic expressions (int/real)
 **/
public class ArithExpr extends Expr
{
	/**
	 * Constructor for ArithExpr </summary>
	 **/
	protected ArithExpr(Context ctx)
	{
		super(ctx);
	}

	ArithExpr(Context ctx, long obj) throws Z3Exception
	{
		super(ctx, obj);
	}
}
