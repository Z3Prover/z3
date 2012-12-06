/**
 * This file was automatically generated from IntExpr.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

/**
 * Int expressions
 **/
public class IntExpr extends ArithExpr
{
	/**
	 * Constructor for IntExpr </summary>
	 **/
	protected IntExpr(Context ctx) throws Z3Exception
	{
		super(ctx);
	}

	IntExpr(Context ctx, long obj) throws Z3Exception
	{
		super(ctx, obj);
	}
}
