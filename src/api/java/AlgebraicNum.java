/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    AlgebraicNum.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/

package com.microsoft.z3;

/**
 * Algebraic numbers
 **/
public class AlgebraicNum extends ArithExpr
{
	/**
	 * Return a upper bound for a given real algebraic number. The interval
	 * isolating the number is smaller than 1/10^<paramref name="precision"/>.
	 * <seealso cref="Expr.IsAlgebraicNumber"/> <param name="precision">the
	 * precision of the result</param>
	 * 
	 * @return A numeral Expr of sort Real
	 **/
	public RatNum toUpper(int precision) throws Z3Exception
	{

		return new RatNum(getContext(), Native.getAlgebraicNumberUpper(getContext()
				.nCtx(), getNativeObject(), precision));
	}

	/**
	 * Return a lower bound for the given real algebraic number. The interval
	 * isolating the number is smaller than 1/10^<paramref name="precision"/>.
	 * <seealso cref="Expr.IsAlgebraicNumber"/> <param name="precision"></param>
	 * 
	 * @return A numeral Expr of sort Real
	 **/
	public RatNum toLower(int precision) throws Z3Exception
	{

		return new RatNum(getContext(), Native.getAlgebraicNumberLower(getContext()
				.nCtx(), getNativeObject(), precision));
	}

	/**
	 * Returns a string representation in decimal notation. <remarks>The result
	 * has at most <paramref name="precision"/> decimal places.</remarks>
	 **/
	public String toDecimal(int precision) throws Z3Exception
	{

		return Native.getNumeralDecimalString(getContext().nCtx(), getNativeObject(),
				precision);
	}

	AlgebraicNum(Context ctx, long obj) throws Z3Exception
	{
		super(ctx, obj);

	}
}
