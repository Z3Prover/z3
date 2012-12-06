/**
 * This file was automatically generated from RealExpr.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

/**
 * Real expressions
 **/
public class RealExpr extends ArithExpr
{
    /**
     * Constructor for RealExpr </summary>
     **/
    protected RealExpr(Context ctx)
    {
        super(ctx);
    }

    RealExpr(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }
}
