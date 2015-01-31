/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    BoolExpr.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/

package com.microsoft.z3;

/**
 * Boolean expressions
 **/
public class BoolExpr extends Expr
{
    /**
     * Constructor for BoolExpr
     **/
    protected BoolExpr(Context ctx)
    {
        super(ctx);
    }

    /**
     * Constructor for BoolExpr
     * @throws Z3Exception 
     * @throws Z3Exception on error
     **/
    BoolExpr(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }
}
