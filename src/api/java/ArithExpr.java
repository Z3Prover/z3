/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    ArithExpr.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/

package com.microsoft.z3;

/**
 * Arithmetic expressions (int/real)
 **/
public class ArithExpr<R extends ArithSort> extends Expr<R>
{
    /**
     * Constructor for ArithExpr
     **/
    ArithExpr(Context ctx, long obj)
    {
        super(ctx, obj);
    }
}
