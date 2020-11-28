/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    DatatypeExpr.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/

package com.microsoft.z3;

/**
 * Datatype expressions
 **/
public class DatatypeExpr<R extends Sort> extends Expr<DatatypeSort<R>>
{
    /**
     * Constructor for DatatypeExpr
     **/
    DatatypeExpr(Context ctx, long obj)
    {
        super(ctx, obj);
    }
}
