/**
Copyright (c) 2012-2016 Microsoft Corporation
   
Module Name:

    ReExpr.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

/**
 * Re expressions
 **/
public class ReExpr<R extends Sort> extends Expr<ReSort<R>>
{
    /**
     * Constructor for ReExpr
     * @throws Z3Exception on error
     **/
    ReExpr(Context ctx, long obj)
    {
        super(ctx, obj);
    }
}
