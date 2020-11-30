/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    ArrayExpr.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/

package com.microsoft.z3;


/**
 * Array expressions
 **/
public class ArrayExpr<D extends Sort, R extends Sort> extends Expr<ArraySort<D, R>>
{
    /**
     * Constructor for ArrayExpr
     **/
    ArrayExpr(Context ctx, long obj)
    {
        super(ctx, obj);
    }
}
