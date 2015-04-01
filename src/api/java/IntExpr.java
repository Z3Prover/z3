/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    IntExpr.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

/**
 * Int expressions
 **/
public class IntExpr extends ArithExpr
{
    /**
     * Constructor for IntExpr
     * @throws Z3Exception on error
     **/
    IntExpr(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }
}
