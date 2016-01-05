/**
Copyright (c) 2012-2016 Microsoft Corporation
   
Module Name:

    SeqExpr.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

/**
 * Seq expressions
 **/
public class SeqExpr extends Expr
{
    /**
     * Constructor for SeqExpr
     * @throws Z3Exception on error
     **/
    SeqExpr(Context ctx, long obj)
    {
        super(ctx, obj);
    }
}
