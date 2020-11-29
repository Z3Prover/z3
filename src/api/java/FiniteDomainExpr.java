/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    FiniteDomainExpr.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2015-12-02

Notes:
    
**/ 

package com.microsoft.z3;

/**
 * Finite-domain expressions
 **/
public class FiniteDomainExpr<R> extends Expr<FiniteDomainSort<R>>
{
    /**
     * Constructor for FiniteDomainExpr
     * @throws Z3Exception on error
     **/
    FiniteDomainExpr(Context ctx, long obj)
    {
        super(ctx, obj);
    }
}
