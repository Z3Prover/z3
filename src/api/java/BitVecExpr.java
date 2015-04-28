/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    BitVecExpr.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/

package com.microsoft.z3;

/**
 * Bit-vector expressions
 **/
public class BitVecExpr extends Expr
{

    /**
     * The size of the sort of a bit-vector term.
     * @throws Z3Exception 
     * @throws Z3Exception on error
     * @return an int
     **/
    public int getSortSize()
    {
        return ((BitVecSort) getSort()).getSize();
    }

    /**
     * Constructor for BitVecExpr
     **/
    BitVecExpr(Context ctx, long obj)
    {
        super(ctx, obj);
    }
}
