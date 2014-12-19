/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    Pattern.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

/**
 * Patterns comprise a list of terms. The list should be non-empty. If the list
 * comprises of more than one term, it is also called a multi-pattern.
 **/
public class Pattern extends AST
{
    /**
     * The number of terms in the pattern.
     **/
    public int getNumTerms() throws Z3Exception
    {
        return Native.getPatternNumTerms(getContext().nCtx(), getNativeObject());
    }

    /**
     * The terms in the pattern.
     * 
     * @throws Z3Exception
     **/
    public Expr[] getTerms() throws Z3Exception
    {

        int n = getNumTerms();
        Expr[] res = new Expr[n];
        for (int i = 0; i < n; i++)
            res[i] = Expr.create(getContext(),
                    Native.getPattern(getContext().nCtx(), getNativeObject(), i));
        return res;
    }

    /**
     * A string representation of the pattern.
     **/
    public String toString()
    {
        try
        {
            return Native.patternToString(getContext().nCtx(), getNativeObject());
        } catch (Z3Exception e)
        {
            return "Z3Exception: " + e.getMessage();
        }
    }

    Pattern(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }
}
