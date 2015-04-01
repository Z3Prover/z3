/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    ASTDecRefQueue.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/

package com.microsoft.z3;

class ASTDecRefQueue extends IDecRefQueue
{
    public ASTDecRefQueue() 
    {
        super();
    }

    public ASTDecRefQueue(int move_limit) 
    {
        super(move_limit);
    }

    protected void incRef(Context ctx, long obj)
    {
        try
        {
            Native.incRef(ctx.nCtx(), obj);
        } catch (Z3Exception e)
        {
            // OK.
        }
    }

    protected void decRef(Context ctx, long obj)
    {
        try
        {
            Native.decRef(ctx.nCtx(), obj);
        } catch (Z3Exception e)
        {
            // OK.
        }
    }
};
