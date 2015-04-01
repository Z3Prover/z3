/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    AstMapDecRefQueue.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/

package com.microsoft.z3;

class ASTMapDecRefQueue extends IDecRefQueue
{
    public ASTMapDecRefQueue() 
    {
        super();
    }

    public ASTMapDecRefQueue(int move_limit) 
    {
        super(move_limit);
    }

    protected void incRef(Context ctx, long obj)
    {
        try
        {
            Native.astMapIncRef(ctx.nCtx(), obj);
        } catch (Z3Exception e)
        {
            // OK.
        }
    }

    protected void decRef(Context ctx, long obj)
    {
        try
        {
            Native.astMapDecRef(ctx.nCtx(), obj);
        } catch (Z3Exception e)
        {
            // OK.
        }
    }
};
