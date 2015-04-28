/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    ApplyResultDecRefQueue.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/

package com.microsoft.z3;

class ApplyResultDecRefQueue extends IDecRefQueue
{
    public ApplyResultDecRefQueue() 
    {
        super();
    }

    public ApplyResultDecRefQueue(int move_limit) 
    {
        super(move_limit);
    }

    protected void incRef(Context ctx, long obj)
    {
        try
        {
            Native.applyResultIncRef(ctx.nCtx(), obj);
        } catch (Z3Exception e)
        {
            // OK.
        }
    }

    protected void decRef(Context ctx, long obj)
    {
        try
        {
            Native.applyResultDecRef(ctx.nCtx(), obj);
        } catch (Z3Exception e)
        {
            // OK.
        }
    }
};
