/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    FuncInterpDecRefQueue.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

class FuncInterpDecRefQueue extends IDecRefQueue
{
    public FuncInterpDecRefQueue() 
    {
        super();
    }

    public FuncInterpDecRefQueue(int move_limit) 
    {
        super(move_limit);
    }

    protected void incRef(Context ctx, long obj)
    {
        try
        {
            Native.funcInterpIncRef(ctx.nCtx(), obj);
        } catch (Z3Exception e)
        {
            // OK.
        }
    }

    protected void decRef(Context ctx, long obj)
    {
        try
        {
            Native.funcInterpDecRef(ctx.nCtx(), obj);
        } catch (Z3Exception e)
        {
            // OK.
        }
    }
};
