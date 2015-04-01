/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    SolverDecRefQueue.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

class SolverDecRefQueue extends IDecRefQueue
{
    public SolverDecRefQueue() { super(); }
    
    public SolverDecRefQueue(int move_limit) 
    {
        super(move_limit);
    }

    protected void incRef(Context ctx, long obj)
    {
        try
        {
            Native.solverIncRef(ctx.nCtx(), obj);
        } catch (Z3Exception e)
        {
            // OK.
        }
    }

    protected void decRef(Context ctx, long obj)
    {
        try
        {
            Native.solverDecRef(ctx.nCtx(), obj);
        } catch (Z3Exception e)
        {
            // OK.
        }
    }
};
