/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    FuncInterpEntryDecRefQueue.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/

package com.microsoft.z3;

class FuncInterpEntryDecRefQueue extends IDecRefQueue
{
    public FuncInterpEntryDecRefQueue() 
    {
        super();
    }

    public FuncInterpEntryDecRefQueue(int move_limit) 
    {
        super(move_limit);
    }

    protected void incRef(Context ctx, long obj)
    {
        try
        {
            Native.funcEntryIncRef(ctx.nCtx(), obj);
        } catch (Z3Exception e)
        {
            // OK.
        }
    }

    protected void decRef(Context ctx, long obj)
    {
        try
        {
            Native.funcEntryDecRef(ctx.nCtx(), obj);
        } catch (Z3Exception e)
        {
            // OK.
        }
    }
};
