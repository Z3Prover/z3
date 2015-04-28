/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    ParamDescrsDecRefQueue.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

class ParamDescrsDecRefQueue extends IDecRefQueue
{
    public ParamDescrsDecRefQueue() 
    {
        super();
    }

    public ParamDescrsDecRefQueue(int move_limit) 
    {
        super(move_limit);
    }

    protected void incRef(Context ctx, long obj)
    {
        try
        {
            Native.paramDescrsIncRef(ctx.nCtx(), obj);
        } catch (Z3Exception e)
        {
            // OK.
        }
    }

    protected void decRef(Context ctx, long obj)
    {
        try
        {
            Native.paramDescrsDecRef(ctx.nCtx(), obj);
        } catch (Z3Exception e)
        {
            // OK.
        }
    }
};
