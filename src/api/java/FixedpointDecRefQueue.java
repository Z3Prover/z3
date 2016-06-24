/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    FixedpointDecRefQueue.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

class FixedpointDecRefQueue extends IDecRefQueue<Fixedpoint> {
    public FixedpointDecRefQueue() 
    {
        super();
    }

    @Override
    protected void decRef(Context ctx, long obj)
    {
        Native.fixedpointDecRef(ctx.nCtx(), obj);
    }
};
