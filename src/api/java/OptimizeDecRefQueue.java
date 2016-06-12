/**
Copyright (c) 2012-2015 Microsoft Corporation
   
Module Name:

    OptimizeDecRefQueue.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

class OptimizeDecRefQueue extends IDecRefQueue<Optimize> {
    public OptimizeDecRefQueue() 
    {
        super();
    }

    public OptimizeDecRefQueue(int move_limit) 
    {
        super(move_limit);
    }

    @Override
    protected void decRef(Context ctx, long obj) {
        Native.optimizeDecRef(ctx.nCtx(), obj);
    }
};
