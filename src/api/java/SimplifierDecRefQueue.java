/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    SimplifierDecRefQueue.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

class SimplifierDecRefQueue extends IDecRefQueue<Simplifier> {
    public SimplifierDecRefQueue() 
    {
        super();
    }

    @Override
    protected void decRef(Context ctx, long obj)
    {
        Native.simplifierDecRef(ctx.nCtx(), obj);
    }
}
