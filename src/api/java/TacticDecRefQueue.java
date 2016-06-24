/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    TacticDecRefQueue.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

class TacticDecRefQueue extends IDecRefQueue<Tactic> {
    public TacticDecRefQueue() 
    {
        super();
    }

    @Override
    protected void decRef(Context ctx, long obj)
    {
        Native.tacticDecRef(ctx.nCtx(), obj);
    }
}
