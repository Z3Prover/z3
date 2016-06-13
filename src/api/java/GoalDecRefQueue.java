/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    GoalDecRefQueue.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

class GoalDecRefQueue extends IDecRefQueue<Goal> {
    public GoalDecRefQueue() 
    {
        super();
    }

    @Override
    protected void decRef(Context ctx, long obj) {
            Native.goalDecRef(ctx.nCtx(), obj);
    }
}
