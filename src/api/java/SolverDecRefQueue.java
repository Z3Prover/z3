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

class SolverDecRefQueue extends IDecRefQueue<Solver> {
    public SolverDecRefQueue() { super(); }
    
    @Override
    protected void decRef(Context ctx, long obj) {
        Native.solverDecRef(ctx.nCtx(), obj);
    }
}
