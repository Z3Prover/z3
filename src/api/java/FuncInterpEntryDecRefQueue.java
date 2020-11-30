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

class FuncInterpEntryDecRefQueue extends IDecRefQueue<FuncInterp.Entry<?>> {
    public FuncInterpEntryDecRefQueue() 
    {
        super();
    }

    @Override
    protected void decRef(Context ctx, long obj) {
        Native.funcEntryDecRef(ctx.nCtx(), obj);
    }
}
