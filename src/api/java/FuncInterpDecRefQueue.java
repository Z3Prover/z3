/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    FuncInterpDecRefQueue.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

class FuncInterpDecRefQueue extends IDecRefQueue<FuncInterp<?>>
{
    public FuncInterpDecRefQueue() 
    {
        super();
    }

    @Override
    protected void decRef(Context ctx, long obj) {
        Native.funcInterpDecRef(ctx.nCtx(), obj);
    }
};
