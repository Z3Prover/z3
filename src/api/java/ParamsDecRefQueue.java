/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    ParamDecRefQueue.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

class ParamsDecRefQueue extends IDecRefQueue<Params> {
    public ParamsDecRefQueue() 
    {
        super();
    }

    @Override
    protected void decRef(Context ctx, long obj) {
        Native.paramsDecRef(ctx.nCtx(), obj);
    }
}
