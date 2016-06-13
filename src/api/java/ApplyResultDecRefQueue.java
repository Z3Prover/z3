/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    ApplyResultDecRefQueue.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/

package com.microsoft.z3;

class ApplyResultDecRefQueue extends IDecRefQueue<ApplyResult>
{
    public ApplyResultDecRefQueue() 
    {
        super();
    }

    @Override
    protected void decRef(Context ctx, long obj) {
        Native.applyResultDecRef(ctx.nCtx(), obj);
    }
};
