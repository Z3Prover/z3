/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    ProbeDecRefQueue.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

class ProbeDecRefQueue extends IDecRefQueue<Probe>
{
    public ProbeDecRefQueue() 
    {
        super();
    }

    @Override
    protected void decRef(Context ctx, long obj)
    {
        Native.probeDecRef(ctx.nCtx(), obj);
    }
};
