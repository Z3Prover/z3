/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    ParamDescrsDecRefQueue.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

class ParamDescrsDecRefQueue extends IDecRefQueue<ParamDescrs>
{
    public ParamDescrsDecRefQueue() 
    {
        super();
    }

    public ParamDescrsDecRefQueue(int move_limit) {
        super(move_limit);
    }

    @Override
    protected void decRef(Context ctx, long obj)
    {
        Native.paramDescrsDecRef(ctx.nCtx(), obj);
    }
};
