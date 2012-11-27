/**
 * Copyright (c) 2012 Microsoft Corporation
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

class StatisticsDecRefQueue extends IDecRefQueue
{
    public void IncRef(Context ctx, long obj)
    {
	Native.statsIncRef(ctx.nCtx(), obj);
    }
    
    public void DecRef(Context ctx, long obj)
    {
	Native.statsDecRef(ctx.nCtx(), obj);
    }
};
