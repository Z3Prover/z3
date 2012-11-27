/**
 * Copyright (c) 2012 Microsoft Corporation
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

class ProbeDecRefQueue extends IDecRefQueue
{
    public void IncRef(Context ctx, long obj)
    {
        Native.probeIncRef(ctx.nCtx(), obj);
    }

    public void DecRef(Context ctx, long obj)
    {
        Native.probeDecRef(ctx.nCtx(), obj);
    }
};
