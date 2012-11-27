/**
 * Copyright (c) 2012 Microsoft Corporation
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

class ParamsDecRefQueue extends IDecRefQueue
{
    public void IncRef(Context ctx, long obj)
    {
        Native.paramsIncRef(ctx.nCtx(), obj);
    }

    public void DecRef(Context ctx, long obj)
    {
        Native.paramsDecRef(ctx.nCtx(), obj);
    }
};
