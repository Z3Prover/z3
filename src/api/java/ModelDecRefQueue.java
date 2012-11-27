/**
 * Copyright (c) 2012 Microsoft Corporation
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.Microsoft.Z3;

class ModelDecRefQueue extends IDecRefQueue
{
    public void IncRef(Context ctx, long obj)
    {
        Native.modelIncRef(ctx.nCtx(), obj);
    }

    public void DecRef(Context ctx, long obj)
    {
        Native.modelDecRef(ctx.nCtx(), obj);
    }
};
