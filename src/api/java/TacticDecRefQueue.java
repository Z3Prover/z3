/**
 * Copyright (c) 2012 Microsoft Corporation
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.Microsoft.Z3;

class TacticDecRefQueue extends IDecRefQueue
{
    public void IncRef(Context ctx, long obj)
    {
        Native.tacticIncRef(ctx.nCtx(), obj);
    }

    public void DecRef(Context ctx, long obj)
    {
        Native.tacticDecRef(ctx.nCtx(), obj);
    }
};
