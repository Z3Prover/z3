/**
 * Copyright (c) 2012 Microsoft Corporation
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

class FuncInterpEntryDecRefQueue extends IDecRefQueue
{
    public void IncRef(Context ctx, long obj)
    {
        try
        {
            Native.funcEntryIncRef(ctx.nCtx(), obj);
        } catch (Z3Exception e)
        {
            // OK.
        }
    }

    public void DecRef(Context ctx, long obj)
    {
        try
        {
            Native.funcEntryDecRef(ctx.nCtx(), obj);
        } catch (Z3Exception e)
        {
            // OK.
        }
    }
};
