/**
 * Copyright (c) 2012 Microsoft Corporation
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.Microsoft.Z3;

class FixedpointDecRefQueue extends IDecRefQueue
{
	public void IncRef(Context ctx, long obj)
	{
		Native.fixedpointIncRef(ctx.nCtx(), obj);
	}

	public void DecRef(Context ctx, long obj)
	{
		Native.fixedpointDecRef(ctx.nCtx(), obj);
	}
};
