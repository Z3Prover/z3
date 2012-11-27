/**
 * Copyright (c) 2012 Microsoft Corporation
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.Microsoft.Z3;

public class ASTDecRefQueue extends IDecRefQueue
{
	public void IncRef(Context ctx, long obj)
	{
		Native.incRef(ctx.nCtx(), obj);
	}

	public void DecRef(Context ctx, long obj)
	{
		Native.decRef(ctx.nCtx(), obj);
	}
};
