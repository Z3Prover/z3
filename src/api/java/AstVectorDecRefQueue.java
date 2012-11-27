/**
 * Copyright (c) 2012 Microsoft Corporation
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.Microsoft.Z3;

class ASTVectorDecRefQueue extends IDecRefQueue
{
	public void IncRef(Context ctx, long obj)
	{
		Native.astVectorIncRef(ctx.nCtx(), obj);
	}

	public void DecRef(Context ctx, long obj)
	{
		Native.astVectorDecRef(ctx.nCtx(), obj);
	}
};
