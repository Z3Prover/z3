/**
 * Copyright (c) 2012 Microsoft Corporation
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.Microsoft.Z3;

class FuncInterpEntryDecRefQueue extends IDecRefQueue
{
	public void IncRef(Context ctx, long obj)
	{
		Native.funcEntryIncRef(ctx.nCtx(), obj);
	}

	public void DecRef(Context ctx, long obj)
	{
		Native.funcEntryDecRef(ctx.nCtx(), obj);
	}
};
