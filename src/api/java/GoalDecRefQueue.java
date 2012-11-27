/**
 * Copyright (c) 2012 Microsoft Corporation
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.Microsoft.Z3;

class GoalDecRefQueue extends IDecRefQueue
{
	public void IncRef(Context ctx, long obj)
	{
		Native.goalIncRef(ctx.nCtx(), obj);
	}

	public void DecRef(Context ctx, long obj)
	{
		Native.goalDecRef(ctx.nCtx(), obj);
	}
};
