/**
 * This file was automatically generated from IDecRefQueue.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

import java.util.LinkedList;

abstract class IDecRefQueue
{
	protected Object m_lock = new Object();
	protected LinkedList<Long> m_queue = new LinkedList<Long>();
	protected final int m_move_limit = 1024;

	protected abstract void incRef(Context ctx, long obj);

	protected abstract void decRef(Context ctx, long obj);

	protected void incAndClear(Context ctx, long o)
	{
		incRef(ctx, o);
		if (m_queue.size() >= m_move_limit)
			clear(ctx);
	}

	protected void add(long o)
	{
		if (o == 0)
			return;

		synchronized (m_lock)
		{
			m_queue.add(o);
		}
	}

	protected void clear(Context ctx)
	{
		synchronized (m_lock)
		{
			for (Long o : m_queue)
				decRef(ctx, o);
			m_queue.clear();
		}
	}
}
