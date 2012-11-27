/**
 * This file was automatically generated from IDecRefQueue.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.Microsoft.Z3;

import java.util.*;

abstract class IDecRefQueue
{
	protected Object m_lock = new Object();
	protected LinkedList<Long> m_queue = new LinkedList<Long>();
	final int m_move_limit = 1024;

	public abstract void IncRef(Context ctx, long obj);

	public abstract void DecRef(Context ctx, long obj);

	public void IncAndClear(Context ctx, long o)
	{
		IncRef(ctx, o);
		if (m_queue.size() >= m_move_limit)
			Clear(ctx);
	}

	public void Add(long o)
	{
		if (o == 0)
			return;

		synchronized (m_lock)
		{
			m_queue.add(o);
		}
	}

	public void Clear(Context ctx)
	{
		synchronized (m_lock)
		{
			for (Long o : m_queue)
				DecRef(ctx, o);
			m_queue.clear();
		}
	}
}
