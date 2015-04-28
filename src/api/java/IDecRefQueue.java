/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    IDecRefQueue.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/

package com.microsoft.z3;

import java.util.LinkedList;

public abstract class IDecRefQueue
{
    protected Object m_lock = new Object();
    protected LinkedList<Long> m_queue = new LinkedList<Long>();
    protected int m_move_limit;

    protected IDecRefQueue() 
	{
    	m_move_limit = 1024;
    }

    protected IDecRefQueue(int move_limit) 
    {
    	m_move_limit = move_limit;
    }
 
    public void setLimit(int l) { m_move_limit = l; }
 
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
