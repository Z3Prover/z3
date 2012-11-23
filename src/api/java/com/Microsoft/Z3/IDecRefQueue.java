/**
 * This file was automatically generated from IDecRefQueue.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;

/* using System; */
/* using System.Collections; */
/* using System.Collections.Generic; */
/* using System.Threading; */

    abstract class IDecRefQueue
    {

        private void ObjectInvariant()
        {
            
        }
        

        protected Object m_lock = new Object();
        protected List<Long> m_queue = new List<Long>();
        final long m_move_limit = 1024;

        public abstract void IncRef(Context ctx, long obj);
        public abstract void DecRef(Context ctx, long obj);

        public void IncAndClear(Context ctx, long o)
        {
            

            IncRef(ctx, o);
            if (m_queue.Count >= m_move_limit) Clear(ctx);
        }

        public void Add(long o)
        {
            if (o == 0) return;

            synchronized (m_lock)
            {
                m_queue.Add(o);
            }
        }

        public void Clear(Context ctx)
        {
            

            synchronized (m_lock)
            {
                for (Iterator o = m_queue.iterator(); o.hasNext(); )
                    DecRef(ctx, o);
                m_queue.Clear();
            }
        }
    }

    abstract class DecRefQueueContracts extends IDecRefQueue
    {
        public void IncRef(Context ctx, long obj)
        {
            
        }

        public void DecRef(Context ctx, long obj)
        {
            
        }
    }
