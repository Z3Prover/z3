/**
 * This file was automatically generated from IDecRefQueue.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;
import com.Microsoft.Z3.Enumerations.*;

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
        protected LinkedList<Long> m_queue = new LinkedList<Long>();
        final int m_move_limit = 1024;

        public abstract void IncRef(Context ctx, long obj);
        public abstract void DecRef(Context ctx, long obj);

        public void IncAndClear(Context ctx, long o)
        {
            

            IncRef(ctx, o);
            if (m_queue.size() >= m_move_limit) Clear(ctx);
        }

        public void Add(long o)
        {
            if (o == 0) return;

            synchronized (m_lock)
            {
                m_queue.add(o);
            }
        }

        public void Clear(Context ctx)
        {
            

            synchronized (m_lock)
            {
                for (Long o: m_queue)
                    DecRef(ctx, o);
                m_queue.clear();
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
