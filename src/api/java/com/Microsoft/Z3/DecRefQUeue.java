/**
 * This file was automatically generated from DecRefQUeue.cs 
 **/

package com.Microsoft.Z3;

/* using System; */
/* using System.Collections; */
/* using System.Collections.Generic; */
/* using System.Threading; */

    abstract class DecRefQueue
    {

        private void ObjectInvariant()
        {
            
        }
        

        protected Object m_lock = new Object();
        protected List<IntPtr> m_queue = new List<IntPtr>();
        final long m_move_limit = 1024;

        public abstract void IncRef(Context ctx, IntPtr obj);
        public abstract void DecRef(Context ctx, IntPtr obj);

        public void IncAndClear(Context ctx, IntPtr o)
        {
            

            IncRef(ctx, o);
            if (m_queue.Count >= m_move_limit) Clear(ctx);
        }

        public void Add(IntPtr o)
        {
            if (o == IntPtr.Zero) return;

            synchronized (m_lock)
            {
                m_queue.Add(o);
            }
        }

        public void Clear(Context ctx)
        {
            

            synchronized (m_lock)
            {
                for (IntPtr.Iterator o = m_queue.iterator(); o.hasNext(); )
                    DecRef(ctx, o);
                m_queue.Clear();
            }
        }
    }

    abstract class DecRefQueueContracts extends DecRefQueue
    {
        public void IncRef(Context ctx, IntPtr obj)
        {
            
        }

        public void DecRef(Context ctx, IntPtr obj)
        {
            
        }
    }
