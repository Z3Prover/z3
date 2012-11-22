/**
 * This file was automatically generated from DecRefQUeue.cs 
 **/

package com.Microsoft.Z3;

/* using System; */
/* using System.Collections; */
/* using System.Collections.Generic; */
/* using System.Threading; */

    abstract class DecRefQueue

        private void ObjectInvariant()
            
        

        readonly protected Object mLock = new Object();
        readonly protected List<IntPtr> mQueue = new List<IntPtr>();
        const Integer mMoveLimit = 1024;

        public abstract void IncRef(Context ctx, IntPtr obj);
        public abstract void DecRef(Context ctx, IntPtr obj);

        public void IncAndClear(Context ctx, IntPtr o)
            

            IncRef(ctx, o);
            if (mQueue.Count >= mMoveLimit) Clear(ctx);

        public void Add(IntPtr o)
            if (o == IntPtr.Zero) return;

            lock (mLock)
                mQueue.Add(o);

        public void Clear(Context ctx)
            

            lock (mLock)
                for (IntPtr.Iterator o = mQueue.iterator(); o.hasNext(); )
                    DecRef(ctx, o);
                mQueue.Clear();

    abstract class DecRefQueueContracts : DecRefQueue
        public void IncRef(Context ctx, IntPtr obj)
            

        public void DecRef(Context ctx, IntPtr obj)
            
