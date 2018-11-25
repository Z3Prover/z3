/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    DecRefQueue.cs

Abstract:

    Z3 Managed API: DecRef Queues

Author:

    Christoph Wintersteiger (cwinter) 2012-03-16

Notes:
    
--*/

using System.Diagnostics;
using System;
using System.Collections;
using System.Collections.Generic;
using System.Threading;

namespace Microsoft.Z3
{
    /// <summary>
    /// DecRefQueue interface
    /// </summary>
    public abstract class IDecRefQueue
    {
        #region Object invariant

        private void ObjectInvariant()
        {
            Debug.Assert(this.m_queue != null);
        }

        #endregion

        readonly private Object m_lock = new Object();
        readonly private List<IntPtr> m_queue = new List<IntPtr>();
        private uint m_move_limit;

        internal IDecRefQueue(uint move_limit = 1024)
        {
            m_move_limit = move_limit;
        }

        /// <summary>
        /// Sets the limit on numbers of objects that are kept back at GC collection.
        /// </summary>
        /// <param name="l"></param>
        public void SetLimit(uint l) { m_move_limit = l; }

        internal abstract void IncRef(Context ctx, IntPtr obj);
        internal abstract void DecRef(Context ctx, IntPtr obj);

        internal void IncAndClear(Context ctx, IntPtr o)
        {
            Debug.Assert(ctx != null);

            IncRef(ctx, o);
            if (m_queue.Count >= m_move_limit) Clear(ctx);
        }

        internal void Add(IntPtr o)
        {
            if (o == IntPtr.Zero) return;

            lock (m_lock)
            {
                m_queue.Add(o);
            }
        }

        internal void Clear(Context ctx)
        {
            Debug.Assert(ctx != null);

            lock (m_lock)
            {
                foreach (IntPtr o in m_queue)
                    DecRef(ctx, o);
                m_queue.Clear();
            }
        }
    }

    abstract class DecRefQueueContracts : IDecRefQueue
    {
        internal override void IncRef(Context ctx, IntPtr obj)
        {
            Debug.Assert(ctx != null);
        }

        internal override void DecRef(Context ctx, IntPtr obj)
        {
            Debug.Assert(ctx != null);
        }
    }
}
