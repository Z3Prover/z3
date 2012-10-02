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

using System;
using System.Collections;
using System.Collections.Generic;
using System.Threading;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{    
    [ContractClass(typeof(DecRefQueueContracts))]
    internal abstract class DecRefQueue
    {
        #region Object invariant

        [ContractInvariantMethod]
        private void ObjectInvariant()
        {
            Contract.Invariant(this.m_queue != null);
        }
        
        #endregion

        readonly internal protected Object m_lock = new Object();
        readonly internal protected List<IntPtr> m_queue = new List<IntPtr>();
        internal const uint m_move_limit = 1024;

        public abstract void IncRef(Context ctx, IntPtr obj);
        public abstract void DecRef(Context ctx, IntPtr obj);

        public void IncAndClear(Context ctx, IntPtr o)
        {
            Contract.Requires(ctx != null);

            IncRef(ctx, o);
            if (m_queue.Count >= m_move_limit) Clear(ctx);
        }

        public void Add(IntPtr o)
        {
            if (o == IntPtr.Zero) return;

            lock (m_lock)
            {
                m_queue.Add(o);
            }
        }

        public void Clear(Context ctx)
        {
            Contract.Requires(ctx != null);

            lock (m_lock)
            {
                foreach (IntPtr o in m_queue)
                    DecRef(ctx, o);
                m_queue.Clear();
            }
        }
    }

    [ContractClassFor(typeof(DecRefQueue))]
    abstract class DecRefQueueContracts : DecRefQueue
    {
        public override void IncRef(Context ctx, IntPtr obj)
        {
            Contract.Requires(ctx != null);
        }

        public override void DecRef(Context ctx, IntPtr obj)
        {
            Contract.Requires(ctx != null);
        }
    }
}
