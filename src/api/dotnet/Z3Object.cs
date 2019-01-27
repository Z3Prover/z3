﻿/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    Z3Object.cs

Abstract:

    Z3 Managed API: Internal Z3 Objects

Author:

    Christoph Wintersteiger (cwinter) 2012-03-21

Notes:
    
--*/

using System.Diagnostics;
using System;
using System.Threading;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Z3
{
    /// <summary>
    /// Internal base class for interfacing with native Z3 objects.
    /// Should not be used externally.
    /// </summary>
    public class Z3Object : IDisposable
    {
        /// <summary>
        /// Finalizer.
        /// </summary>
        ~Z3Object()
        {
            Dispose();            
        }

        /// <summary>
        /// Disposes of the underlying native Z3 object.
        /// </summary>
        public void Dispose()
        {
            if (m_n_obj != IntPtr.Zero)
            {
                DecRef(m_n_obj);
                m_n_obj = IntPtr.Zero;                
            }

            if (m_ctx != null)
            {
                if (Interlocked.Decrement(ref m_ctx.refCount) == 0)
                    GC.ReRegisterForFinalize(m_ctx);
                m_ctx = null;
            }

            GC.SuppressFinalize(this);
        }

        #region Object Invariant
        
        private void ObjectInvariant()
        {
            Debug.Assert(this.m_ctx != null);
        }

        #endregion

        #region Internal
        private Context m_ctx = null;
        private IntPtr m_n_obj = IntPtr.Zero;

        internal Z3Object(Context ctx)
        {
            Debug.Assert(ctx != null);

            Interlocked.Increment(ref ctx.refCount);
            m_ctx = ctx;
        }

        internal Z3Object(Context ctx, IntPtr obj)
        {
            Debug.Assert(ctx != null);

            Interlocked.Increment(ref ctx.refCount);
            m_ctx = ctx;
            IncRef(obj);
            m_n_obj = obj;
        }

        internal virtual void IncRef(IntPtr o) { }
        internal virtual void DecRef(IntPtr o) { }

        internal virtual void CheckNativeObject(IntPtr obj) { }

        internal virtual IntPtr NativeObject
        {
            get { return m_n_obj; }
            set
            {
                if (value != IntPtr.Zero) { CheckNativeObject(value); IncRef(value); }
                if (m_n_obj != IntPtr.Zero) { DecRef(m_n_obj); }
                m_n_obj = value;
            }
        }

        internal static IntPtr GetNativeObject(Z3Object s)
        {
            if (s == null) return new IntPtr();
            return s.NativeObject;
        }

        internal Context Context
        {
            get 
            {
                return m_ctx; 
            }            
        }

        internal static IntPtr[] ArrayToNative(Z3Object[] a)
        {

            if (a == null) return null;
            IntPtr[] an = new IntPtr[a.Length];
            for (uint i = 0; i < a.Length; i++)
                if (a[i] != null) an[i] = a[i].NativeObject;
            return an;
        }

        internal static IntPtr[] EnumToNative<T>(IEnumerable<T> a) where T : Z3Object
        {

            if (a == null) return null;
            IntPtr[] an = new IntPtr[a.Count()];
            int i = 0;
            foreach (var ai in a)
            {
                if (ai != null) an[i] = ai.NativeObject;
                ++i;
            }
            return an;
        }

        internal static uint ArrayLength(Z3Object[] a)
        {
            return (a == null)?0:(uint)a.Length;
        }
        #endregion
    }
}
