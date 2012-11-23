/**
 * This file was automatically generated from Z3Object.cs 
 **/

package com.Microsoft.Z3;

/* using System; */

    /**
     * Internal base class for interfacing with native Z3 objects.
     * Should not be used externally.
     **/
    public class Z3Object extends IDisposable
    {
        /**
         * Finalizer.
         **/
        protected void finalize()
        {
            Dispose();            
        }

        /**
         * Disposes of the underlying native Z3 object.
         **/
        public void Dispose()
        {
            if (m_n_obj != IntPtr.Zero)
            {
                DecRef(m_n_obj);
                m_n_obj = IntPtr.Zero;                
            }

            if (m_ctx != null)
            {
                m_ctx.refCount--;
                if (m_ctx.refCount == 0)
                    GC.ReRegisterForFinalize(m_ctx);
                m_ctx = null;
            }

            GC.SuppressFinalize(this);
        }

        
        private void ObjectInvariant()
        {
            
        }


        private Context m_ctx = null;
        private IntPtr m_n_obj = IntPtr.Zero;

        Z3Object(Context ctx)
        {
            

            ctx.refCount++;
            m_ctx = ctx;
        }

        Z3Object(Context ctx, IntPtr obj)
        {
            

            ctx.refCount++;
            m_ctx = ctx;
            IncRef(obj);
            m_n_obj = obj;
        }

        void IncRef(IntPtr o) { }
        void DecRef(IntPtr o) { }

        void CheckNativeObject(IntPtr obj) { }

        IntPtr NativeObject
        {
            get { return m_n_obj; }
            set
            {
                if (value != IntPtr.Zero) { CheckNativeObject(value); IncRef(value); }
                if (m_n_obj != IntPtr.Zero) { DecRef(m_n_obj); }
                m_n_obj = value;
            }
        }

        static IntPtr GetNativeObject(Z3Object s)
        {
            if (s == null) return new IntPtr();
            return s.NativeObject;
        }

        Context Context
        {
            get 
            {
                
                return m_ctx; 
            }            
        }

        static IntPtr[] ArrayToNative(Z3Object[] a)
        {
            
            

            if (a == null) return null;
            IntPtr[] an = new IntPtr[a.Length];
            for (long i = 0; i < a.Length; i++)
                if (a[i] != null) an[i] = a[i].NativeObject;
            return an;
        }

        static long ArrayLength(Z3Object[] a)
        {
            return (a == null)?0:(long)a.Length;
        }
    }
