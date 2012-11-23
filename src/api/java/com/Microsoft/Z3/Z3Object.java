/**
 * This file was automatically generated from Z3Object.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;

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
            if (m_n_obj != 0)
            {
                DecRef(m_n_obj);
                m_n_obj = 0;                
            }

            if (m_ctx != null)
            {
                m_ctx.refCount--;
                if (m_ctx.refCount == 0)
                    
                m_ctx = null;
            }

            
        }

        
        private void ObjectInvariant()
        {
            
        }


        private Context m_ctx = null;
        private long m_n_obj = 0;

        Z3Object(Context ctx)
        {
            

            ctx.refCount++;
            m_ctx = ctx;
        }

        Z3Object(Context ctx, long obj)
        {
            

            ctx.refCount++;
            m_ctx = ctx;
            IncRef(obj);
            m_n_obj = obj;
        }

        void IncRef(long o) { }
        void DecRef(long o) { }

        void CheckNativeObject(long obj) { }

                         long NativeObject()  { return m_n_obj; }
                         void setNativeObject(long value) 
            {
                if (value != 0) { CheckNativeObject(value); IncRef(value); }
                if (m_n_obj != 0) { DecRef(m_n_obj); }
                m_n_obj = value;
            }

        static long GetNativeObject(Z3Object s)
        {
            if (s == null) return 0;
            return s.NativeObject();
        }

                 Context Context() 
            {
                
                return m_ctx; 
            }            

        static long[] ArrayToNative(Z3Object[] a)
        {
            
            

            if (a == null) return null;
            long[] an = new long[a.Length];
            for (long i; i < a.Length; i++)
                if (a[i] != null) an[i] = a[i].NativeObject();
            return an;
        }

        static long ArrayLength(Z3Object[] a)
        {
            return (a == null)?0:(long)a.Length;
        }
    }
