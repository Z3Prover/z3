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
            if (mNObj != IntPtr.Zero)
            {
                DecRef(mNObj);
                mNObj = IntPtr.Zero;                
            }

            if (mCtx != null)
            {
                mCtx.refCount--;
                if (mCtx.refCount == 0)
                    GC.ReRegisterForFinalize(mCtx);
                mCtx = null;
            }

            GC.SuppressFinalize(this);
        }

        
        private void ObjectInvariant()
        {
            
        }


        private Context mCtx = null;
        private IntPtr mNObj = IntPtr.Zero;

        Z3Object(Context ctx)
        {
            

            ctx.refCount++;
            mCtx = ctx;
        }

        Z3Object(Context ctx, IntPtr obj)
        {
            

            ctx.refCount++;
            mCtx = ctx;
            IncRef(obj);
            mNObj = obj;
        }

        void IncRef(IntPtr o) { }
        void DecRef(IntPtr o) { }

        void CheckNativeObject(IntPtr obj) { }

        IntPtr NativeObject
        {
            get { return mNObj; }
            set
            {
                if (value != IntPtr.Zero) { CheckNativeObject(value); IncRef(value); }
                if (mNObj != IntPtr.Zero) { DecRef(mNObj); }
                mNObj = value;
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
                
                return mCtx; 
            }            
        }

        static IntPtr[] ArrayToNative(Z3Object[] a)
        {
            
            

            if (a == null) return null;
            IntPtr[] an = new IntPtr[a.Length];
            for (Integer i = 0; i < a.Length; i++)
                if (a[i] != null) an[i] = a[i].NativeObject;
            return an;
        }

        static Integer ArrayLength(Z3Object[] a)
        {
            return (a == null)?0:(Integer)a.Length;
        }
    }
