/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    Z3Object.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

/**
 * Internal base class for interfacing with native Z3 objects. Should not be
 * used externally.
 **/
public class Z3Object extends IDisposable
{
    /**
     * Finalizer.
     **/
    protected void finalize() throws Z3Exception
    {
        dispose();
    }

    /**
     * Disposes of the underlying native Z3 object.
     **/
    public void dispose() throws Z3Exception
    {
        if (m_n_obj != 0)
        {
            decRef(m_n_obj);
            m_n_obj = 0;
        }

        if (m_ctx != null)
        {
            m_ctx.m_refCount--;
            m_ctx = null;
        }
    }

    private Context m_ctx = null;
    private long m_n_obj = 0;

    Z3Object(Context ctx)
    {
        ctx.m_refCount++;
        m_ctx = ctx;
    }

    Z3Object(Context ctx, long obj) throws Z3Exception
    {
        ctx.m_refCount++;
        m_ctx = ctx;
        incRef(obj);
        m_n_obj = obj;
    }

    void incRef(long o) throws Z3Exception
    {
    }

    void decRef(long o) throws Z3Exception
    {
    }

    void checkNativeObject(long obj) throws Z3Exception
    {
    }

    long getNativeObject()
    {
        return m_n_obj;
    }

    void setNativeObject(long value) throws Z3Exception
    {
        if (value != 0)
        {
            checkNativeObject(value);
            incRef(value);
        }
        if (m_n_obj != 0)
        {
            decRef(m_n_obj);
        }
        m_n_obj = value;
    }

    static long getNativeObject(Z3Object s)
    {
        if (s == null)
            return 0;
        return s.getNativeObject();
    }

    Context getContext()
    {
        return m_ctx;
    }

    static long[] arrayToNative(Z3Object[] a)
    {
        if (a == null)
            return null;
        long[] an = new long[a.length];
        for (int i = 0; i < a.length; i++)
        an[i] = (a[i] == null) ? 0 : a[i].getNativeObject();
        return an;
    }

    static int arrayLength(Z3Object[] a)
    {
        return (a == null) ? 0 : a.length;
    }
}
