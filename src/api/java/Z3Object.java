/**
 * This file was automatically generated from Z3Object.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.Microsoft.Z3;

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
        Dispose();
    }

    /**
     * Disposes of the underlying native Z3 object.
     **/
    public void Dispose() throws Z3Exception
    {
        if (m_n_obj != 0)
        {
            DecRef(m_n_obj);
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
        IncRef(obj);
        m_n_obj = obj;
    }

    void IncRef(long o) throws Z3Exception
    {
    }

    void DecRef(long o) throws Z3Exception
    {
    }

    void CheckNativeObject(long obj) throws Z3Exception
    {
    }

    long NativeObject()
    {
        return m_n_obj;
    }

    void setNativeObject(long value) throws Z3Exception
    {
        if (value != 0)
        {
            CheckNativeObject(value);
            IncRef(value);
        }
        if (m_n_obj != 0)
        {
            DecRef(m_n_obj);
        }
        m_n_obj = value;
    }

    static long GetNativeObject(Z3Object s)
    {
        if (s == null)
            return 0;
        return s.NativeObject();
    }

    Context Context()
    {
        return m_ctx;
    }

    static long[] ArrayToNative(Z3Object[] a)
    {
        if (a == null)
            return null;
        long[] an = new long[a.length];
        for (int i = 0; i < a.length; i++)
            if (a[i] != null)
                an[i] = a[i].NativeObject();
        return an;
    }

    static int ArrayLength(Z3Object[] a)
    {
        return (a == null) ? 0 : (int) a.length;
    }
}
