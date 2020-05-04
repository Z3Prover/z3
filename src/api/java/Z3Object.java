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
public abstract class Z3Object {

    private final Context m_ctx;
    private final long m_n_obj;

    Z3Object(Context ctx, long obj) {
        m_ctx = ctx;
        checkNativeObject(obj);
        m_n_obj = obj;
        incRef();
        addToReferenceQueue();
    }

    /**
     * Add to ReferenceQueue for tracking reachability on the object and
     * decreasing the reference count when the object is no longer reachable.
     */
    abstract void addToReferenceQueue();

    /**
     * Increment reference count on {@code this}.
     */
    abstract void incRef();

    /**
     * This function is provided for overriding, and a child class
     * can insert consistency checks on {@code obj}.
     *
     * @param obj Z3 native object.
     */
    void checkNativeObject(long obj) {}

    long getNativeObject()
    {
        return m_n_obj;
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

    public static long[] arrayToNative(Z3Object[] a)
    {
        if (a == null)
            return null;
        long[] an = new long[a.length];
        for (int i = 0; i < a.length; i++)
            an[i] = (a[i] == null) ? 0 : a[i].getNativeObject();
        return an;
    }

    public static int arrayLength(Z3Object[] a)
    {
        return (a == null) ? 0 : a.length;
    }
}
