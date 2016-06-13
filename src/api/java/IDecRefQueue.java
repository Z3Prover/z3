/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    IDecRefQueue.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/

package com.microsoft.z3;

import java.lang.ref.PhantomReference;
import java.lang.ref.Reference;
import java.lang.ref.ReferenceQueue;
import java.util.IdentityHashMap;
import java.util.Map;

public abstract class IDecRefQueue<T extends Z3Object>
{
    private final int m_move_limit;

    // TODO: problem: ReferenceQueue has no API to return length.
    private final ReferenceQueue<T> referenceQueue = new ReferenceQueue<>();
    private int queueSize = 0;
    private final Map<PhantomReference<T>, Long> referenceMap =
            new IdentityHashMap<>();

    protected IDecRefQueue() 
	{
    	m_move_limit = 1024;
    }

    protected IDecRefQueue(int move_limit) 
    {
    	m_move_limit = move_limit;
    }

    /**
     * An implementation of this method should decrement the reference on a
     * given native object.
     * This function should always be called on the {@code ctx} thread.
     *
     * @param ctx Z3 context.
     * @param obj Pointer to a Z3 object.
     */
    protected abstract void decRef(Context ctx, long obj);

    public void storeReference(Context ctx, T obj) {
        PhantomReference<T> ref = new PhantomReference<>(obj, referenceQueue);
        referenceMap.put(ref, obj.getNativeObject());

        // TODO: use move_limit, somehow get the size of referenceQueue.
        clear(ctx);
    }

    protected void clear(Context ctx)
    {
        Reference<? extends T> ref;
        while ((ref = referenceQueue.poll()) != null) {
            long z3ast = referenceMap.remove(ref);
            decRef(ctx, z3ast);
        }
    }
}
