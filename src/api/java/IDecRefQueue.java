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

/**
 * A queue to handle management of native memory.
 *
 * <p><b>Mechanics: </b>once an object is created, a metadata is stored for it in
 * {@code referenceMap}, and a {@link PhantomReference} is created with a
 * reference  to {@code referenceQueue}.
 * Once the object becomes strongly unreachable, the phantom reference gets
 * added by JVM to the {@code referenceQueue}.
 * After each object creation, we iterate through the available objects in
 * {@code referenceQueue} and decrement references for them.
 *
 * @param <T> Type of object stored in queue.
 */
public abstract class IDecRefQueue<T extends Z3Object> {
    private final ReferenceQueue<T> referenceQueue = new ReferenceQueue<>();
    private final Map<PhantomReference<T>, Long> referenceMap =
            new IdentityHashMap<>();

    protected IDecRefQueue() {}

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
        clear(ctx);
    }

    /**
     * Clean all references currently in {@code referenceQueue}.
     */
    protected void clear(Context ctx)
    {
        Reference<? extends T> ref;
        while ((ref = referenceQueue.poll()) != null) {
            long z3ast = referenceMap.remove(ref);
            decRef(ctx, z3ast);
        }
    }

    /**
     * Clean all references stored in {@code referenceMap},
     * <b>regardless</b> of whether they are in {@code referenceMap} or not.
     */
    public void forceClear(Context ctx) {
        for (long ref : referenceMap.values()) {
            decRef(ctx, ref);
        }
    }
}
