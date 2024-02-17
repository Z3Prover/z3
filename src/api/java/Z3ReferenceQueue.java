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
import java.lang.ref.ReferenceQueue;

/**
 * A queue to handle management of native memory.
 *
 * <p><b>Mechanics: </b>When an object is created, a so-called {@link PhantomReference}
 * is constructed that is associated with the created object and the reference queue {@code referenceQueue}.
 * Once the object becomes strongly unreachable, the phantom reference gets
 * added by JVM to the {@code referenceQueue}.
 * After each object creation, we iterate through the available objects in
 * {@code referenceQueue} and decrement references for them.
 * <p>
 * In order for this to work, we need to (i) associate to each phantom reference the underlying
 * native object (and its type) that it references and (ii) keep the phantom references themselves alive, so they are not
 * garbage collected before the object they reference.
 * We use a doubly-linked list of custom phantom references, subclasses of {@link Reference}, to achieve this.
 *
 */
class Z3ReferenceQueue {
    private final Context ctx;
    private final ReferenceQueue<Z3Object> referenceQueue = new ReferenceQueue<>();
    private final Reference<?> referenceList = emptyList();

    Z3ReferenceQueue(Context ctx) {
        this.ctx = ctx;
    }

    /**
     * Create and store a new phantom reference.
     */
    <T extends Z3Object> void storeReference(T z3Object, ReferenceConstructor<T> refConstructor) {
        referenceList.insert(refConstructor.construct(z3Object, referenceQueue));
        clear();
    }

    /**
     * Clean all references currently in {@code referenceQueue}.
     */
    private void clear() {
        Reference<?> ref;
        while ((ref = (Reference<?>)referenceQueue.poll()) != null) {
            ref.cleanup(ctx);
        }
    }

    /**
     * Clean all references stored in {@code referenceList},
     * <b>regardless</b> of whether they are in {@code referenceQueue} or not.
     */
    @SuppressWarnings("StatementWithEmptyBody")
    public void forceClear() {
        // Decrement all reference counters
        Reference<?> cur = referenceList.next;
        while (cur.next != null) {
            cur.decRef(ctx, cur.nativePtr);
            cur = cur.next;
        }

        // Bulk-delete the reference list's entries
        referenceList.next = cur;
        cur.prev = referenceList;

        // Empty the reference queue so that there are no living phantom references anymore.
        // This makes sure that all stored phantom references can be GC'd now.
        while (referenceQueue.poll() != null) {}
    }

    private static Reference<?> emptyList() {
        Reference<?> head = new DummyReference();
        Reference<?> tail = new DummyReference();
        head.next = tail;
        tail.prev = head;
        return head;
    }

    // ================================================================================================================

    @FunctionalInterface
    interface ReferenceConstructor<T extends Z3Object> {
        Reference<T> construct(T reference, ReferenceQueue<Z3Object> queue);
    }

    abstract static class Reference<T extends Z3Object> extends PhantomReference<T> {

        private Reference<?> prev;
        private Reference<?> next;
        private final long nativePtr;

        Reference(T referent, ReferenceQueue<Z3Object> q) {
            super(referent, q);
            this.nativePtr = referent != null ? referent.getNativeObject() : 0;
        }

        private void cleanup(Context ctx) {
            decRef(ctx, nativePtr);
            assert (prev != null && next != null);
            prev.next = next;
            next.prev = prev;
        }

        private void insert(Reference<?> ref) {
            assert next != null;
            ref.prev = this;
            ref.next = this.next;
            ref.next.prev = ref;
            next = ref;
        }

        abstract void decRef(Context ctx, long z3Obj);
    }

    private static class DummyReference extends Reference<Z3Object> {

        public DummyReference() {
            super(null, null);
        }

        @Override
        void decRef(Context ctx, long z3Obj) {
            // Should never be called.
            assert false;
        }
    }
}
