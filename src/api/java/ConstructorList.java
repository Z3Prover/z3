/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    ConstructorList.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/

package com.microsoft.z3;

import java.lang.ref.ReferenceQueue;

/**
 * Lists of constructors
 **/
public class ConstructorList<R> extends Z3Object {

    ConstructorList(Context ctx, long obj)
    {
        super(ctx, obj);
    }

    @Override
    void incRef() {
        // Constructor lists are not reference counted.
    }

    @Override
    void addToReferenceQueue() {
        getContext().getReferenceQueue().storeReference(this, ConstructorListRef::new);
    }

    ConstructorList(Context ctx, Constructor<R>[] constructors)
    {
        super(ctx, Native.mkConstructorList(ctx.nCtx(),
                constructors.length,
                Constructor.arrayToNative(constructors)));
    }

    private static class ConstructorListRef extends Z3ReferenceQueue.Reference<ConstructorList<?>> {

        private ConstructorListRef(ConstructorList<?> referent, ReferenceQueue<Z3Object> q) {
            super(referent, q);
        }

        @Override
        void decRef(Context ctx, long z3Obj) {
            Native.delConstructorList(ctx.nCtx(), z3Obj);
        }
    }
}
