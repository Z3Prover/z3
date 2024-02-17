/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    Simplifiers.cs

Abstract:

    Z3 Managed API: Simplifiers

Author:

    Christoph Wintersteiger (cwinter) 2012-03-21

--*/

package com.microsoft.z3;


import java.lang.ref.ReferenceQueue;

public class Simplifier extends Z3Object {
    /*
     * A string containing a description of parameters accepted by the simplifier.
     */

    public String getHelp()
    {
	return Native.simplifierGetHelp(getContext().nCtx(), getNativeObject());
    }

    /*
     * Retrieves parameter descriptions for Simplifiers.
     */
    public ParamDescrs getParameterDescriptions() {
        return new ParamDescrs(getContext(), Native.simplifierGetParamDescrs(getContext().nCtx(), getNativeObject()));
    }

    Simplifier(Context ctx, long obj)
    {
	super(ctx, obj);
    }

    Simplifier(Context ctx, String name)
    {
	super(ctx, Native.mkSimplifier(ctx.nCtx(), name));
    }

    @Override
    void incRef()
    {
	Native.simplifierIncRef(getContext().nCtx(), getNativeObject());
    }

    @Override
    void addToReferenceQueue() {
        getContext().getReferenceQueue().storeReference(this, SimplifierRef::new);
    }

    private static class SimplifierRef extends Z3ReferenceQueue.Reference<Simplifier> {

        private SimplifierRef(Simplifier referent, ReferenceQueue<Z3Object> q) {
            super(referent, q);
        }

        @Override
        void decRef(Context ctx, long z3Obj) {
            Native.simplifierDecRef(ctx.nCtx(), z3Obj);
        }
    }
}