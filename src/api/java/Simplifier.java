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
        getContext().getSimplifierDRQ().storeReference(getContext(), this);
    }
}	