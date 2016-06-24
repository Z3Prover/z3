/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    Probe.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

/**
 * Probes are used to inspect a goal (aka problem) and collect information that
 * may be used to decide which solver and/or preprocessing step will be used.
 * The complete list of probes may be obtained using the procedures
 * {@code Context.NumProbes} and {@code Context.ProbeNames}. It may
 * also be obtained using the command {@code (help-tactic)} in the SMT 2.0
 * front-end.
 **/
public class Probe extends Z3Object {
    /**
     * Execute the probe over the goal.
     * 
     * @return A probe always produce a double value. "Boolean" probes return
     *         0.0 for false, and a value different from 0.0 for true.
     * @throws Z3Exception 
     **/
    public double apply(Goal g)
    {
        getContext().checkContextMatch(g);
        return Native.probeApply(getContext().nCtx(), getNativeObject(),
                g.getNativeObject());
    }

    Probe(Context ctx, long obj)
    {
        super(ctx, obj);
    }

    Probe(Context ctx, String name) {
        super(ctx, Native.mkProbe(ctx.nCtx(), name));
    }

    @Override
    void incRef() {
        Native.probeIncRef(getContext().nCtx(), getNativeObject());
    }

    @Override
    void addToReferenceQueue() {
        getContext().getProbeDRQ().storeReference(getContext(), this);
    }
}
