/**
 * This file was automatically generated from Probe.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

/**
 * Probes are used to inspect a goal (aka problem) and collect information that
 * may be used to decide which solver and/or preprocessing step will be used.
 * The complete list of probes may be obtained using the procedures
 * <code>Context.NumProbes</code> and <code>Context.ProbeNames</code>. It may
 * also be obtained using the command <code>(help-tactics)</code> in the SMT 2.0
 * front-end.
 **/
public class Probe extends Z3Object
{
    /**
     * Execute the probe over the goal.
     * 
     * @return A probe always produce a double value. "Boolean" probes return
     *         0.0 for false, and a value different from 0.0 for true.
     * @throws Z3Exception 
     **/
    public double apply(Goal g) throws Z3Exception
    {
        getContext().checkContextMatch(g);
        return Native.probeApply(getContext().nCtx(), getNativeObject(),
                g.getNativeObject());
    }

    Probe(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }

    Probe(Context ctx, String name) throws Z3Exception
    {
        super(ctx, Native.mkProbe(ctx.nCtx(), name));
    }

    void incRef(long o) throws Z3Exception
    {
        getContext().probe_DRQ().incAndClear(getContext(), o);
        super.incRef(o);
    }

    void decRef(long o) throws Z3Exception
    {
        getContext().probe_DRQ().add(o);
        super.decRef(o);
    }
}
