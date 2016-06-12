/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    Tactic.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

/**
 * Tactics are the basic building block for creating custom solvers for specific
 * problem domains. The complete list of tactics may be obtained using
 * {@code Context.NumTactics} and {@code Context.TacticNames}. It may
 * also be obtained using the command {@code (help-tactic)} in the SMT 2.0
 * front-end.
 **/
public class Tactic extends Z3Object {
    /**
     * A string containing a description of parameters accepted by the tactic.
     **/
    public String getHelp()
    {
        return Native.tacticGetHelp(getContext().nCtx(), getNativeObject());
    }

    /**
     * Retrieves parameter descriptions for Tactics.
     * @throws Z3Exception 
     **/
    public ParamDescrs getParameterDescriptions()
    {
        return new ParamDescrs(getContext(), Native.tacticGetParamDescrs(getContext()
                .nCtx(), getNativeObject()));
    }

    /**
     * Execute the tactic over the goal.
     * @throws Z3Exception 
     **/
    public ApplyResult apply(Goal g)
    {    
        return apply(g, null);
    }

    /**
     * Execute the tactic over the goal.
     * @throws Z3Exception 
     **/
    public ApplyResult apply(Goal g, Params p)
    {
        getContext().checkContextMatch(g);
        if (p == null)
            return new ApplyResult(getContext(), Native.tacticApply(getContext()
                    .nCtx(), getNativeObject(), g.getNativeObject()));
        else
        {
            getContext().checkContextMatch(p);
            return new ApplyResult(getContext(),
                    Native.tacticApplyEx(getContext().nCtx(), getNativeObject(),
                            g.getNativeObject(), p.getNativeObject()));
        }
    }

    /**
     * Creates a solver that is implemented using the given tactic. 
     * @see Context#mkSolver(Tactic)
     * @throws Z3Exception 
     **/
    public Solver getSolver()
    {
        return getContext().mkSolver(this);
    }

    Tactic(Context ctx, long obj)
    {
        super(ctx, obj);
    }

    Tactic(Context ctx, String name)
    {
        super(ctx, Native.mkTactic(ctx.nCtx(), name));
    }

    @Override
    void incRef() {
        Native.tacticIncRef(getContext().nCtx(), getNativeObject());
    }

    @Override
    void addToReferenceQueue() {
        getContext().getTacticDRQ().storeReference(getContext(), this);
    }
}
