/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    ApplyResult.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/

package com.microsoft.z3;

/**
 * ApplyResult objects represent the result of an application of a tactic to a
 * goal. It contains the subgoals that were produced.
 **/
public class ApplyResult extends Z3Object {
    /**
     * The number of Subgoals.
     **/
    public int getNumSubgoals()
    {
        return Native.applyResultGetNumSubgoals(getContext().nCtx(),
                getNativeObject());
    }

    /**
     * Retrieves the subgoals from the ApplyResult.
     * 
     * @throws Z3Exception
     **/
    public Goal[] getSubgoals()
    {
        int n = getNumSubgoals();
        Goal[] res = new Goal[n];
        for (int i = 0; i < n; i++)
            res[i] = new Goal(getContext(), 
                Native.applyResultGetSubgoal(getContext().nCtx(), getNativeObject(), i));
        return res;
    }

    /**
     * A string representation of the ApplyResult.
     **/
    @Override
    public String toString() {
        return Native.applyResultToString(getContext().nCtx(), getNativeObject());
    }

    ApplyResult(Context ctx, long obj)
    {
        super(ctx, obj);
    }

    @Override
    void incRef() {
        Native.applyResultIncRef(getContext().nCtx(), getNativeObject());
    }

    @Override
    void addToReferenceQueue() {
        getContext().getApplyResultDRQ().storeReference(getContext(), this);
    }
}
