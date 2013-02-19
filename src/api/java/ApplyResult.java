/**
 * This file was automatically generated from ApplyResult.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

/**
 * ApplyResult objects represent the result of an application of a tactic to a
 * goal. It contains the subgoals that were produced.
 **/
public class ApplyResult extends Z3Object
{
    /**
     * The number of Subgoals.
     **/
    public int getNumSubgoals() throws Z3Exception
    {
        return Native.applyResultGetNumSubgoals(getContext().nCtx(),
                getNativeObject());
    }

    /**
     * Retrieves the subgoals from the ApplyResult.
     * 
     * @throws Z3Exception
     **/
    public Goal[] getSubgoals() throws Z3Exception
    {
        int n = getNumSubgoals();
        Goal[] res = new Goal[n];
        for (int i = 0; i < n; i++)
            res[i] = new Goal(getContext(), 
                Native.applyResultGetSubgoal(getContext().nCtx(), getNativeObject(), i));
        return res;
    }

    /**
     * Convert a model for the subgoal <paramref name="i"/> into a model for the
     * original goal <code>g</code>, that the ApplyResult was obtained from.
     * 
     * @return A model for <code>g</code>
     * @throws Z3Exception
     **/
    public Model convertModel(int i, Model m) throws Z3Exception
    {
        return new Model(getContext(), 
            Native.applyResultConvertModel(getContext().nCtx(), getNativeObject(), i, m.getNativeObject()));
    }

    /**
     * A string representation of the ApplyResult.
     **/
    public String toString()
    {
        try
        {
            return Native.applyResultToString(getContext().nCtx(), getNativeObject());
        } catch (Z3Exception e)
        {
            return "Z3Exception: " + e.getMessage();
        }
    }

    ApplyResult(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }

    void incRef(long o) throws Z3Exception
    {
        getContext().applyResult_DRQ().incAndClear(getContext(), o);
        super.incRef(o);
    }

    void decRef(long o) throws Z3Exception
    {
        getContext().applyResult_DRQ().add(o);
        super.decRef(o);
    }
}
