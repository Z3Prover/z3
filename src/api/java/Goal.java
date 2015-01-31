/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    Goal.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

import com.microsoft.z3.enumerations.Z3_goal_prec;

/**
 * A goal (aka problem). A goal is essentially a set of formulas, that can be
 * solved and/or transformed using tactics and solvers.
 **/
public class Goal extends Z3Object
{
    /**
     * The precision of the goal.
     * Remarks:  Goals can be transformed using over
     * and under approximations. An under approximation is applied when the
     * objective is to find a model for a given goal. An over approximation is
     * applied when the objective is to find a proof for a given goal.
     * 
     **/
    public Z3_goal_prec getPrecision() throws Z3Exception
    {
        return Z3_goal_prec.fromInt(Native.goalPrecision(getContext().nCtx(),
                getNativeObject()));
    }

    /**
     * Indicates whether the goal is precise.
     **/
    public boolean isPrecise() throws Z3Exception
    {
        return getPrecision() == Z3_goal_prec.Z3_GOAL_PRECISE;
    }

    /**
     * Indicates whether the goal is an under-approximation.
     **/
    public boolean isUnderApproximation() throws Z3Exception
    {
        return getPrecision() == Z3_goal_prec.Z3_GOAL_UNDER;
    }

    /**
     * Indicates whether the goal is an over-approximation.
     **/
    public boolean isOverApproximation() throws Z3Exception
    {
        return getPrecision() == Z3_goal_prec.Z3_GOAL_OVER;
    }

    /**
     * Indicates whether the goal is garbage (i.e., the product of over- and
     * under-approximations).
     **/
    public boolean isGarbage() throws Z3Exception
    {
        return getPrecision() == Z3_goal_prec.Z3_GOAL_UNDER_OVER;
    }

    /**
     * Adds the {@code constraints} to the given goal.
     * 
     * @throws Z3Exception
     **/
    public void add(BoolExpr ... constraints) throws Z3Exception
    {
        getContext().checkContextMatch(constraints);
        for (BoolExpr c : constraints)
        {
            Native.goalAssert(getContext().nCtx(), getNativeObject(),
                    c.getNativeObject());
        }
    }

    /**
     * Indicates whether the goal contains `false'.
     **/
    public boolean inconsistent() throws Z3Exception
    {
        return Native.goalInconsistent(getContext().nCtx(), getNativeObject());
    }

    /**
     * The depth of the goal.
     * Remarks:  This tracks how many transformations
     * were applied to it. 
     **/
    public int getDepth() throws Z3Exception
    {
        return Native.goalDepth(getContext().nCtx(), getNativeObject());
    }

    /**
     * Erases all formulas from the given goal.
     **/
    public void reset() throws Z3Exception
    {
        Native.goalReset(getContext().nCtx(), getNativeObject());
    }

    /**
     * The number of formulas in the goal.
     **/
    public int size() throws Z3Exception
    {
        return Native.goalSize(getContext().nCtx(), getNativeObject());
    }

    /**
     * The formulas in the goal.
     * 
     * @throws Z3Exception
     **/
    public BoolExpr[] getFormulas() throws Z3Exception
    {
        int n = size();
        BoolExpr[] res = new BoolExpr[n];
        for (int i = 0; i < n; i++)
            res[i] = new BoolExpr(getContext(), Native.goalFormula(getContext()
                    .nCtx(), getNativeObject(), i));
        return res;
    }

    /**
     * The number of formulas, subformulas and terms in the goal.
     **/
    public int getNumExprs() throws Z3Exception
    {
        return Native.goalNumExprs(getContext().nCtx(), getNativeObject());
    }

    /**
     * Indicates whether the goal is empty, and it is precise or the product of
     * an under approximation.
     **/
    public boolean isDecidedSat() throws Z3Exception
    {
        return Native.goalIsDecidedSat(getContext().nCtx(), getNativeObject());
    }

    /**
     * Indicates whether the goal contains `false', and it is precise or the
     * product of an over approximation.
     **/
    public boolean isDecidedUnsat() throws Z3Exception
    {
        return Native
                .goalIsDecidedUnsat(getContext().nCtx(), getNativeObject());
    }

    /**
     * Translates (copies) the Goal to the target Context {@code ctx}.
     * 
     * @throws Z3Exception
     **/
    public Goal translate(Context ctx) throws Z3Exception
    {
        return new Goal(ctx, Native.goalTranslate(getContext().nCtx(),
                getNativeObject(), ctx.nCtx()));
    }

    /**
     * Simplifies the goal.
     * Remarks: Essentially invokes the `simplify' tactic
     * on the goal.
     **/
    public Goal simplify() throws Z3Exception
    {
        Tactic t = getContext().mkTactic("simplify");
        ApplyResult res = t.apply(this);

        if (res.getNumSubgoals() == 0)
            throw new Z3Exception("No subgoals");
        else
            return res.getSubgoals()[0];
    }
    
    /**
     * Simplifies the goal.
     * Remarks: Essentially invokes the `simplify' tactic
     * on the goal.
     **/
    public Goal simplify(Params p) throws Z3Exception
    {
        Tactic t = getContext().mkTactic("simplify");
        ApplyResult res = t.apply(this, p);

        if (res.getNumSubgoals() == 0)
            throw new Z3Exception("No subgoals");
        else
            return res.getSubgoals()[0];
    }

    /**
     * Goal to string conversion.
     * 
     * @return A string representation of the Goal.
     **/
    public String toString()
    {
        try
        {
            return Native.goalToString(getContext().nCtx(), getNativeObject());
        } catch (Z3Exception e)
        {
            return "Z3Exception: " + e.getMessage();
        }
    }

    Goal(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }

    Goal(Context ctx, boolean models, boolean unsatCores, boolean proofs)
            throws Z3Exception
    {
        super(ctx, Native.mkGoal(ctx.nCtx(), (models) ? true : false,
                (unsatCores) ? true : false, (proofs) ? true : false));
    }

    void incRef(long o) throws Z3Exception
    {
        getContext().getGoalDRQ().incAndClear(getContext(), o);
        super.incRef(o);
    }

    void decRef(long o) throws Z3Exception
    {
        getContext().getGoalDRQ().add(o);
        super.decRef(o);
    }

}
