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
    public Z3_goal_prec getPrecision()
    {
        return Z3_goal_prec.fromInt(Native.goalPrecision(getContext().nCtx(),
                getNativeObject()));
    }

    /**
     * Indicates whether the goal is precise.
     **/
    public boolean isPrecise()
    {
        return getPrecision() == Z3_goal_prec.Z3_GOAL_PRECISE;
    }

    /**
     * Indicates whether the goal is an under-approximation.
     **/
    public boolean isUnderApproximation()
    {
        return getPrecision() == Z3_goal_prec.Z3_GOAL_UNDER;
    }

    /**
     * Indicates whether the goal is an over-approximation.
     **/
    public boolean isOverApproximation()
    {
        return getPrecision() == Z3_goal_prec.Z3_GOAL_OVER;
    }

    /**
     * Indicates whether the goal is garbage (i.e., the product of over- and
     * under-approximations).
     **/
    public boolean isGarbage()
    {
        return getPrecision() == Z3_goal_prec.Z3_GOAL_UNDER_OVER;
    }

    /**
     * Adds the {@code constraints} to the given goal.
     * 
     * @throws Z3Exception
     **/
    public void add(BoolExpr ... constraints)
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
    public boolean inconsistent()
    {
        return Native.goalInconsistent(getContext().nCtx(), getNativeObject());
    }

    /**
     * The depth of the goal.
     * Remarks:  This tracks how many transformations
     * were applied to it. 
     **/
    public int getDepth()
    {
        return Native.goalDepth(getContext().nCtx(), getNativeObject());
    }

    /**
     * Erases all formulas from the given goal.
     **/
    public void reset()
    {
        Native.goalReset(getContext().nCtx(), getNativeObject());
    }

    /**
     * The number of formulas in the goal.
     **/
    public int size()
    {
        return Native.goalSize(getContext().nCtx(), getNativeObject());
    }

    /**
     * The formulas in the goal.
     * 
     * @throws Z3Exception
     **/
    public BoolExpr[] getFormulas()
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
    public int getNumExprs()
    {
        return Native.goalNumExprs(getContext().nCtx(), getNativeObject());
    }

    /**
     * Indicates whether the goal is empty, and it is precise or the product of
     * an under approximation.
     **/
    public boolean isDecidedSat()
    {
        return Native.goalIsDecidedSat(getContext().nCtx(), getNativeObject());
    }

    /**
     * Indicates whether the goal contains `false', and it is precise or the
     * product of an over approximation.
     **/
    public boolean isDecidedUnsat()
    {
        return Native
                .goalIsDecidedUnsat(getContext().nCtx(), getNativeObject());
    }

    /**
     * Translates (copies) the Goal to the target Context {@code ctx}.
     * 
     * @throws Z3Exception
     **/
    public Goal translate(Context ctx)
    {
        return new Goal(ctx, Native.goalTranslate(getContext().nCtx(),
                getNativeObject(), ctx.nCtx()));
    }

    /**
     * Simplifies the goal.
     * Remarks: Essentially invokes the `simplify' tactic
     * on the goal.
     **/
    public Goal simplify()
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
    public Goal simplify(Params p)
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
    
    /** 
     * Goal to BoolExpr conversion.
     *  
     * Returns a string representation of the Goal.
     **/
    public BoolExpr AsBoolExpr() {
        int n = size();
        if (n == 0) 
            return getContext().mkTrue();
        else if (n == 1)                
            return getFormulas()[0];
        else {
            return getContext().mkAnd(getFormulas());
        }
    }

    Goal(Context ctx, long obj)
    {
        super(ctx, obj);
    }

    Goal(Context ctx, boolean models, boolean unsatCores, boolean proofs)
           
    {
        super(ctx, Native.mkGoal(ctx.nCtx(), (models) ? true : false,
                (unsatCores) ? true : false, (proofs) ? true : false));
    }

    void incRef(long o)
    {
        getContext().getGoalDRQ().incAndClear(getContext(), o);
        super.incRef(o);
    }

    void decRef(long o)
    {
        getContext().getGoalDRQ().add(o);
        super.decRef(o);
    }

}
