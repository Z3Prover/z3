/**
 * This file was automatically generated from Goal.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

import com.microsoft.z3.enumerations.*;

/**
 * A goal (aka problem). A goal is essentially a set of formulas, that can be
 * solved and/or transformed using tactics and solvers.
 **/
public class Goal extends Z3Object
{
    /**
     * The precision of the goal. <remarks> Goals can be transformed using over
     * and under approximations. An under approximation is applied when the
     * objective is to find a model for a given goal. An over approximation is
     * applied when the objective is to find a proof for a given goal.
     * </remarks>
     **/
    public Z3_goal_prec Precision() throws Z3Exception
    {
        return Z3_goal_prec.fromInt(Native.goalPrecision(Context().nCtx(),
                NativeObject()));
    }

    /**
     * Indicates whether the goal is precise.
     **/
    public boolean IsPrecise() throws Z3Exception
    {
        return Precision() == Z3_goal_prec.Z3_GOAL_PRECISE;
    }

    /**
     * Indicates whether the goal is an under-approximation.
     **/
    public boolean IsUnderApproximation() throws Z3Exception
    {
        return Precision() == Z3_goal_prec.Z3_GOAL_UNDER;
    }

    /**
     * Indicates whether the goal is an over-approximation.
     **/
    public boolean IsOverApproximation() throws Z3Exception
    {
        return Precision() == Z3_goal_prec.Z3_GOAL_OVER;
    }

    /**
     * Indicates whether the goal is garbage (i.e., the product of over- and
     * under-approximations).
     **/
    public boolean IsGarbage() throws Z3Exception
    {
        return Precision() == Z3_goal_prec.Z3_GOAL_UNDER_OVER;
    }

    /**
     * Adds the <paramref name="constraints"/> to the given goal.
     * 
     * @throws Z3Exception
     **/
    public void Assert(BoolExpr[] constraints) throws Z3Exception
    {
        Context().CheckContextMatch(constraints);
        for (BoolExpr c : constraints)
        {
            Native.goalAssert(Context().nCtx(), NativeObject(),
                    c.NativeObject());
        }
    }

    /**
     * Adds a <paramref name="constraint"/> to the given goal.
     * 
     * @throws Z3Exception
     **/
    public void Assert(BoolExpr constraint) throws Z3Exception
    {
        Context().CheckContextMatch(constraint);
        Native.goalAssert(Context().nCtx(), NativeObject(),
                constraint.NativeObject());
    }

    /**
     * Indicates whether the goal contains `false'.
     **/
    public boolean Inconsistent() throws Z3Exception
    {
        return Native.goalInconsistent(Context().nCtx(), NativeObject());
    }

    /**
     * The depth of the goal. <remarks> This tracks how many transformations
     * were applied to it. </remarks>
     **/
    public int Depth() throws Z3Exception
    {
        return Native.goalDepth(Context().nCtx(), NativeObject());
    }

    /**
     * Erases all formulas from the given goal.
     **/
    public void Reset() throws Z3Exception
    {
        Native.goalReset(Context().nCtx(), NativeObject());
    }

    /**
     * The number of formulas in the goal.
     **/
    public int Size() throws Z3Exception
    {
        return Native.goalSize(Context().nCtx(), NativeObject());
    }

    /**
     * The formulas in the goal.
     * 
     * @throws Z3Exception
     **/
    public BoolExpr[] Formulas() throws Z3Exception
    {
        int n = Size();
        BoolExpr[] res = new BoolExpr[n];
        for (int i = 0; i < n; i++)
            res[i] = new BoolExpr(Context(), Native.goalFormula(Context()
                    .nCtx(), NativeObject(), i));
        return res;
    }

    /**
     * The number of formulas, subformulas and terms in the goal.
     **/
    public int NumExprs() throws Z3Exception
    {
        return Native.goalNumExprs(Context().nCtx(), NativeObject());
    }

    /**
     * Indicates whether the goal is empty, and it is precise or the product of
     * an under approximation.
     **/
    public boolean IsDecidedSat() throws Z3Exception
    {
        return Native.goalIsDecidedSat(Context().nCtx(), NativeObject());
    }

    /**
     * Indicates whether the goal contains `false', and it is precise or the
     * product of an over approximation.
     **/
    public boolean IsDecidedUnsat() throws Z3Exception
    {
        return Native.goalIsDecidedUnsat(Context().nCtx(), NativeObject());
    }

    /**
     * Translates (copies) the Goal to the target Context <paramref
     * name="ctx"/>.
     * 
     * @throws Z3Exception
     **/
    public Goal Translate(Context ctx) throws Z3Exception
    {
        return new Goal(ctx, Native.goalTranslate(Context().nCtx(),
                NativeObject(), ctx.nCtx()));
    }

    /**
     * Simplifies the goal. <remarks>Essentially invokes the `simplify' tactic
     * on the goal.</remarks>
     **/
    public Goal Simplify(Params p) throws Z3Exception
    {
        Tactic t = Context().MkTactic("simplify");
        ApplyResult res = t.Apply(this, p);

        if (res.NumSubgoals() == 0)
            throw new Z3Exception("No subgoals");
        else
            return res.Subgoals()[0];
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
            return Native.goalToString(Context().nCtx(), NativeObject());
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

    void IncRef(long o) throws Z3Exception
    {
        Context().Goal_DRQ().IncAndClear(Context(), o);
        super.IncRef(o);
    }

    void DecRef(long o) throws Z3Exception
    {
        Context().Goal_DRQ().Add(o);
        super.DecRef(o);
    }

}
