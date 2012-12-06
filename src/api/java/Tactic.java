/**
 * This file was automatically generated from Tactic.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

/**
 * Tactics are the basic building block for creating custom solvers for specific
 * problem domains. The complete list of tactics may be obtained using
 * <code>Context.NumTactics</code> and <code>Context.TacticNames</code>. It may
 * also be obtained using the command <code>(help-tactics)</code> in the SMT 2.0
 * front-end.
 **/
public class Tactic extends Z3Object
{
    /**
     * A string containing a description of parameters accepted by the tactic.
     **/
    public String Help() throws Z3Exception
    {
        return Native.tacticGetHelp(Context().nCtx(), NativeObject());
    }

    /**
     * Retrieves parameter descriptions for Tactics.
     * @throws Z3Exception 
     **/
    public ParamDescrs ParameterDescriptions() throws Z3Exception
    {
        return new ParamDescrs(Context(), Native.tacticGetParamDescrs(Context()
                .nCtx(), NativeObject()));
    }

    /**
     * Execute the tactic over the goal.
     * @throws Z3Exception 
     **/
    public ApplyResult Apply(Goal g) throws Z3Exception
    {	
        return Apply(g, null);
    }

    /**
     * Execute the tactic over the goal.
     * @throws Z3Exception 
     **/
    public ApplyResult Apply(Goal g, Params p) throws Z3Exception
    {

        Context().CheckContextMatch(g);
        if (p == null)
            return new ApplyResult(Context(), Native.tacticApply(Context()
                    .nCtx(), NativeObject(), g.NativeObject()));
        else
        {
            Context().CheckContextMatch(p);
            return new ApplyResult(Context(),
                    Native.tacticApplyEx(Context().nCtx(), NativeObject(),
                            g.NativeObject(), p.NativeObject()));
        }
    }

    /**
     * Apply the tactic to a goal.
     * @throws Z3Exception 
     **/
    public ApplyResult get(Goal g) throws Z3Exception
    {

        return Apply(g, null);
    }

    /**
     * Creates a solver that is implemented using the given tactic. <seealso
     * cref="Context.MkSolver(Tactic)"/>
     * @throws Z3Exception 
     **/
    public Solver Solver() throws Z3Exception
    {

        return Context().MkSolver(this);
    }

    Tactic(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }

    Tactic(Context ctx, String name) throws Z3Exception
    {
        super(ctx, Native.mkTactic(ctx.nCtx(), name));
    }

    void IncRef(long o) throws Z3Exception
    {
        Context().Tactic_DRQ().IncAndClear(Context(), o);
        super.IncRef(o);
    }

    void DecRef(long o) throws Z3Exception
    {
        Context().Tactic_DRQ().Add(o);
        super.DecRef(o);
    }
}
