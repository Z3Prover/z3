/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    Solver.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

import com.microsoft.z3.enumerations.Z3_lbool;

/**
 * Solvers.
 **/
public class Solver extends Z3Object
{
    /**
     * A string that describes all available solver parameters.
     **/
    public String getHelp()
    {
        return Native.solverGetHelp(getContext().nCtx(), getNativeObject());
    }

    /**
     * Sets the solver parameters.
     * 
     * @throws Z3Exception
     **/
    public void setParameters(Params value)
    {
        getContext().checkContextMatch(value);
        Native.solverSetParams(getContext().nCtx(), getNativeObject(),
                value.getNativeObject());
    }

    /**
     * Retrieves parameter descriptions for solver.
     * 
     * @throws Z3Exception
     **/
    public ParamDescrs getParameterDescriptions()
    {
        return new ParamDescrs(getContext(), Native.solverGetParamDescrs(
                getContext().nCtx(), getNativeObject()));
    }

    /**
     * The current number of backtracking points (scopes). 
     * @see pop 
     * @see push
     **/
    public int getNumScopes()
    {
        return Native
                .solverGetNumScopes(getContext().nCtx(), getNativeObject());
    }

    /**
     * Creates a backtracking point. 
     * @see pop
     **/
    public void push()
    {
        Native.solverPush(getContext().nCtx(), getNativeObject());
    }

    /**
     * Backtracks one backtracking point.
     * Remarks: .
     **/
    public void pop()
    {
        pop(1);
    }

    /**
     * Backtracks {@code n} backtracking points.
     * Remarks: Note that
     * an exception is thrown if {@code n} is not smaller than
     * {@code NumScopes} 
     * @see push
     **/
    public void pop(int n)
    {
        Native.solverPop(getContext().nCtx(), getNativeObject(), n);
    }

    /**
     * Resets the Solver.
     * Remarks: This removes all assertions from the
     * solver.
     **/
    public void reset()
    {
        Native.solverReset(getContext().nCtx(), getNativeObject());
    }

    /**
     * Assert a multiple constraints into the solver.
     * 
     * @throws Z3Exception
     **/
    public void add(BoolExpr... constraints)
    {
        getContext().checkContextMatch(constraints);
        for (BoolExpr a : constraints)
        {
            Native.solverAssert(getContext().nCtx(), getNativeObject(),
                    a.getNativeObject());
        }
    }

    /** 
     *  Assert multiple constraints into the solver, and track them (in the
     * unsat) core
     * using the Boolean constants in ps.
     *
     * Remarks: 
     * This API is an alternative to <see cref="Check"/> with assumptions for
     * extracting unsat cores.
     * Both APIs can be used in the same solver. The unsat core will contain a
     * combination
     * of the Boolean variables provided using <see cref="AssertAndTrack"/>
     * and the Boolean literals
     * provided using <see cref="Check"/> with assumptions.
     **/
    public void assertAndTrack(BoolExpr[] constraints, BoolExpr[] ps)
    {
        getContext().checkContextMatch(constraints);
        getContext().checkContextMatch(ps);
        if (constraints.length != ps.length)
            throw new Z3Exception("Argument size mismatch");

        for (int i = 0; i < constraints.length; i++)
            Native.solverAssertAndTrack(getContext().nCtx(), getNativeObject(),
                    constraints[i].getNativeObject(), ps[i].getNativeObject());
    }

    /** 
     * Assert a constraint into the solver, and track it (in the unsat) core
     * using the Boolean constant p.
     * 
     * Remarks: 
     * This API is an alternative to <see cref="Check"/> with assumptions for
     * extracting unsat cores.
     * Both APIs can be used in the same solver. The unsat core will contain a
     * combination
     * of the Boolean variables provided using <see cref="AssertAndTrack"/>
     * and the Boolean literals
     * provided using <see cref="Check"/> with assumptions.
     */ 
    public void assertAndTrack(BoolExpr constraint, BoolExpr p)
    {
        getContext().checkContextMatch(constraint);
        getContext().checkContextMatch(p);

        Native.solverAssertAndTrack(getContext().nCtx(), getNativeObject(),
                constraint.getNativeObject(), p.getNativeObject());
    }

    /**
     * The number of assertions in the solver.
     * 
     * @throws Z3Exception
     **/
    public int getNumAssertions()
    {
        ASTVector assrts = new ASTVector(getContext(), Native.solverGetAssertions(getContext().nCtx(), getNativeObject()));
        return assrts.size();
    }

    /**
     * The set of asserted formulas.
     * 
     * @throws Z3Exception
     **/
    public BoolExpr[] getAssertions()
    {
        ASTVector assrts = new ASTVector(getContext(), Native.solverGetAssertions(getContext().nCtx(), getNativeObject()));
        return assrts.ToBoolExprArray();
    }

    /**
     * Checks whether the assertions in the solver are consistent or not.
     * Remarks:  
     * @see getModel
     * @see getUnsatCore
     * @see getProof 
     **/
    public Status check(Expr... assumptions)
    {
        Z3_lbool r;
        if (assumptions == null)
            r = Z3_lbool.fromInt(Native.solverCheck(getContext().nCtx(),
                    getNativeObject()));
        else
            r = Z3_lbool.fromInt(Native.solverCheckAssumptions(getContext()
                    .nCtx(), getNativeObject(), (int) assumptions.length, AST
                    .arrayToNative(assumptions)));
        switch (r)
        {
        case Z3_L_TRUE:
            return Status.SATISFIABLE;
        case Z3_L_FALSE:
            return Status.UNSATISFIABLE;
        default:
            return Status.UNKNOWN;
        }
    }

    /**
     * Checks whether the assertions in the solver are consistent or not.
     * Remarks:  
     * @see getModel
     * @see getUnsatCore
     * @see getProof 
     **/
    public Status check()
    {
        return check((Expr[]) null);
    }

    /**
     * The model of the last {@code Check}.
     * Remarks:  The result is
     * {@code null} if {@code Check} was not invoked before, if its
     * results was not {@code SATISFIABLE}, or if model production is not
     * enabled. 
     * 
     * @throws Z3Exception
     **/
    public Model getModel()
    {
        long x = Native.solverGetModel(getContext().nCtx(), getNativeObject());
        if (x == 0)
            return null;
        else
            return new Model(getContext(), x);
    }

    /**
     * The proof of the last {@code Check}.
     * Remarks:  The result is
     * {@code null} if {@code Check} was not invoked before, if its
     * results was not {@code UNSATISFIABLE}, or if proof production is
     * disabled. 
     * 
     * @throws Z3Exception
     **/
    public Expr getProof()
    {
        long x = Native.solverGetProof(getContext().nCtx(), getNativeObject());
        if (x == 0)
            return null;
        else
            return Expr.create(getContext(), x);
    }

    /**
     * The unsat core of the last {@code Check}.
     * Remarks:  The unsat core
     * is a subset of {@code Assertions} The result is empty if
     * {@code Check} was not invoked before, if its results was not
     * {@code UNSATISFIABLE}, or if core production is disabled. 
     * 
     * @throws Z3Exception
     **/
    public BoolExpr[] getUnsatCore()
    {

        ASTVector core = new ASTVector(getContext(), Native.solverGetUnsatCore(getContext().nCtx(), getNativeObject()));        
        return core.ToBoolExprArray();
    }

    /**
     * A brief justification of why the last call to {@code Check} returned
     * {@code UNKNOWN}.
     **/
    public String getReasonUnknown()
    {
        return Native.solverGetReasonUnknown(getContext().nCtx(),
                getNativeObject());
    }

    /**
     * Create a clone of the current solver with respect to <c>ctx</c>.
     */
    public Solver translate(Context ctx) 
    {
	return new Solver(ctx, Native.solverTranslate(getContext().nCtx(), getNativeObject(), ctx.nCtx()));
    }

    /**
     * Solver statistics.
     * 
     * @throws Z3Exception
     **/
    public Statistics getStatistics()
    {
        return new Statistics(getContext(), Native.solverGetStatistics(
                getContext().nCtx(), getNativeObject()));
    }

    /**
     * A string representation of the solver.
     **/
    public String toString()
    {
        try
        {
            return Native
                    .solverToString(getContext().nCtx(), getNativeObject());
        } catch (Z3Exception e)
        {
            return "Z3Exception: " + e.getMessage();
        }
    }

    Solver(Context ctx, long obj)
    {
        super(ctx, obj);
    }

    void incRef(long o)
    {
        getContext().getSolverDRQ().incAndClear(getContext(), o);
        super.incRef(o);
    }

    void decRef(long o)
    {
        getContext().getSolverDRQ().add(o);
        super.decRef(o);
    }
}
