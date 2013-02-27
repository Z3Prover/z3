/**
 * This file was automatically generated from Solver.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
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
    public String getHelp() throws Z3Exception
    {
        return Native.solverGetHelp(getContext().nCtx(), getNativeObject());
    }

    /**
     * Sets the solver parameters.
     * 
     * @throws Z3Exception
     **/
    public void setParameters(Params value) throws Z3Exception
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
    public ParamDescrs getParameterDescriptions() throws Z3Exception
    {
        return new ParamDescrs(getContext(), Native.solverGetParamDescrs(
                getContext().nCtx(), getNativeObject()));
    }

    /**
     * The current number of backtracking points (scopes). <seealso cref="Pop"/>
     * <seealso cref="Push"/>
     **/
    public int getNumScopes() throws Z3Exception
    {
        return Native
                .solverGetNumScopes(getContext().nCtx(), getNativeObject());
    }

    /**
     * Creates a backtracking point. <seealso cref="Pop"/>
     **/
    public void push() throws Z3Exception
    {
        Native.solverPush(getContext().nCtx(), getNativeObject());
    }

    /**
     * Backtracks one backtracking point. <remarks>.
     **/
    public void pop() throws Z3Exception
    {
        pop(1);
    }

    /**
     * Backtracks <paramref name="n"/> backtracking points. <remarks>Note that
     * an exception is thrown if <paramref name="n"/> is not smaller than
     * <code>NumScopes</code></remarks> <seealso cref="Push"/>
     **/
    public void pop(int n) throws Z3Exception
    {
        Native.solverPop(getContext().nCtx(), getNativeObject(), n);
    }

    /**
     * Resets the Solver. <remarks>This removes all assertions from the
     * solver.</remarks>
     **/
    public void reset() throws Z3Exception
    {
        Native.solverReset(getContext().nCtx(), getNativeObject());
    }

    /**
     * Assert a multiple constraints into the solver.
     * 
     * @throws Z3Exception
     **/
    public void add(BoolExpr... constraints) throws Z3Exception
    {
        getContext().checkContextMatch(constraints);
        for (BoolExpr a : constraints)
        {
            Native.solverAssert(getContext().nCtx(), getNativeObject(),
                    a.getNativeObject());
        }
    }

    // / <summary>
    // / Assert multiple constraints into the solver, and track them (in the
    // unsat) core
    // / using the Boolean constants in ps.
    // / </summary>
    // / <remarks>
    // / This API is an alternative to <see cref="Check"/> with assumptions for
    // extracting unsat cores.
    // / Both APIs can be used in the same solver. The unsat core will contain a
    // combination
    // / of the Boolean variables provided using <see cref="AssertAndTrack"/>
    // and the Boolean literals
    // / provided using <see cref="Check"/> with assumptions.
    // / </remarks>
    public void assertAndTrack(BoolExpr[] constraints, BoolExpr[] ps) throws Z3Exception
    {
        getContext().checkContextMatch(constraints);
        getContext().checkContextMatch(ps);
        if (constraints.length != ps.length)
            throw new Z3Exception("Argument size mismatch");

        for (int i = 0; i < constraints.length; i++)
            Native.solverAssertAndTrack(getContext().nCtx(), getNativeObject(),
                    constraints[i].getNativeObject(), ps[i].getNativeObject());
    }

    // / <summary>
    // / Assert a constraint into the solver, and track it (in the unsat) core
    // / using the Boolean constant p.
    // / </summary>
    // / <remarks>
    // / This API is an alternative to <see cref="Check"/> with assumptions for
    // extracting unsat cores.
    // / Both APIs can be used in the same solver. The unsat core will contain a
    // combination
    // / of the Boolean variables provided using <see cref="AssertAndTrack"/>
    // and the Boolean literals
    // / provided using <see cref="Check"/> with assumptions.
    // / </remarks>
    public void assertAndTrack(BoolExpr constraint, BoolExpr p) throws Z3Exception
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
    public int getNumAssertions() throws Z3Exception
    {
        ASTVector ass = new ASTVector(getContext(), Native.solverGetAssertions(
                getContext().nCtx(), getNativeObject()));
        return ass.size();
    }

    /**
     * The set of asserted formulas.
     * 
     * @throws Z3Exception
     **/
    public BoolExpr[] getAssertions() throws Z3Exception
    {
        ASTVector ass = new ASTVector(getContext(), Native.solverGetAssertions(
                getContext().nCtx(), getNativeObject()));
        int n = ass.size();
        BoolExpr[] res = new BoolExpr[n];
        for (int i = 0; i < n; i++)
            res[i] = new BoolExpr(getContext(), ass.get(i).getNativeObject());
        return res;
    }

    /**
     * Checks whether the assertions in the solver are consistent or not.
     * <remarks> <seealso cref="Model"/> <seealso cref="UnsatCore"/> <seealso
     * cref="Proof"/> </remarks>
     **/
    public Status check(Expr... assumptions) throws Z3Exception
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
     * <remarks> <seealso cref="Model"/> <seealso cref="UnsatCore"/> <seealso
     * cref="Proof"/> </remarks>
     **/
    public Status check() throws Z3Exception
    {
        return check((Expr[]) null);
    }

    /**
     * The model of the last <code>Check</code>. <remarks> The result is
     * <code>null</code> if <code>Check</code> was not invoked before, if its
     * results was not <code>SATISFIABLE</code>, or if model production is not
     * enabled. </remarks>
     * 
     * @throws Z3Exception
     **/
    public Model getModel() throws Z3Exception
    {
        long x = Native.solverGetModel(getContext().nCtx(), getNativeObject());
        if (x == 0)
            return null;
        else
            return new Model(getContext(), x);
    }

    /**
     * The proof of the last <code>Check</code>. <remarks> The result is
     * <code>null</code> if <code>Check</code> was not invoked before, if its
     * results was not <code>UNSATISFIABLE</code>, or if proof production is
     * disabled. </remarks>
     * 
     * @throws Z3Exception
     **/
    public Expr getProof() throws Z3Exception
    {
        long x = Native.solverGetProof(getContext().nCtx(), getNativeObject());
        if (x == 0)
            return null;
        else
            return Expr.create(getContext(), x);
    }

    /**
     * The unsat core of the last <code>Check</code>. <remarks> The unsat core
     * is a subset of <code>Assertions</code> The result is empty if
     * <code>Check</code> was not invoked before, if its results was not
     * <code>UNSATISFIABLE</code>, or if core production is disabled. </remarks>
     * 
     * @throws Z3Exception
     **/
    public Expr[] getUnsatCore() throws Z3Exception
    {

        ASTVector core = new ASTVector(getContext(), Native.solverGetUnsatCore(
                getContext().nCtx(), getNativeObject()));
        int n = core.size();
        Expr[] res = new Expr[n];
        for (int i = 0; i < n; i++)
            res[i] = Expr.create(getContext(), core.get(i).getNativeObject());
        return res;
    }

    /**
     * A brief justification of why the last call to <code>Check</code> returned
     * <code>UNKNOWN</code>.
     **/
    public String getReasonUnknown() throws Z3Exception
    {
        return Native.solverGetReasonUnknown(getContext().nCtx(),
                getNativeObject());
    }

    /**
     * Solver statistics.
     * 
     * @throws Z3Exception
     **/
    public Statistics getStatistics() throws Z3Exception
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

    Solver(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }

    void incRef(long o) throws Z3Exception
    {
        getContext().solver_DRQ().incAndClear(getContext(), o);
        super.incRef(o);
    }

    void decRef(long o) throws Z3Exception
    {
        getContext().solver_DRQ().add(o);
        super.decRef(o);
    }
}
