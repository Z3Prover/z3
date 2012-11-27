/**
 * This file was automatically generated from Solver.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.Microsoft.Z3;

import com.Microsoft.Z3.Enumerations.*;

/**
 * Solvers.
 **/
public class Solver extends Z3Object
{
    /**
     * A string that describes all available solver parameters.
     **/
    public String Help()
    {
        return Native.solverGetHelp(Context().nCtx(), NativeObject());
    }

    /**
     * Sets the solver parameters.
     * @throws Z3Exception 
     **/
    public void setParameters(Params value) throws Z3Exception
    {
        Context().CheckContextMatch(value);
        Native.solverSetParams(Context().nCtx(), NativeObject(),
                value.NativeObject());
    }

    /**
     * Retrieves parameter descriptions for solver.
     * @throws Z3Exception 
     **/
    public ParamDescrs ParameterDescriptions() throws Z3Exception
    {
        return new ParamDescrs(Context(), Native.solverGetParamDescrs(Context()
                .nCtx(), NativeObject()));
    }

    /**
     * The current number of backtracking points (scopes). <seealso cref="Pop"/>
     * <seealso cref="Push"/>
     **/
    public int NumScopes()
    {
        return Native.solverGetNumScopes(Context().nCtx(), NativeObject());
    }

    /**
     * Creates a backtracking point. <seealso cref="Pop"/>
     **/
    public void Push()
    {
        Native.solverPush(Context().nCtx(), NativeObject());
    }

    /**
     * Backtracks <paramref name="n"/> backtracking points. <remarks>Note that
     * an exception is thrown if <paramref name="n"/> is not smaller than
     * <code>NumScopes</code></remarks> <seealso cref="Push"/>
     **/
    public void Pop(int n)
    {
        Native.solverPop(Context().nCtx(), NativeObject(), n);
    }

    /**
     * Resets the Solver. <remarks>This removes all assertions from the
     * solver.</remarks>
     **/
    public void Reset()
    {
        Native.solverReset(Context().nCtx(), NativeObject());
    }

    /**
     * Assert a constraint (or multiple) into the solver.
     * @throws Z3Exception 
     **/
    public void Assert(BoolExpr[] constraints) throws Z3Exception
    {
        Context().CheckContextMatch(constraints);
        for (BoolExpr a : constraints)
        {
            Native.solverAssert(Context().nCtx(), NativeObject(),
                    a.NativeObject());
        }
    }

    /**
     * The number of assertions in the solver.
     * @throws Z3Exception 
     **/
    public int NumAssertions() throws Z3Exception
    {
        ASTVector ass = new ASTVector(Context(), Native.solverGetAssertions(
                Context().nCtx(), NativeObject()));
        return ass.Size();
    }

    /**
     * The set of asserted formulas.
     * @throws Z3Exception 
     **/
    public BoolExpr[] Assertions() throws Z3Exception
    {
        ASTVector ass = new ASTVector(Context(), Native.solverGetAssertions(
                Context().nCtx(), NativeObject()));
        int n = ass.Size();
        BoolExpr[] res = new BoolExpr[n];
        for (int i = 0; i < n; i++)
            res[i] = new BoolExpr(Context(), ass.get(i).NativeObject());
        return res;
    }

    /**
     * Checks whether the assertions in the solver are consistent or not.
     * <remarks> <seealso cref="Model"/> <seealso cref="UnsatCore"/> <seealso
     * cref="Proof"/> </remarks>
     **/
    public Status Check(Expr[] assumptions)
    {
        Z3_lbool r;
        if (assumptions == null)
            r = Z3_lbool.fromInt(Native.solverCheck(Context().nCtx(),
                    NativeObject()));
        else
            r = Z3_lbool.fromInt(Native.solverCheckAssumptions(
                    Context().nCtx(), NativeObject(), (int) assumptions.length,
                    AST.ArrayToNative(assumptions)));
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
     * The model of the last <code>Check</code>. <remarks> The result is
     * <code>null</code> if <code>Check</code> was not invoked before, if its
     * results was not <code>SATISFIABLE</code>, or if model production is not
     * enabled. </remarks>
     * @throws Z3Exception 
     **/
    public Model Model() throws Z3Exception
    {
        long x = Native.solverGetModel(Context().nCtx(), NativeObject());
        if (x == 0)
            return null;
        else
            return new Model(Context(), x);
    }

    /**
     * The proof of the last <code>Check</code>. <remarks> The result is
     * <code>null</code> if <code>Check</code> was not invoked before, if its
     * results was not <code>UNSATISFIABLE</code>, or if proof production is
     * disabled. </remarks>
     * @throws Z3Exception 
     **/
    public Expr Proof() throws Z3Exception
    {
        long x = Native.solverGetProof(Context().nCtx(), NativeObject());
        if (x == 0)
            return null;
        else
            return Expr.Create(Context(), x);
    }

    /**
     * The unsat core of the last <code>Check</code>. <remarks> The unsat core
     * is a subset of <code>Assertions</code> The result is empty if
     * <code>Check</code> was not invoked before, if its results was not
     * <code>UNSATISFIABLE</code>, or if core production is disabled. </remarks>
     * @throws Z3Exception 
     **/
    public Expr[] UnsatCore() throws Z3Exception
    {

        ASTVector core = new ASTVector(Context(), Native.solverGetUnsatCore(
                Context().nCtx(), NativeObject()));
        int n = core.Size();
        Expr[] res = new Expr[n];
        for (int i = 0; i < n; i++)
            res[i] = Expr.Create(Context(), core.get(i).NativeObject());
        return res;
    }

    /**
     * A brief justification of why the last call to <code>Check</code> returned
     * <code>UNKNOWN</code>.
     **/
    public String ReasonUnknown()
    {

        return Native.solverGetReasonUnknown(Context().nCtx(), NativeObject());
    }

    /**
     * Solver statistics.
     * @throws Z3Exception 
     **/
    public Statistics Statistics() throws Z3Exception
    {
        return new Statistics(Context(), Native.solverGetStatistics(Context()
                .nCtx(), NativeObject()));
    }

    /**
     * A string representation of the solver.
     **/
    public String toString()
    {
        return Native.solverToString(Context().nCtx(), NativeObject());
    }

    Solver(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }

    void IncRef(long o) throws Z3Exception
    {
        Context().Solver_DRQ().IncAndClear(Context(), o);
        super.IncRef(o);
    }

    void DecRef(long o) throws Z3Exception
    {
        Context().Solver_DRQ().Add(o);
        super.DecRef(o);
    }
}
