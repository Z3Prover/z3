/**
Copyright (c) 2015 Microsoft Corporation

Module Name:

    Optimize.java

Abstract:

    Z3 Java API: Optimizes

Author:

    Nikolaj Bjorner (nbjorner) 2015-07-16

Notes:
**/

package com.microsoft.z3;

import com.microsoft.z3.enumerations.Z3_lbool;


/**
 * Object for managing optimization context
 **/
public class Optimize extends Z3Object {

    /**
     * A string that describes all available optimize solver parameters.
     **/
    public String getHelp()
    {
        return Native.optimizeGetHelp(getContext().nCtx(), getNativeObject());
    }

    /**
     * Sets the optimize solver parameters.
     *
     * @throws Z3Exception
     **/
    public void setParameters(Params value)
    {
        Native.optimizeSetParams(getContext().nCtx(), getNativeObject(), value.getNativeObject());
    }

    /**
     * Retrieves parameter descriptions for Optimize solver.
     **/
    public ParamDescrs getParameterDescriptions()
    {
        return new ParamDescrs(getContext(), Native.optimizeGetParamDescrs(getContext().nCtx(), getNativeObject()));
    }

    /**
     * Assert a constraint (or multiple) into the optimize solver.
     **/
    public void Assert(BoolExpr ... constraints)
    {
        getContext().checkContextMatch(constraints);
        for (BoolExpr a : constraints)
        {
            Native.optimizeAssert(getContext().nCtx(), getNativeObject(), a.getNativeObject());
        }
    }

    /**
     * Alias for Assert.
     **/
    public void Add(BoolExpr ... constraints)
    {
        Assert(constraints);
    }

    /**
     * Handle to objectives returned by objective functions.
     **/
    public static class Handle {

        private final Optimize opt;
        private final int handle;

        Handle(Optimize opt, int h)
        {
            this.opt = opt;
            this.handle = h;
        }

        /**
         * Retrieve a lower bound for the objective handle.
         **/
        public Expr getLower()
        {
            return opt.GetLower(handle);
        }

        /**
         * Retrieve an upper bound for the objective handle.
         **/
        public Expr getUpper()
        {
            return opt.GetUpper(handle);
        }

        /**
         * @return a triple representing the upper bound of the objective handle.
         *
         * The triple contains values {@code inf, value, eps},
         * where the objective value is unbounded iff {@code inf} is non-zero,
         * and otherwise is represented by the expression {@code value + eps * EPSILON},
         * where {@code EPSILON} is an arbitrarily small real number.
         */
        public Expr[] getUpperAsVector()
        {
            return opt.GetUpperAsVector(handle);
        }

        /**
         * @return a triple representing the upper bound of the objective handle.
         *
         * <p>See {@link #getUpperAsVector()} for triple semantics.
         */
        public Expr[] getLowerAsVector()
        {
            return opt.GetLowerAsVector(handle);
        }

        /**
         * Retrieve the value of an objective.
         **/
        public Expr getValue()
        {
            return getLower();
        }

        /**
         * Print a string representation of the handle.
         **/
        @Override
        public String toString()
        {
            return getValue().toString();
        }
    }

    /**
     * Assert soft constraint
     *
     * Return an objective which associates with the group of constraints.
     *
     **/
    public Handle AssertSoft(BoolExpr constraint, int weight, String group)
    {
        getContext().checkContextMatch(constraint);
        Symbol s = getContext().mkSymbol(group);
        return new Handle(this, Native.optimizeAssertSoft(getContext().nCtx(), getNativeObject(), constraint.getNativeObject(), Integer.toString(weight), s.getNativeObject()));
    }

    /**
     * Check satisfiability of asserted constraints.
     * Produce a model that (when the objectives are bounded and 
     * don't use strict inequalities) meets the objectives.
     **/
    public Status Check()
    {
        Z3_lbool r = Z3_lbool.fromInt(Native.optimizeCheck(getContext().nCtx(), getNativeObject()));
        switch (r) {
            case Z3_L_TRUE:
                return Status.SATISFIABLE;
            case Z3_L_FALSE:
                return Status.UNSATISFIABLE;
            default:
                return Status.UNKNOWN;
        }
    }

    /**
     * Creates a backtracking point.
     **/
    public void Push()
    {
        Native.optimizePush(getContext().nCtx(), getNativeObject());
    }

    /**
     * Backtrack one backtracking point.
     *
     * Note that an exception is thrown if Pop is called without a corresponding Push.
     **/
    public void Pop()
    {
        Native.optimizePop(getContext().nCtx(), getNativeObject());
    }


    /**
     * The model of the last Check.
     *
     * The result is null if Check was not invoked before,
     * if its results was not SATISFIABLE, or if model production is not enabled.
     **/
    public Model getModel()
    {
        long x = Native.optimizeGetModel(getContext().nCtx(), getNativeObject());
        if (x == 0) {
            return null;
        } else {
            return new Model(getContext(), x);
        }
    }

    /**
     *  Declare an arithmetical maximization objective.
     *  Return a handle to the objective. The handle is used as
     *  to retrieve the values of objectives after calling Check.
     **/            
    public Handle MkMaximize(Expr e)
    {
        return new Handle(this, Native.optimizeMaximize(getContext().nCtx(), getNativeObject(), e.getNativeObject()));
    }

    /**
     *  Declare an arithmetical minimization objective. 
     *  Similar to MkMaximize.
     **/
    public Handle MkMinimize(Expr e)
    {
        return new Handle(this, Native.optimizeMinimize(getContext().nCtx(), getNativeObject(), e.getNativeObject()));
    }
    
    /**
     *  Retrieve a lower bound for the objective handle.
     **/
    private Expr GetLower(int index)
    {
        return Expr.create(getContext(), Native.optimizeGetLower(getContext().nCtx(), getNativeObject(), index));
    }

    /**
     *  Retrieve an upper bound for the objective handle.
     **/
    private Expr GetUpper(int index)
    {
        return Expr.create(getContext(), Native.optimizeGetUpper(getContext().nCtx(), getNativeObject(), index));
    }

    /**
     * @return Triple representing the upper bound for the objective handle.
     *
     * <p>See {@link Handle#getUpperAsVector}.
     */
    private Expr[] GetUpperAsVector(int index) {
        return unpackObjectiveValueVector(
                Native.optimizeGetUpperAsVector(
                        getContext().nCtx(), getNativeObject(), index
                )
        );
    }

    /**
     * @return Triple representing the upper bound for the objective handle.
     *
     * <p>See {@link Handle#getLowerAsVector}.
     */
    private Expr[] GetLowerAsVector(int index) {
        return unpackObjectiveValueVector(
                Native.optimizeGetLowerAsVector(
                        getContext().nCtx(), getNativeObject(), index
                )
        );
    }

    private Expr[] unpackObjectiveValueVector(long nativeVec) {
        ASTVector vec = new ASTVector(
                getContext(), nativeVec
        );
        return new Expr[] {
                (Expr) vec.get(0), (Expr) vec.get(1), (Expr) vec.get(2)
        };

    }

    /**
     * Return a string the describes why the last to check returned unknown
     **/
    public String getReasonUnknown()
    {
        return Native.optimizeGetReasonUnknown(getContext().nCtx(), getNativeObject());
    }

    /**
     *  Print the context to a String (SMT-LIB parseable benchmark).
     **/
    @Override
    public String toString()
    {
        return Native.optimizeToString(getContext().nCtx(), getNativeObject());
    }

    /**
     * Parse an SMT-LIB2 file with optimization objectives and constraints.
     * The parsed constraints and objectives are added to the optimization context.
     */
    public void fromFile(String file)
    {
        Native.optimizeFromFile(getContext().nCtx(), getNativeObject(), file);
    }

    /**
     * Similar to FromFile. Instead it takes as argument a string.
     */
    public void fromString(String s)
    {
        Native.optimizeFromString(getContext().nCtx(), getNativeObject(), s);
    }

    /**
     * The set of asserted formulas.
     */
    public BoolExpr[] getAssertions() 
    {
        ASTVector assertions = new ASTVector(getContext(), Native.optimizeGetAssertions(getContext().nCtx(), getNativeObject()));
        return assertions.ToBoolExprArray();
    }

    /**
     * The set of asserted formulas.
     */
    public Expr[] getObjectives() 
    {
        ASTVector objectives = new ASTVector(getContext(), Native.optimizeGetObjectives(getContext().nCtx(), getNativeObject()));
        return objectives.ToExprArray();
    }

    /**
     *  Optimize statistics.
     **/
    public Statistics getStatistics()
    {
        return new Statistics(getContext(), Native.optimizeGetStatistics(getContext().nCtx(), getNativeObject()));
    }


    Optimize(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }

    Optimize(Context ctx) throws Z3Exception
    {
        super(ctx, Native.mkOptimize(ctx.nCtx()));
    }

    @Override
    void incRef() {
        Native.optimizeIncRef(getContext().nCtx(), getNativeObject());
    }

    @Override
    void addToReferenceQueue() {
        getContext().getOptimizeDRQ().storeReference(getContext(), this);
    }
}
