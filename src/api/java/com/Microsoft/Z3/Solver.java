/**
 * This file was automatically generated from Solver.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;
import com.Microsoft.Z3.Enumerations.*;

/* using System; */

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
         **/
        public void setParameters(Params value) 
            {
                

                Context().CheckContextMatch(value);
                Native.solverSetParams(Context().nCtx(), NativeObject(), value.NativeObject());
            }

        /**
         * Retrieves parameter descriptions for solver.
         **/
        public ParamDescrs ParameterDescriptions()  { return new ParamDescrs(Context(), Native.solverGetParamDescrs(Context().nCtx(), NativeObject())); }


        /**
         * The current number of backtracking points (scopes).
         * <seealso cref="Pop"/>
         * <seealso cref="Push"/>
         **/
        public int NumScopes()  { return Native.solverGetNumScopes(Context().nCtx(), NativeObject()); }

        /**
         * Creates a backtracking point.
         * <seealso cref="Pop"/>
         **/
        public void Push()
        {
            Native.solverPush(Context().nCtx(), NativeObject());
        }

        /**
         * Backtracks <paramref name="n"/> backtracking points.
         * <remarks>Note that an exception is thrown if <paramref name="n"/> is not smaller than <code>NumScopes</code></remarks>
         * <seealso cref="Push"/>
         **/
        public void Pop(int n)
        {
            Native.solverPop(Context().nCtx(), NativeObject(), n);
        }

        /**
         * Resets the Solver.
         * <remarks>This removes all assertions from the solver.</remarks>
         **/
        public void Reset()
        {
            Native.solverReset(Context().nCtx(), NativeObject());
        }

        /**
         * Assert a constraint (or multiple) into the solver.
         **/
        public void Assert(BoolExpr[] constraints)
        {
            
            

            Context().CheckContextMatch(constraints);
            for (BoolExpr a: constraints)
            {
                Native.solverAssert(Context().nCtx(), NativeObject(), a.NativeObject());
            }
        }

        /**
         * The number of assertions in the solver.
         **/
        public int NumAssertions() 
            {
                ASTVector ass = new ASTVector(Context(), Native.solverGetAssertions(Context().nCtx(), NativeObject()));
                return ass.Size;
            }

        /**
         * The set of asserted formulas.
         **/
        public BoolExpr[] Assertions() 
            {
                

                ASTVector ass = new ASTVector(Context(), Native.solverGetAssertions(Context().nCtx(), NativeObject()));
                int n = ass.Size;
                BoolExpr[] res = new BoolExpr[n];
                for (int i = 0; i < n; i++)
                    res[i] = new BoolExpr(Context(), ass[i].NativeObject());
                return res;
            }

        /**
         * Checks whether the assertions in the solver are consistent or not.
         * <remarks>
         * <seealso cref="Model"/>
         * <seealso cref="UnsatCore"/>
         * <seealso cref="Proof"/>    
         * </remarks>    
         **/
        public Status Check(Expr[] assumptions)
        {
            Z3_lbool r;
            if (assumptions == null)
                r = Z3_lbool.fromInt(Native.solverCheck(Context().nCtx(), NativeObject()));
            else
                r = Z3_lbool.fromInt(Native.solverCheckAssumptions(Context().nCtx(), NativeObject(), (int)assumptions.length, AST.ArrayToNative(assumptions)));
            switch (r)
            {
                case Z3_L_TRUE: return Status.SATISFIABLE;
                case Z3_L_FALSE: return Status.UNSATISFIABLE;
                default: return Status.UNKNOWN;
            }
        }

        /**
         * The model of the last <code>Check</code>.
         * <remarks>
         * The result is <code>null</code> if <code>Check</code> was not invoked before,
         * if its results was not <code>SATISFIABLE</code>, or if model production is not enabled.
         * </remarks>
         **/
        public Model Model() 
            {
                long x = Native.solverGetModel(Context().nCtx(), NativeObject());
                if (x == 0)
                    return null;
                else
                    return new Model(Context(), x);
            }

        /**
         * The proof of the last <code>Check</code>.
         * <remarks>    
         * The result is <code>null</code> if <code>Check</code> was not invoked before,
         * if its results was not <code>UNSATISFIABLE</code>, or if proof production is disabled.
         * </remarks>
         **/
        public Expr Proof() 
            {
                long x = Native.solverGetProof(Context().nCtx(), NativeObject());
                if (x == 0)
                    return null;
                else
                    return Expr.Create(Context(), x);
            }

        /**
         * The unsat core of the last <code>Check</code>.
         * <remarks>
         * The unsat core is a subset of <code>Assertions</code>
         * The result is empty if <code>Check</code> was not invoked before,
         * if its results was not <code>UNSATISFIABLE</code>, or if core production is disabled.
         * </remarks>
         **/
        public Expr[] UnsatCore() 
            {
                

                ASTVector core = new ASTVector(Context(), Native.solverGetUnsatCore(Context().nCtx(), NativeObject()));
                int n = core.Size;
                Expr[] res = new Expr[n];
                for (int i = 0; i < n; i++)
                    res[i] = Expr.Create(Context(), core[i].NativeObject());
                return res;
            }

        /**
         * A brief justification of why the last call to <code>Check</code> returned <code>UNKNOWN</code>.
         **/
        public String ReasonUnknown() 
            {
                

                return Native.solverGetReasonUnknown(Context().nCtx(), NativeObject());
            }

        /**
         * Solver statistics.
         **/
        public Statistics Statistics() 
            {
                

                return new Statistics(Context(), Native.solverGetStatistics(Context().nCtx(), NativeObject()));
            }

        /**
         * A string representation of the solver.
         **/
        public String toString()
        {
            return Native.solverToString(Context().nCtx(), NativeObject());
        }

        Solver(Context ctx, long obj)
        { super(ctx, obj);
            
        }

        class DecRefQueue extends IDecRefQueue
        {
            public void IncRef(Context ctx, long obj)
            {
                Native.solverIncRef(ctx.nCtx(), obj);
            }

            public void DecRef(Context ctx, long obj)
            {
                Native.solverDecRef(ctx.nCtx(), obj);
            }
        };

        void IncRef(long o)
        {
            Context().Solver_DRQ().IncAndClear(Context(), o);
            super.IncRef(o);
        }

        void DecRef(long o)
        {
            Context().Solver_DRQ().Add(o);
            super.DecRef(o);
        }
    }
