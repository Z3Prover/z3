/**
 * This file was automatically generated from Goal.cs 
 **/

package com.Microsoft.Z3;

/* using System; */

    /**
     * A goal (aka problem). A goal is essentially a set
     * of formulas, that can be solved and/or transformed using
     * tactics and solvers.
     **/
    public class Goal extends Z3Object
    {
        /**
         * The precision of the goal. 
         * <remarks>
         * Goals can be transformed using over and under approximations.
         * An under approximation is applied when the objective is to find a model for a given goal.
         * An over approximation is applied when the objective is to find a proof for a given goal.
         * </remarks>
         **/
        public Z3_goal_prec Precision()  { return (Z3_goal_prec)Native.goalPrecision(Context.nCtx, NativeObject); }

        /**
         * Indicates whether the goal is precise.
         **/
        public boolean IsPrecise()  { return Precision == Z3_goal_prec.Z3_GOAL_PRECISE; }
        /**
         * Indicates whether the goal is an under-approximation.
         **/
        public boolean IsUnderApproximation()  { return Precision == Z3_goal_prec.Z3_GOAL_UNDER; }

        /**
         * Indicates whether the goal is an over-approximation.
         **/
        public boolean IsOverApproximation()  { return Precision == Z3_goal_prec.Z3_GOAL_OVER; }

        /**
         * Indicates whether the goal is garbage (i.e., the product of over- and under-approximations).
         **/
        public boolean IsGarbage()  { return Precision == Z3_goal_prec.Z3_GOAL_UNDER_OVER; }

        /**
         * Adds the <paramref name="constraints"/> to the given goal. 
         **/
        public void Assert(BoolExpr[] constraints)
        {
            
            

            Context.CheckContextMatch(constraints);
            for (BoolExpr.Iterator c = constraints.iterator(); c.hasNext(); )
            {
                 // It was an assume, now made an assert just to be sure we do not regress
                Native.goalAssert(Context.nCtx, NativeObject, c.NativeObject);
            }
        }

        /**
         * Indicates whether the goal contains `false'.
         **/
        public boolean Inconsistent()  { return Native.goalInconsistent(Context.nCtx, NativeObject) != 0; }

        /**
         * The depth of the goal.
         * <remarks>
         * This tracks how many transformations were applied to it.
         * </remarks>
         **/
        public long Depth()  { return Native.goalDepth(Context.nCtx, NativeObject); }

        /**
         * Erases all formulas from the given goal.
         **/
        public void Reset()
        {
            Native.goalReset(Context.nCtx, NativeObject);
        }

        /**
         * The number of formulas in the goal.
         **/
        public long Size()  { return Native.goalSize(Context.nCtx, NativeObject); }

        /**
         * The formulas in the goal.
         **/
        public BoolExpr[] Formulas() 
            {
                

                long n = Size;
                BoolExpr[] res = new BoolExpr[n];
                for (long i = 0; i < n; i++)
                    res[i] = new BoolExpr(Context, Native.goalFormula(Context.nCtx, NativeObject, i));
                return res;
            }

        /**
         * The number of formulas, subformulas and terms in the goal.
         **/
        public long NumExprs()  { return Native.goalNumExprs(Context.nCtx, NativeObject); }

        /**
         * Indicates whether the goal is empty, and it is precise or the product of an under approximation.
         **/
        public boolean IsDecidedSat()  { return Native.goalIsDecidedSat(Context.nCtx, NativeObject) != 0; }

        /**
         * Indicates whether the goal contains `false', and it is precise or the product of an over approximation.
         **/
        public boolean IsDecidedUnsat()  { return Native.goalIsDecidedUnsat(Context.nCtx, NativeObject) != 0; }

        /**
         * Translates (copies) the Goal to the target Context <paramref name="ctx"/>.
         **/
        public Goal Translate(Context ctx)
        {
            

            return new Goal(ctx, Native.goalTranslate(Context.nCtx, NativeObject, ctx.nCtx));
        }

        /**
         * Simplifies the goal.
         * <remarks>Essentially invokes the `simplify' tactic on the goal.</remarks>
         **/
        public Goal Simplify(Params p)
        {
            Tactic t = Context.MkTactic("simplify");
            ApplyResult res = t.Apply(this, p);
            
            if (res.NumSubgoals == 0)
                return Context.MkGoal();
            else        
                return res.Subgoals[0];
        }

        /**
         * Goal to string conversion.
         * @return A string representation of the Goal.
         **/
        public String toString()
        {
            return Native.goaltoString(Context.nCtx, NativeObject);
        }

        Goal(Context ctx, IntPtr obj) { super(ctx, obj);  }

        Goal(Context ctx, boolean models, boolean unsatCores, boolean proofs)
            { super(ctx, Native.mkGoal(ctx.nCtx, (models); ? 1 : 0, (unsatCores) ? 1 : 0, (proofs) ? 1 : 0))
            
        }

        class DecRefQueue extends Z3.DecRefQueue
        {
            public void IncRef(Context ctx, IntPtr obj)
            {
                Native.goalIncRef(ctx.nCtx, obj);
            }

            public void DecRef(Context ctx, IntPtr obj)
            {
                Native.goalDecRef(ctx.nCtx, obj);
            }
        };        

        void IncRef(IntPtr o)
        {
            Context.Goal_DRQ.IncAndClear(Context, o);
            super.IncRef(o);
        }

        void DecRef(IntPtr o)
        {
            Context.Goal_DRQ.Add(o);
            super.DecRef(o);
        }

    }
