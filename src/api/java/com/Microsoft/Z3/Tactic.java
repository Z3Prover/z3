/**
 * This file was automatically generated from Tactic.cs 
 **/

package com.Microsoft.Z3;

import java.math.BigInteger;
import java.util.*;
import java.lang.Exception;

/* using System; */

    /**
     * Tactics are the basic building block for creating custom solvers for specific problem domains.
     * The complete list of tactics may be obtained using <code>Context.NumTactics</code> 
     * and <code>Context.TacticNames</code>.
     * It may also be obtained using the command <code>(help-tactics)</code> in the SMT 2.0 front-end.
     **/
    public class Tactic extends Z3Object
    {
        /**
         * A string containing a description of parameters accepted by the tactic.
         **/
        public String Help() 
            {
                

                return Native.tacticGetHelp(Context().nCtx(), NativeObject());
            }


        /**
         * Retrieves parameter descriptions for Tactics.
         **/
        public ParamDescrs ParameterDescriptions()  { return new ParamDescrs(Context, Native.tacticGetParamDescrs(Context().nCtx(), NativeObject())); }


        /**
         * Execute the tactic over the goal. 
         **/
        public ApplyResult Apply(Goal g, Params p)
        {
            
            

            Context.CheckContextMatch(g);
            if (p == null)
                return new ApplyResult(Context, Native.tacticApply(Context().nCtx(), NativeObject(), g.NativeObject));
            else
            {
                Context.CheckContextMatch(p);
                return new ApplyResult(Context, Native.tacticApplyEx(Context().nCtx(), NativeObject(), g.NativeObject, p.NativeObject));
            }
        }

        /**
         * Apply the tactic to a goal.
         **/
        public ApplyResult get(Goal g) 
            {
                
                

                return Apply(g);
            }

        /**
         * Creates a solver that is implemented using the given tactic.
         * <seealso cref="Context.MkSolver(Tactic)"/>
         **/
        public Solver Solver() 
            {
                

                return Context.MkSolver(this);
            }

        Tactic(Context ctx, long obj)
        { super(ctx, obj);
            
        }
        Tactic(Context ctx, String name)
        { super(ctx, Native.mkTactic(ctx.nCtx(), name));
            
        }

        class DecRefQueue extends IDecRefQueue
        {
            public void IncRef(Context ctx, long obj)
            {
                Native.tacticIncRef(ctx.nCtx(), obj);
            }

            public void DecRef(Context ctx, long obj)
            {
                Native.tacticDecRef(ctx.nCtx(), obj);
            }
        };

        void IncRef(long o)
        {
            Context.Tactic_DRQ.IncAndClear(Context, o);
            super.IncRef(o);
        }

        void DecRef(long o)
        {
            Context.Tactic_DRQ.Add(o);
            super.DecRef(o);
        }
    }
