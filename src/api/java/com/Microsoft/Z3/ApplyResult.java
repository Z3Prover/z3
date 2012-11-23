/**
 * This file was automatically generated from ApplyResult.cs 
 **/

package com.Microsoft.Z3;

/* using System; */

    /**
     * ApplyResult objects represent the result of an application of a 
     * tactic to a goal. It contains the subgoals that were produced.
     **/
    public class ApplyResult extends Z3Object
    {
        /**
         * The number of Subgoals.
         **/
        public long NumSubgoals()  { return Native.applyResultGetNumSubgoals(Context.nCtx, NativeObject); }

        /**
         * Retrieves the subgoals from the ApplyResult.
         **/
        public Goal[] Subgoals() 
            {
              
              

                long n = NumSubgoals;
                Goal[] res = new Goal[n];
                for (long i = 0; i < n; i++)
                    res[i] = new Goal(Context, Native.applyResultGetSubgoal(Context.nCtx, NativeObject, i));
                return res;
            }

        /**
         * Convert a model for the subgoal <paramref name="i"/> into a model for the original 
         * goal <code>g</code>, that the ApplyResult was obtained from. 
         * @return A model for <code>g</code>
         **/
        public Model ConvertModel(long i, Model m)
        {
            
            

            return new Model(Context, Native.applyResultConvertModel(Context.nCtx, NativeObject, i, m.NativeObject));
        }

        /**
         * A string representation of the ApplyResult.
         **/
        public String toString()
        {
            return Native.applyResulttoString(Context.nCtx, NativeObject);
        }

        ApplyResult(Context ctx, IntPtr obj) { super(ctx, obj); 
            
        }

        class DecRefQueue extends Z3.DecRefQueue
        {
            public void IncRef(Context ctx, IntPtr obj)
            {
                Native.applyResultIncRef(ctx.nCtx, obj);
            }

            public void DecRef(Context ctx, IntPtr obj)
            {
                Native.applyResultDecRef(ctx.nCtx, obj);
            }
        };        

        void IncRef(IntPtr o)
        {
            Context.ApplyResult_DRQ.IncAndClear(Context, o);
            super.IncRef(o);
        }

        void DecRef(IntPtr o)
        {
            Context.ApplyResult_DRQ.Add(o);
            super.DecRef(o);
        }
    }
