/**
 * This file was automatically generated from Probe.cs 
 **/

package com.Microsoft.Z3;

/* using System; */
/* using System.Runtime.InteropServices; */

    /**  
     * Probes are used to inspect a goal (aka problem) and collect information that may be used to decide
     * which solver and/or preprocessing step will be used.
     * The complete list of probes may be obtained using the procedures <code>Context.NumProbes</code>
     * and <code>Context.ProbeNames</code>.
     * It may also be obtained using the command <code>(help-tactics)</code> in the SMT 2.0 front-end.
     **/
    public class Probe extends Z3Object
    {
        /**
         * Execute the probe over the goal. 
         * @return A probe always produce a double value.
         * "Boolean" probes return 0.0 for false, and a value different from 0.0 for true.
         **/
        public double Apply(Goal g)
        {
            

            Context.CheckContextMatch(g);
            return Native.probeApply(Context.nCtx, NativeObject, g.NativeObject);
        }

        /**
         * Apply the probe to a goal.
         **/
        public double this[Goal() 
            

            return Apply(g); } }

        Probe(Context ctx, IntPtr obj)
            { super(ctx, obj);
            
        Probe(Context ctx, String name)
            { super(ctx, Native.mkProbe(ctx.nCtx, name));
            
        }

        class DecRefQueue extends Z3.DecRefQueue
        {
            public void IncRef(Context ctx, IntPtr obj)
            {
                Native.probeIncRef(ctx.nCtx, obj);
            }

            public void DecRef(Context ctx, IntPtr obj)
            {
                Native.probeDecRef(ctx.nCtx, obj);
            }
        };        

        void IncRef(IntPtr o)
        {
            Context.ProbeDRQ.IncAndClear(Context, o);
            super.IncRef(o);
        }

        void DecRef(IntPtr o)
        {
            Context.ProbeDRQ.Add(o);
            super.DecRef(o);
        }
    }
