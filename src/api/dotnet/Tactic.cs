﻿/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    Tactic.cs

Abstract:

    Z3 Managed API: Tactics

Author:

    Christoph Wintersteiger (cwinter) 2012-03-21

Notes:
    
--*/

using System;
using System.Diagnostics;

namespace Microsoft.Z3
{
    /// <summary>
    /// Tactics are the basic building block for creating custom solvers for specific problem domains.
    /// The complete list of tactics may be obtained using <c>Context.NumTactics</c> 
    /// and <c>Context.TacticNames</c>.
    /// It may also be obtained using the command <c>(help-tactic)</c> in the SMT 2.0 front-end.
    /// </summary>
    public class Tactic : Z3Object
    {
        /// <summary>
        /// A string containing a description of parameters accepted by the tactic.
        /// </summary>
        public string Help
        {
            get
            {

                return Native.Z3_tactic_get_help(Context.nCtx, NativeObject);
            }
        }


        /// <summary>
        /// Retrieves parameter descriptions for Tactics.
        /// </summary>
        public ParamDescrs ParameterDescriptions
        {
            get { return new ParamDescrs(Context, Native.Z3_tactic_get_param_descrs(Context.nCtx, NativeObject)); }
        }


        /// <summary>
        /// Execute the tactic over the goal. 
        /// </summary>
        public ApplyResult Apply(Goal g, Params p = null)
        {
            Debug.Assert(g != null);

            Context.CheckContextMatch(g);
            if (p == null)
                return new ApplyResult(Context, Native.Z3_tactic_apply(Context.nCtx, NativeObject, g.NativeObject));
            else
            {
                Context.CheckContextMatch(p);
                return new ApplyResult(Context, Native.Z3_tactic_apply_ex(Context.nCtx, NativeObject, g.NativeObject, p.NativeObject));
            }
        }

        /// <summary>
        /// Apply the tactic to a goal.
        /// </summary>
        public ApplyResult this[Goal g]
        {
            get
            {
                Debug.Assert(g != null);

                return Apply(g);
            }
        }

        /// <summary>
        /// Creates a solver that is implemented using the given tactic.
        /// </summary>
        /// <seealso cref="Context.MkSolver(Tactic)"/>
        public Solver Solver
        {
            get
            {

                return Context.MkSolver(this);
            }
        }

        #region Internal
        internal Tactic(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Debug.Assert(ctx != null);
        }
        internal Tactic(Context ctx, string name)
            : base(ctx, Native.Z3_mk_tactic(ctx.nCtx, name))
        {
            Debug.Assert(ctx != null);
        }

        /// <summary>
        /// DecRefQueue
        /// </summary>
        internal class DecRefQueue : IDecRefQueue
        {
            public DecRefQueue() : base() { }
            public DecRefQueue(uint move_limit) : base(move_limit) { }
            internal override void IncRef(Context ctx, IntPtr obj)
            {
                Native.Z3_tactic_inc_ref(ctx.nCtx, obj);
            }

            internal override void DecRef(Context ctx, IntPtr obj)
            {
                Native.Z3_tactic_dec_ref(ctx.nCtx, obj);
            }
        };

        internal override void IncRef(IntPtr o)
        {
            Context.Tactic_DRQ.IncAndClear(Context, o);
            base.IncRef(o);
        }

        internal override void DecRef(IntPtr o)
        {
            Context.Tactic_DRQ.Add(o);
            base.DecRef(o);
        }
        #endregion
    }
}
