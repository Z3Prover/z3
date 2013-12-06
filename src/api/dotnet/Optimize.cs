/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    Optimize.cs

Abstract:

    Z3 Managed API: Optimizes

Author:

    Nikolaj Bjorner (nbjorner) 2013-12-03

Notes:
    
--*/

using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// Object for managing optimizization context
    /// </summary>
    [ContractVerification(true)]
    public class Optimize : Z3Object
    {
        HashSet<uint> indices;

#if false
        /// <summary>
        /// A string that describes all available optimize solver parameters.
        /// </summary>
        public string Help
        {
            get
            {
                Contract.Ensures(Contract.Result<string>() != null);
                return Native.Z3_optimize_get_help(Context.nCtx, NativeObject);
            }
        }
#endif

        /// <summary>
        /// Sets the optimize solver parameters.
        /// </summary>
        public Params Parameters
        {
            set
            {
                Contract.Requires(value != null);
                Context.CheckContextMatch(value);
                Native.Z3_optimize_set_params(Context.nCtx, NativeObject, value.NativeObject);
            }
        }

        /// <summary>
        /// Retrieves parameter descriptions for Optimize solver.
        /// </summary>
        public ParamDescrs ParameterDescriptions
        {
            get { return new ParamDescrs(Context, Native.Z3_optimize_get_param_descrs(Context.nCtx, NativeObject)); }
        }

        /// <summary>
        /// Get the number of objectives.
        /// </summary>
        public uint ObjectiveCount
        {
            get { return (uint)indices.Count; }
        }

        /// <summary>
        /// Get all indices of objectives.
        /// </summary>
        public uint[] Objectives
        {
            get 
            {
                var objectives = new uint[indices.Count];
                indices.CopyTo(objectives, 0);
                return objectives;
            }
        }

        /// <summary>
        /// Assert a constraint (or multiple) into the optimize solver.
        /// </summary>        
        public void Assert(params BoolExpr[] constraints)
        {
            Contract.Requires(constraints != null);
            Contract.Requires(Contract.ForAll(constraints, c => c != null));

            Context.CheckContextMatch(constraints);
            foreach (BoolExpr a in constraints)
            {
                Native.Z3_optimize_assert(Context.nCtx, NativeObject, a.NativeObject);
            }
        }

        /// <summary>
        /// Alias for Assert.
        /// </summary>        
        public void Add(params BoolExpr[] constraints)
        {
            Assert(constraints);
        }

        /// <summary>
        /// Assert soft constraint
        /// </summary>        
        /// <remarks>
        /// Return an objective which associates with the group of constraints.
        /// </remarks>
        public uint AssertSoft(BoolExpr constraint, uint weight, string group)
        {
            Context.CheckContextMatch(constraint);
	        Symbol s = Context.MkSymbol(group);            
	        uint index = Native.Z3_optimize_assert_soft(Context.nCtx, NativeObject, constraint.NativeObject, weight.ToString(), s.NativeObject);
            indices.Add(index);
            return index;
        }
	
	    public Status Check() {
	        Z3_lbool r = (Z3_lbool)Native.Z3_optimize_check(Context.nCtx, NativeObject);
            switch (r)
            {
                case Z3_lbool.Z3_L_TRUE: 
                    return Status.SATISFIABLE;
                case Z3_lbool.Z3_L_FALSE: 
                    return Status.UNSATISFIABLE;
                default: 
                    return Status.UNKNOWN;
            }         
        }

        /// <summary>
        /// The model of the last <c>Check</c>.
        /// </summary>
        /// <remarks>
        /// The result is <c>null</c> if <c>Check</c> was not invoked before,
        /// if its results was not <c>SATISFIABLE</c>, or if model production is not enabled.
        /// </remarks>
        public Model Model
        {
            get
            {
                IntPtr x = Native.Z3_optimize_get_model(Context.nCtx, NativeObject);
                if (x == IntPtr.Zero)
                    return null;
                else
                    return new Model(Context, x);
            }
        }
        	
	    public uint MkMaximize(ArithExpr e) 
        {
	        uint index = Native.Z3_optimize_maximize(Context.nCtx, NativeObject, e.NativeObject);
            indices.Add(index);
            return index;
	    }

        public uint MkMinimize(ArithExpr e)
        {
	        uint index = Native.Z3_optimize_minimize(Context.nCtx, NativeObject, e.NativeObject);
            indices.Add(index);
            return index;
	    }

	    public ArithExpr GetLower(uint index) 
        {
            Contract.Requires(indices.Contains(index));
	        return new ArithExpr(Context, Native.Z3_optimize_get_lower(Context.nCtx, NativeObject, index));
        }

        public ArithExpr GetUpper(uint index)
        {
            Contract.Requires(indices.Contains(index));
	        return new ArithExpr(Context, Native.Z3_optimize_get_upper(Context.nCtx, NativeObject, index));
        }

        #region Internal
        internal Optimize(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
            indices = new HashSet<uint>();
        }
        internal Optimize(Context ctx)
            : base(ctx, Native.Z3_mk_optimize(ctx.nCtx))
        {
            Contract.Requires(ctx != null);
            indices = new HashSet<uint>();
        }

        internal class DecRefQueue : IDecRefQueue
        {
            public override void IncRef(Context ctx, IntPtr obj)
            {
                Native.Z3_optimize_inc_ref(ctx.nCtx, obj);
            }

            public override void DecRef(Context ctx, IntPtr obj)
            {
                Native.Z3_optimize_dec_ref(ctx.nCtx, obj);
            }
        };

        internal override void IncRef(IntPtr o)
        {
            Context.Optimize_DRQ.IncAndClear(Context, o);
            base.IncRef(o);
        }

        internal override void DecRef(IntPtr o)
        {
            Context.Optimize_DRQ.Add(o);
            base.DecRef(o);
        }
        #endregion
    }
}
