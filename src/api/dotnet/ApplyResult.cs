/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    ApplyResult.cs

Abstract:

    Z3 Managed API: Result object for tactic applications

Author:

    Christoph Wintersteiger (cwinter) 2012-03-21

Notes:
    
--*/

using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// ApplyResult objects represent the result of an application of a 
    /// tactic to a goal. It contains the subgoals that were produced.
    /// </summary>
    [ContractVerification(true)]
    public class ApplyResult : Z3Object
    {
        /// <summary>
        /// The number of Subgoals.
        /// </summary>
        public uint NumSubgoals
        {
            get { return Native.Z3_apply_result_get_num_subgoals(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// Retrieves the subgoals from the ApplyResult.
        /// </summary>
        public Goal[] Subgoals
        {
            get
            {
                Contract.Ensures(Contract.Result<Goal[]>() != null);
                Contract.Ensures(Contract.Result<Goal[]>().Length == this.NumSubgoals);

                uint n = NumSubgoals;
                Goal[] res = new Goal[n];
                for (uint i = 0; i < n; i++)
                    res[i] = new Goal(Context, Native.Z3_apply_result_get_subgoal(Context.nCtx, NativeObject, i));
                return res;
            }
        }

        /// <summary>
        /// Convert a model for the subgoal <paramref name="i"/> into a model for the original 
        /// goal <c>g</c>, that the ApplyResult was obtained from. 
        /// </summary>
        /// <returns>A model for <c>g</c></returns>
        public Model ConvertModel(uint i, Model m)
        {
            Contract.Requires(m != null);
            Contract.Ensures(Contract.Result<Model>() != null);

            return new Model(Context, Native.Z3_apply_result_convert_model(Context.nCtx, NativeObject, i, m.NativeObject));
        }

        /// <summary>
        /// A string representation of the ApplyResult.
        /// </summary>
        public override string ToString()
        {
            return Native.Z3_apply_result_to_string(Context.nCtx, NativeObject);
        }

        #region Internal
        internal ApplyResult(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }

        internal class DecRefQueue : IDecRefQueue
        {
            public DecRefQueue() : base() { }
            public DecRefQueue(uint move_limit) : base(move_limit) { }
            internal override void IncRef(Context ctx, IntPtr obj)
            {
                Native.Z3_apply_result_inc_ref(ctx.nCtx, obj);
            }

            internal override void DecRef(Context ctx, IntPtr obj)
            {
                Native.Z3_apply_result_dec_ref(ctx.nCtx, obj);
            }
        };

        internal override void IncRef(IntPtr o)
        {
            Context.ApplyResult_DRQ.IncAndClear(Context, o);
            base.IncRef(o);
        }

        internal override void DecRef(IntPtr o)
        {
            Context.ApplyResult_DRQ.Add(o);
            base.DecRef(o);
        }
        #endregion
    }
}
