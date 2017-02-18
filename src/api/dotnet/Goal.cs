/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    Goal.cs

Abstract:

    Z3 Managed API: Goal

Author:

    Christoph Wintersteiger (cwinter) 2012-03-21

Notes:
    
--*/

using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// A goal (aka problem). A goal is essentially a set
    /// of formulas, that can be solved and/or transformed using
    /// tactics and solvers.
    /// </summary>
    [ContractVerification(true)]
    public class Goal : Z3Object
    {
        /// <summary>
        /// The precision of the goal. 
        /// </summary>
        /// <remarks>
        /// Goals can be transformed using over and under approximations.
        /// An under approximation is applied when the objective is to find a model for a given goal.
        /// An over approximation is applied when the objective is to find a proof for a given goal.
        /// </remarks>
        public Z3_goal_prec Precision
        {
            get { return (Z3_goal_prec)Native.Z3_goal_precision(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// Indicates whether the goal is precise.
        /// </summary>
        public bool IsPrecise
        {
            get { return Precision == Z3_goal_prec.Z3_GOAL_PRECISE; }
        }
        /// <summary>
        /// Indicates whether the goal is an under-approximation.
        /// </summary>
        public bool IsUnderApproximation
        {
            get { return Precision == Z3_goal_prec.Z3_GOAL_UNDER; }
        }

        /// <summary>
        /// Indicates whether the goal is an over-approximation.
        /// </summary>
        public bool IsOverApproximation
        {
            get { return Precision == Z3_goal_prec.Z3_GOAL_OVER; }
        }

        /// <summary>
        /// Indicates whether the goal is garbage (i.e., the product of over- and under-approximations).
        /// </summary>
        public bool IsGarbage
        {
            get { return Precision == Z3_goal_prec.Z3_GOAL_UNDER_OVER; }
        }

        /// <summary>
        /// Adds the <paramref name="constraints"/> to the given goal. 
        /// </summary>   
        public void Assert(params BoolExpr[] constraints)
        {
            Contract.Requires(constraints != null);
            Contract.Requires(Contract.ForAll(constraints, c => c != null));

            Context.CheckContextMatch<BoolExpr>(constraints);
            foreach (BoolExpr c in constraints)
            {
                Contract.Assert(c != null); // It was an assume, now made an assert just to be sure we do not regress
                Native.Z3_goal_assert(Context.nCtx, NativeObject, c.NativeObject);
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
        /// Indicates whether the goal contains `false'.
        /// </summary>
        public bool Inconsistent
        {
            get { return Native.Z3_goal_inconsistent(Context.nCtx, NativeObject) != 0; }
        }

        /// <summary>
        /// The depth of the goal.
        /// </summary>
        /// <remarks>
        /// This tracks how many transformations were applied to it.
        /// </remarks>
        public uint Depth
        {
            get { return Native.Z3_goal_depth(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// Erases all formulas from the given goal.
        /// </summary>
        public void Reset()
        {
            Native.Z3_goal_reset(Context.nCtx, NativeObject);
        }

        /// <summary>
        /// The number of formulas in the goal.
        /// </summary>
        public uint Size
        {
            get { return Native.Z3_goal_size(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// The formulas in the goal.
        /// </summary>
        public BoolExpr[] Formulas
        {
            get
            {
                Contract.Ensures(Contract.Result<BoolExpr[]>() != null);

                uint n = Size;
                BoolExpr[] res = new BoolExpr[n];
                for (uint i = 0; i < n; i++)
                    res[i] = new BoolExpr(Context, Native.Z3_goal_formula(Context.nCtx, NativeObject, i));
                return res;
            }
        }

        /// <summary>
        /// The number of formulas, subformulas and terms in the goal.
        /// </summary>
        public uint NumExprs
        {
            get { return Native.Z3_goal_num_exprs(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// Indicates whether the goal is empty, and it is precise or the product of an under approximation.
        /// </summary>
        public bool IsDecidedSat
        {
            get { return Native.Z3_goal_is_decided_sat(Context.nCtx, NativeObject) != 0; }
        }

        /// <summary>
        /// Indicates whether the goal contains `false', and it is precise or the product of an over approximation.
        /// </summary>
        public bool IsDecidedUnsat
        {
            get { return Native.Z3_goal_is_decided_unsat(Context.nCtx, NativeObject) != 0; }
        }

        /// <summary>
        /// Translates (copies) the Goal to the target Context <paramref name="ctx"/>.
        /// </summary>
        public Goal Translate(Context ctx)
        {
            Contract.Requires(ctx != null);

            return new Goal(ctx, Native.Z3_goal_translate(Context.nCtx, NativeObject, ctx.nCtx));
        }

        /// <summary>
        /// Simplifies the goal.
        /// </summary>
        /// <remarks>Essentially invokes the `simplify' tactic on the goal.</remarks>
        public Goal Simplify(Params p = null)
        {
            Tactic t = Context.MkTactic("simplify");
            ApplyResult res = t.Apply(this, p);

            if (res.NumSubgoals == 0)
                throw new Z3Exception("No subgoals");
            else
                return res.Subgoals[0];
        }

        /// <summary>
        /// Goal to string conversion.
        /// </summary>
        /// <returns>A string representation of the Goal.</returns>
        public override string ToString()
        {
            return Native.Z3_goal_to_string(Context.nCtx, NativeObject);
        }

        /// <summary>
        /// Goal to BoolExpr conversion.
        /// </summary>
        /// <returns>A string representation of the Goal.</returns>
        public BoolExpr AsBoolExpr() {
            uint n = Size;
            if (n == 0) 
                return Context.MkTrue();
            else if (n == 1)                
                return Formulas[0];
            else {
                return Context.MkAnd(Formulas);
            }
        }

        #region Internal
        internal Goal(Context ctx, IntPtr obj) : base(ctx, obj) { Contract.Requires(ctx != null); }

        internal Goal(Context ctx, bool models, bool unsatCores, bool proofs)
            : base(ctx, Native.Z3_mk_goal(ctx.nCtx, (models) ? 1 : 0, (unsatCores) ? 1 : 0, (proofs) ? 1 : 0))
        {
            Contract.Requires(ctx != null);
        }

        internal class DecRefQueue : IDecRefQueue
        {
            public DecRefQueue() : base() { }
            public DecRefQueue(uint move_limit) : base(move_limit) { }
            internal override void IncRef(Context ctx, IntPtr obj)
            {
                Native.Z3_goal_inc_ref(ctx.nCtx, obj);
            }

            internal override void DecRef(Context ctx, IntPtr obj)
            {
                Native.Z3_goal_dec_ref(ctx.nCtx, obj);
            }
        };        

        internal override void IncRef(IntPtr o)
        {
            Context.Goal_DRQ.IncAndClear(Context, o);
            base.IncRef(o);
        }

        internal override void DecRef(IntPtr o)
        {
            Context.Goal_DRQ.Add(o);
            base.DecRef(o);
        }

        #endregion
    }
}
