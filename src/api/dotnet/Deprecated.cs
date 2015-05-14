/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    Deprecated.cs

Abstract:

    Expose deprecated features for use from the managed API 
    those who use them for experiments.

Author:

    Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
--*/
using System;
using System.Collections.Generic;
using System.Runtime.InteropServices;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// The main interaction with Z3 happens via the Context.
    /// </summary>
    [ContractVerification(true)]
    public class Deprecated 
    {

        /// <summary>
        /// Creates a backtracking point.
        /// </summary>
        /// <seealso cref="Pop"/>
         public static void Push(Context ctx) {
             Native.Z3_push(ctx.nCtx);
         }

        /// <summary>
        /// Backtracks <paramref name="n"/> backtracking points.
        /// </summary>
        /// <remarks>Note that an exception is thrown if <paramref name="n"/> is not smaller than <c>NumScopes</c></remarks>
        /// <seealso cref="Push"/>
         public static void Pop(Context ctx, uint n = 1) {
             Native.Z3_pop(ctx.nCtx, n);
         }

        /// <summary>
        /// Assert a constraint (or multiple) into the solver.
        /// </summary>        
         public static void Assert(Context ctx, params BoolExpr[] constraints) 
         {
            Contract.Requires(constraints != null);
            Contract.Requires(Contract.ForAll(constraints, c => c != null));

            ctx.CheckContextMatch(constraints);
            foreach (BoolExpr a in constraints)
            {
                Native.Z3_assert_cnstr(ctx.nCtx, a.NativeObject);
            }
         }
        /// <summary>
        /// Checks whether the assertions in the context are consistent or not.
        /// </summary>
        public static Status Check(Context ctx, List<BoolExpr> core, ref Model model, ref Expr proof, params Expr[] assumptions)
        {
            Z3_lbool r;
            model = null;
            proof = null;
            if (assumptions == null || assumptions.Length == 0)
                r = (Z3_lbool)Native.Z3_check(ctx.nCtx);
            else {
                IntPtr mdl = IntPtr.Zero, prf = IntPtr.Zero;
                uint core_size = 0;
                IntPtr[] native_core = new IntPtr[assumptions.Length];
                r = (Z3_lbool)Native.Z3_check_assumptions(ctx.nCtx, 
                                   (uint)assumptions.Length, AST.ArrayToNative(assumptions),
                                   ref mdl, ref prf, ref core_size, native_core);

                for (uint i = 0; i < core_size; i++)
                    core.Add((BoolExpr)Expr.Create(ctx, native_core[i]));
                if (mdl != IntPtr.Zero) {
                    model = new Model(ctx, mdl);
                }
                if (prf != IntPtr.Zero) {
                    proof = Expr.Create(ctx, prf);
                }

            }
            switch (r)
            {
                case Z3_lbool.Z3_L_TRUE: return Status.SATISFIABLE;
                case Z3_lbool.Z3_L_FALSE: return Status.UNSATISFIABLE;
                default: return Status.UNKNOWN;
            }
        }

        /// <summary>
        /// Retrieves an assignment to atomic propositions for a satisfiable context.
        /// </summary>
         public static BoolExpr GetAssignment(Context ctx) 
         {
             IntPtr x = Native.Z3_get_context_assignment(ctx.nCtx);
             return (BoolExpr)Expr.Create(ctx, x);
         }

    }
}