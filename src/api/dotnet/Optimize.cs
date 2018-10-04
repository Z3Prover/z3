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
        /// Assert a constraint (or multiple) into the optimize solver.
        /// </summary>        
        public void Assert(params BoolExpr[] constraints)
        {
            AddConstraints(constraints);
        }

        /// <summary>
        /// Assert a constraint (or multiple) into the optimize solver.
        /// </summary>        
        public void Assert(IEnumerable<BoolExpr> constraints)
        {
            AddConstraints(constraints);
        }

        /// <summary>
        /// Alias for Assert.
        /// </summary>        
        public void Add(params BoolExpr[] constraints)
        {
            AddConstraints(constraints);
        }

        /// <summary>
        /// Alias for Assert.
        /// </summary>        
        public void Add(IEnumerable<BoolExpr> constraints)
        {
            AddConstraints(constraints);
        }

        /// <summary>
        /// Assert a constraint (or multiple) into the optimize solver.
        /// </summary>   
        private void AddConstraints(IEnumerable<BoolExpr> constraints)
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
        /// Handle to objectives returned by objective functions.
        /// </summary>
        public class Handle
        {
            Optimize opt;
            uint handle;
            internal Handle(Optimize opt, uint h)
            {
                this.opt = opt;
                this.handle = h;
            }

            /// <summary>
            /// Retrieve a lower bound for the objective handle.
            /// </summary>                   
            public Expr Lower
            {
                get { return opt.GetLower(handle); }
            }

            /// <summary>
            /// Retrieve an upper bound for the objective handle.
            /// </summary>                   
            public Expr Upper
            {
                get { return opt.GetUpper(handle); }
            }

            /// <summary>
            /// Retrieve the value of an objective.
            /// </summary>                   
            public Expr Value
            {
                get { return Lower; }
            }

            /// <summary>
            /// Retrieve a lower bound for the objective handle.
            /// </summary>                   
            public Expr[] LowerAsVector
            {
                get { return opt.GetLowerAsVector(handle); }
            }

            /// <summary>
            /// Retrieve an upper bound for the objective handle.
            /// </summary>                   
            public Expr[] UpperAsVector
            {
                get { return opt.GetUpperAsVector(handle); }
            }

        }

        /// <summary>
        /// Assert soft constraint
        /// </summary>        
        /// <remarks>
        /// Return an objective which associates with the group of constraints.
        /// </remarks>
        public Handle AssertSoft(BoolExpr constraint, uint weight, string group)
        {
            Context.CheckContextMatch(constraint);
            Symbol s = Context.MkSymbol(group);
            return new Handle(this, Native.Z3_optimize_assert_soft(Context.nCtx, NativeObject, constraint.NativeObject, weight.ToString(), s.NativeObject));
        }


        /// <summary>
        /// Check satisfiability of asserted constraints.
        /// Produce a model that (when the objectives are bounded and 
        /// don't use strict inequalities) meets the objectives.
        /// </summary>
        ///
        public Status Check(params Expr[] assumptions)
        {
            Z3_lbool r = (Z3_lbool)Native.Z3_optimize_check(Context.nCtx, NativeObject, (uint)assumptions.Length, AST.ArrayToNative(assumptions));
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
        /// Creates a backtracking point.
        /// </summary>
        /// <seealso cref="Pop"/>
        public void Push()
        {
            Native.Z3_optimize_push(Context.nCtx, NativeObject);
        }

        /// <summary>
        /// Backtrack one backtracking point.
        /// </summary>
        /// <remarks>Note that an exception is thrown if Pop is called without a corresponding <c>Push</c></remarks>
        /// <seealso cref="Push"/>
        public void Pop()
        {
            Native.Z3_optimize_pop(Context.nCtx, NativeObject);
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

        /// <summary>
        /// The unsat core of the last <c>Check</c>.
        /// </summary>
        /// <remarks>
        /// The unsat core is a subset of <c>assumptions</c>
        /// The result is empty if <c>Check</c> was not invoked before,
        /// if its results was not <c>UNSATISFIABLE</c>, or if core production is disabled.
        /// </remarks>
        public BoolExpr[] UnsatCore
        {
            get
            {
                Contract.Ensures(Contract.Result<Expr[]>() != null);

                ASTVector core = new ASTVector(Context, Native.Z3_optimize_get_unsat_core(Context.nCtx, NativeObject));                
                return core.ToBoolExprArray();
            }
        }

        /// <summary>
        /// Declare an arithmetical maximization objective.
        /// Return a handle to the objective. The handle is used as
        /// to retrieve the values of objectives after calling Check.
        /// The expression can be either an arithmetical expression or bit-vector.
        /// </summary>            
        public Handle MkMaximize(Expr e)
        {
            return new Handle(this, Native.Z3_optimize_maximize(Context.nCtx, NativeObject, e.NativeObject));
        }

        /// <summary>
        /// Declare an arithmetical minimization objective. 
        /// Similar to MkMaximize.
        /// </summary>            
        public Handle MkMinimize(Expr e)
        {
            return new Handle(this, Native.Z3_optimize_minimize(Context.nCtx, NativeObject, e.NativeObject));
        }


        /// <summary>
        /// Retrieve a lower bound for the objective handle.
        /// </summary>            
        private Expr GetLower(uint index)
        {
            return Expr.Create(Context, Native.Z3_optimize_get_lower(Context.nCtx, NativeObject, index));
        }


        /// <summary>
        /// Retrieve an upper bound for the objective handle.
        /// </summary>            
        private Expr GetUpper(uint index)
        {
            return Expr.Create(Context, Native.Z3_optimize_get_upper(Context.nCtx, NativeObject, index));
        }

        /// <summary>
        /// Retrieve a lower bound for the objective handle.
        /// </summary>            
        private Expr[] GetLowerAsVector(uint index)
        {
            ASTVector v = new ASTVector(Context, Native.Z3_optimize_get_lower_as_vector(Context.nCtx, NativeObject, index));
            return v.ToExprArray();
        }


        /// <summary>
        /// Retrieve an upper bound for the objective handle.
        /// </summary>            
        private Expr[] GetUpperAsVector(uint index)
        {
            ASTVector v = new ASTVector(Context, Native.Z3_optimize_get_upper_as_vector(Context.nCtx, NativeObject, index));
            return v.ToExprArray();
        }

    /// <summary>
    /// Return a string the describes why the last to check returned unknown
    /// </summary>    
        public String ReasonUnknown
        {
            get 
            {
                Contract.Ensures(Contract.Result<string>() != null);
                return Native.Z3_optimize_get_reason_unknown(Context.nCtx, NativeObject);
            }
        }


        /// <summary>
        /// Print the context to a string (SMT-LIB parseable benchmark).
        /// </summary>            
        public override string ToString()
        {
            return Native.Z3_optimize_to_string(Context.nCtx, NativeObject);
        }

        /// <summary>
        /// Parse an SMT-LIB2 file with optimization objectives and constraints.
        /// The parsed constraints and objectives are added to the optimization context.
        /// </summary>                
        public void FromFile(string file)
        {
            Native.Z3_optimize_from_file(Context.nCtx, NativeObject, file);
        }

        /// <summary>
        /// Similar to FromFile. Instead it takes as argument a string.
        /// </summary>
        public void FromString(string s)
        {
            Native.Z3_optimize_from_string(Context.nCtx, NativeObject, s);
        }

        /// <summary>
        /// The set of asserted formulas.
        /// </summary>
        public BoolExpr[] Assertions
        {
            get
            {
                Contract.Ensures(Contract.Result<BoolExpr[]>() != null);

                ASTVector assertions = new ASTVector(Context, Native.Z3_optimize_get_assertions(Context.nCtx, NativeObject));
                return assertions.ToBoolExprArray();
            }
        }

        /// <summary>
        /// The set of asserted formulas.
        /// </summary>
        public Expr[] Objectives
        {
            get
            {
                Contract.Ensures(Contract.Result<Expr[]>() != null);

                ASTVector objectives = new ASTVector(Context, Native.Z3_optimize_get_objectives(Context.nCtx, NativeObject));
                return objectives.ToExprArray();
            }
        }


        /// <summary>
        /// Optimize statistics.
        /// </summary>
        public Statistics Statistics
        {
            get
            {
                Contract.Ensures(Contract.Result<Statistics>() != null);

                return new Statistics(Context, Native.Z3_optimize_get_statistics(Context.nCtx, NativeObject));
            }
        }


        #region Internal
        internal Optimize(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }
        internal Optimize(Context ctx)
            : base(ctx, Native.Z3_mk_optimize(ctx.nCtx))
        {
            Contract.Requires(ctx != null);
        }

        internal class DecRefQueue : IDecRefQueue
        {
            public DecRefQueue() : base() { }
            public DecRefQueue(uint move_limit) : base(move_limit) { }
            internal override void IncRef(Context ctx, IntPtr obj)
            {
                Native.Z3_optimize_inc_ref(ctx.nCtx, obj);
            }

            internal override void DecRef(Context ctx, IntPtr obj)
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
