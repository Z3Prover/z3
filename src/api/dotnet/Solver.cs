/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    Solver.cs

Abstract:

    Z3 Managed API: Solvers

Author:

    Christoph Wintersteiger (cwinter) 2012-03-22

Notes:
    
--*/

using System;
using System.Linq;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// Solvers.
    /// </summary>
    [ContractVerification(true)]
    public class Solver : Z3Object
    {
        /// <summary>
        /// A string that describes all available solver parameters.
        /// </summary>
        public string Help
        {
            get
            {
                Contract.Ensures(Contract.Result<string>() != null);

                return Native.Z3_solver_get_help(Context.nCtx, NativeObject);
            }
        }

        /// <summary>
        /// Sets the solver parameters.
        /// </summary>
        public Params Parameters
        {
            set
            {
                Contract.Requires(value != null);

                Context.CheckContextMatch(value);
                Native.Z3_solver_set_params(Context.nCtx, NativeObject, value.NativeObject);
            }
        }

	/// <summary>
	/// Sets parameter on the solver
	/// </summary>
	public void Set(string name, bool value) { Parameters = Context.MkParams().Add(name, value); }
	/// <summary>
	/// Sets parameter on the solver
	/// </summary>
	public void Set(string name, uint value) { Parameters = Context.MkParams().Add(name, value); }
	/// <summary>
	/// Sets parameter on the solver
	/// </summary>
	public void Set(string name, double value) { Parameters = Context.MkParams().Add(name, value); }
	/// <summary>
	/// Sets parameter on the solver
	/// </summary>
	public void Set(string name, string value) { Parameters = Context.MkParams().Add(name, value); }
	/// <summary>
	/// Sets parameter on the solver
	/// </summary>
	public void Set(string name, Symbol value) { Parameters = Context.MkParams().Add(name, value); }
	/// <summary>
	/// Sets parameter on the solver
	/// </summary>
	public void Set(Symbol name, bool value) { Parameters = Context.MkParams().Add(name, value); }
	/// <summary>
	/// Sets parameter on the solver
	/// </summary>
	public void Set(Symbol name, uint value) { Parameters = Context.MkParams().Add(name, value); }
	/// <summary>
	/// Sets parameter on the solver
	/// </summary>
	public void Set(Symbol name, double value) { Parameters = Context.MkParams().Add(name, value); }
	/// <summary>
	/// Sets parameter on the solver
	/// </summary>
	public void Set(Symbol name, string value) { Parameters = Context.MkParams().Add(name, value); }
	/// <summary>
	/// Sets parameter on the solver
	/// </summary>
	public void Set(Symbol name, Symbol value) { Parameters = Context.MkParams().Add(name, value); }



        /// <summary>
        /// Retrieves parameter descriptions for solver.
        /// </summary>
        public ParamDescrs ParameterDescriptions
        {
            get { return new ParamDescrs(Context, Native.Z3_solver_get_param_descrs(Context.nCtx, NativeObject)); }
        }


        /// <summary>
        /// The current number of backtracking points (scopes).
        /// </summary>
        /// <seealso cref="Pop"/>
        /// <seealso cref="Push"/>
        public uint NumScopes
        {
            get { return Native.Z3_solver_get_num_scopes(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// Creates a backtracking point.
        /// </summary>
        /// <seealso cref="Pop"/>
        public void Push()
        {
            Native.Z3_solver_push(Context.nCtx, NativeObject);
        }

        /// <summary>
        /// Backtracks <paramref name="n"/> backtracking points.
        /// </summary>
        /// <remarks>Note that an exception is thrown if <paramref name="n"/> is not smaller than <c>NumScopes</c></remarks>
        /// <seealso cref="Push"/>
        public void Pop(uint n = 1)
        {
            Native.Z3_solver_pop(Context.nCtx, NativeObject, n);
        }

        /// <summary>
        /// Resets the Solver.
        /// </summary>
        /// <remarks>This removes all assertions from the solver.</remarks>
        public void Reset()
        {
            Native.Z3_solver_reset(Context.nCtx, NativeObject);
        }

        /// <summary>
        /// Assert a constraint (or multiple) into the solver.
        /// </summary>        
        public void Assert(params BoolExpr[] constraints)
        {
            Contract.Requires(constraints != null);
            Contract.Requires(Contract.ForAll(constraints, c => c != null));

            Context.CheckContextMatch<BoolExpr>(constraints);
            foreach (BoolExpr a in constraints)
            {
                Native.Z3_solver_assert(Context.nCtx, NativeObject, a.NativeObject);
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
        /// Alias for Assert.
        /// </summary>        
        public void Add(IEnumerable<BoolExpr> constraints)
        {
            Assert(constraints.ToArray());
        }

        /// <summary>
        /// Assert multiple constraints into the solver, and track them (in the unsat) core 
        /// using the Boolean constants in ps. 
        /// </summary>
        /// <remarks>
        /// This API is an alternative to <see cref="Check(Expr[])"/> with assumptions for extracting unsat cores.
        /// Both APIs can be used in the same solver. The unsat core will contain a combination
        /// of the Boolean variables provided using <see cref="AssertAndTrack(BoolExpr[],BoolExpr[])"/> 
        /// and the Boolean literals
        /// provided using <see cref="Check(Expr[])"/> with assumptions.
        /// </remarks>        
        public void AssertAndTrack(BoolExpr[] constraints, BoolExpr[] ps)
        {
            Contract.Requires(constraints != null);
            Contract.Requires(Contract.ForAll(constraints, c => c != null));
            Contract.Requires(Contract.ForAll(ps, c => c != null));
            Context.CheckContextMatch<BoolExpr>(constraints);
            Context.CheckContextMatch<BoolExpr>(ps);
            if (constraints.Length != ps.Length)
                throw new Z3Exception("Argument size mismatch");
            
            for (int i = 0 ; i < constraints.Length; i++)
                Native.Z3_solver_assert_and_track(Context.nCtx, NativeObject, constraints[i].NativeObject, ps[i].NativeObject);
        }

        /// <summary>
        /// Assert a constraint into the solver, and track it (in the unsat) core 
        /// using the Boolean constant p. 
        /// </summary>
        /// <remarks>
        /// This API is an alternative to <see cref="Check(Expr[])"/> with assumptions for extracting unsat cores.
        /// Both APIs can be used in the same solver. The unsat core will contain a combination
        /// of the Boolean variables provided using <see cref="AssertAndTrack(BoolExpr[],BoolExpr[])"/> 
        /// and the Boolean literals
        /// provided using <see cref="Check(Expr[])"/> with assumptions.
        /// </remarks>        
        public void AssertAndTrack(BoolExpr constraint, BoolExpr p)
        {
            Contract.Requires(constraint != null);
            Contract.Requires(p != null);
            Context.CheckContextMatch(constraint);
            Context.CheckContextMatch(p);
                        
            Native.Z3_solver_assert_and_track(Context.nCtx, NativeObject, constraint.NativeObject, p.NativeObject);
        }

	/// <summary>
	/// Load solver assertions from a file.
	/// </summary>
	public void FromFile(string file) 
        {
	     Native.Z3_solver_from_file(Context.nCtx, NativeObject, file);	
	}

	/// <summary>
	/// Load solver assertions from a string.
	/// </summary>
	public void FromString(string str) 
        {
	     Native.Z3_solver_from_string(Context.nCtx, NativeObject, str);	
	}

        /// <summary>
        /// The number of assertions in the solver.
        /// </summary>
        public uint NumAssertions
        {
            get
            {
                ASTVector assertions = new ASTVector(Context, Native.Z3_solver_get_assertions(Context.nCtx, NativeObject));
                return assertions.Size;
            }
        }

        /// <summary>
        /// The set of asserted formulas.
        /// </summary>
        public BoolExpr[] Assertions
        {
            get
            {
                Contract.Ensures(Contract.Result<BoolExpr[]>() != null);

                ASTVector assertions = new ASTVector(Context, Native.Z3_solver_get_assertions(Context.nCtx, NativeObject));
                return assertions.ToBoolExprArray();
            }
        }

        /// <summary>
        /// Currently inferred units.
        /// </summary>
        public BoolExpr[] Units
        {
            get
            {
                Contract.Ensures(Contract.Result<BoolExpr[]>() != null);

                ASTVector assertions = new ASTVector(Context, Native.Z3_solver_get_units(Context.nCtx, NativeObject));
                return assertions.ToBoolExprArray();
            }
        }

        /// <summary>
        /// Checks whether the assertions in the solver are consistent or not.
        /// </summary>
        /// <remarks>
        /// <seealso cref="Model"/>
        /// <seealso cref="UnsatCore"/>
        /// <seealso cref="Proof"/>    
        /// </remarks>    
        public Status Check(params Expr[] assumptions)
        {
            Z3_lbool r;
            if (assumptions == null || assumptions.Length == 0)
                r = (Z3_lbool)Native.Z3_solver_check(Context.nCtx, NativeObject);
            else
                r = (Z3_lbool)Native.Z3_solver_check_assumptions(Context.nCtx, NativeObject, (uint)assumptions.Length, AST.ArrayToNative(assumptions));
            return lboolToStatus(r);
        }

        /// <summary>
        /// Checks whether the assertions in the solver are consistent or not.
        /// </summary>
        /// <remarks>
        /// <seealso cref="Model"/>
        /// <seealso cref="UnsatCore"/>
        /// <seealso cref="Proof"/>    
        /// </remarks>    
        public Status Check(IEnumerable<BoolExpr> assumptions)
        {
            Z3_lbool r;
            BoolExpr[] asms = assumptions.ToArray();
            if (asms.Length == 0)
                r = (Z3_lbool)Native.Z3_solver_check(Context.nCtx, NativeObject);
            else
                r = (Z3_lbool)Native.Z3_solver_check_assumptions(Context.nCtx, NativeObject, (uint)asms.Length, AST.ArrayToNative(asms));
            return lboolToStatus(r);
        }

        /// <summary>
        /// Retrieve fixed assignments to the set of variables in the form of consequences.
        /// Each consequence is an implication of the form 
        ///
        ///       relevant-assumptions Implies variable = value
        /// 
        /// where the relevant assumptions is a subset of the assumptions that are passed in
        /// and the equality on the right side of the implication indicates how a variable
        /// is fixed.
        /// </summary>
        /// <remarks>
        /// <seealso cref="Model"/>
        /// <seealso cref="UnsatCore"/>
        /// <seealso cref="Proof"/>    
        /// </remarks>    
        public Status Consequences(IEnumerable<BoolExpr> assumptions, IEnumerable<Expr> variables, out BoolExpr[] consequences) 
        {
            ASTVector result = new ASTVector(Context);
            ASTVector asms = new ASTVector(Context);
            ASTVector vars = new ASTVector(Context);
            foreach (var asm in assumptions) asms.Push(asm);
            foreach (var v in variables) vars.Push(v);
            Z3_lbool r = (Z3_lbool)Native.Z3_solver_get_consequences(Context.nCtx, NativeObject, asms.NativeObject, vars.NativeObject, result.NativeObject);
            consequences = result.ToBoolExprArray();
            return lboolToStatus(r);
        }

        /// <summary>
        /// The model of the last <c>Check(params Expr[] assumptions)</c>.
        /// </summary>
        /// <remarks>
        /// The result is <c>null</c> if <c>Check(params Expr[] assumptions)</c> was not invoked before,
        /// if its results was not <c>SATISFIABLE</c>, or if model production is not enabled.
        /// </remarks>
        public Model Model
        {
            get
            {
                IntPtr x = Native.Z3_solver_get_model(Context.nCtx, NativeObject);
                if (x == IntPtr.Zero)
                    return null;
                else
                    return new Model(Context, x);
            }
        }

        /// <summary>
        /// The proof of the last <c>Check(params Expr[] assumptions)</c>.
        /// </summary>
        /// <remarks>    
        /// The result is <c>null</c> if <c>Check(params Expr[] assumptions)</c> was not invoked before,
        /// if its results was not <c>UNSATISFIABLE</c>, or if proof production is disabled.
        /// </remarks>
        public Expr Proof
        {
            get
            {
                IntPtr x = Native.Z3_solver_get_proof(Context.nCtx, NativeObject);
                if (x == IntPtr.Zero)
                    return null;
                else
                    return Expr.Create(Context, x);
            }
        }

        /// <summary>
        /// The unsat core of the last <c>Check</c>.
        /// </summary>
        /// <remarks>
        /// The unsat core is a subset of <c>Assertions</c>
        /// The result is empty if <c>Check</c> was not invoked before,
        /// if its results was not <c>UNSATISFIABLE</c>, or if core production is disabled.
        /// </remarks>
        public BoolExpr[] UnsatCore
        {
            get
            {
                Contract.Ensures(Contract.Result<Expr[]>() != null);

                ASTVector core = new ASTVector(Context, Native.Z3_solver_get_unsat_core(Context.nCtx, NativeObject));                
                return core.ToBoolExprArray();
            }
        }

        /// <summary>
        /// A brief justification of why the last call to <c>Check</c> returned <c>UNKNOWN</c>.
        /// </summary>
        public string ReasonUnknown
        {
            get
            {
                Contract.Ensures(Contract.Result<string>() != null);

                return Native.Z3_solver_get_reason_unknown(Context.nCtx, NativeObject);
            }
        }

	/// <summary>
	/// Backtrack level that can be adjusted by conquer process
	/// </summary>
        public uint BacktrackLevel { get; set; }

	/// <summary>
	/// Variables available and returned by the cuber.
	/// </summary>
	public BoolExpr[] CubeVariables { get; set; }
        

	/// <summary>
	/// Return a set of cubes.
	/// </summary>
	public IEnumerable<BoolExpr[]> Cube()
	{
             ASTVector cv = new ASTVector(Context);
             if (CubeVariables != null) 
                foreach (var b in CubeVariables) cv.Push(b);

	     while (true) {
                var lvl = BacktrackLevel;
                BacktrackLevel = uint.MaxValue;
                ASTVector r = new ASTVector(Context, Native.Z3_solver_cube(Context.nCtx, NativeObject, cv.NativeObject, lvl));
                var v = r.ToBoolExprArray();
                CubeVariables = cv.ToBoolExprArray();
                if (v.Length == 1 && v[0].IsFalse) {
                   break;
                }
                yield return v; 
                if (v.Length == 0) {
                   break;
                }
	     }
	}

        /// <summary>
        /// Create a clone of the current solver with respect to <c>ctx</c>.
        /// </summary>
        public Solver Translate(Context ctx) 
        {
             Contract.Requires(ctx != null);
             Contract.Ensures(Contract.Result<Solver>() != null);
             return new Solver(ctx, Native.Z3_solver_translate(Context.nCtx, NativeObject, ctx.nCtx));
        }

	/// <summary>
	/// Import model converter from other solver. 
	/// </summary>
	public void ImportModelConverter(Solver src) 
	{
	     Native.Z3_solver_import_model_converter(Context.nCtx, src.NativeObject, NativeObject);
	}

        /// <summary>
        /// Solver statistics.
        /// </summary>
        public Statistics Statistics
        {
            get
            {
                Contract.Ensures(Contract.Result<Statistics>() != null);

                return new Statistics(Context, Native.Z3_solver_get_statistics(Context.nCtx, NativeObject));
            }
        }

        /// <summary>
        /// A string representation of the solver.
        /// </summary>
        public override string ToString()
        {
            return Native.Z3_solver_to_string(Context.nCtx, NativeObject);
        }

        #region Internal
        internal Solver(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
            this.BacktrackLevel = uint.MaxValue;
        }

        internal class DecRefQueue : IDecRefQueue
        {
            public DecRefQueue() : base() { }
            public DecRefQueue(uint move_limit) : base(move_limit) { }
            internal override void IncRef(Context ctx, IntPtr obj)
            {
                Native.Z3_solver_inc_ref(ctx.nCtx, obj);
            }

            internal override void DecRef(Context ctx, IntPtr obj)
            {
                Native.Z3_solver_dec_ref(ctx.nCtx, obj);
            }
        };

        internal override void IncRef(IntPtr o)
        {
            Context.Solver_DRQ.IncAndClear(Context, o);
            base.IncRef(o);
        }

        internal override void DecRef(IntPtr o)
        {
            Context.Solver_DRQ.Add(o);
            base.DecRef(o);
        }

        private Status lboolToStatus(Z3_lbool r) 
        {
            switch (r)
            {
                case Z3_lbool.Z3_L_TRUE: return Status.SATISFIABLE;
                case Z3_lbool.Z3_L_FALSE: return Status.UNSATISFIABLE;
                default: return Status.UNKNOWN;
            }
        }

        #endregion
    }
}
