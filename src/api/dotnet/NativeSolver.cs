/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    NativeSolver.cs

Abstract:

    Z3 Managed API: Native Solver

Author:

    Christoph Wintersteiger (cwinter) 2012-03-22
    Nikolaj Bjorner (nbjorner) 2022-03-01

Notes:
    
--*/

using System;
using System.Diagnostics;
using System.Linq;
using System.Collections.Generic;

namespace Microsoft.Z3
{

    using Z3_context = System.IntPtr;
    using Z3_ast = System.IntPtr;
    using Z3_app = System.IntPtr;
    using Z3_sort = System.IntPtr;
    using Z3_func_decl = System.IntPtr;
    using Z3_model = System.IntPtr;
    using Z3_ast_vector = System.IntPtr;
    using Z3_solver = System.IntPtr;

    /// <summary>
    /// Solvers.
    /// </summary>
    public class NativeSolver : IDisposable
    {
        /// <summary>
        /// A string that describes all available solver parameters.
        /// </summary>
        public string Help
        {
            get
            {

                return Native.Z3_solver_get_help(Context.nCtx, NativeObject);
            }
        }

#if false
        /// <summary>
        /// Sets the solver parameters.
        /// </summary>
        public Params Parameters
        {
            set
            {
                Debug.Assert(value != null);

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

#endif

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
        public void Assert(params Z3_ast[] constraints)
        {
            Debug.Assert(constraints != null);
            Debug.Assert(constraints.All(c => c != IntPtr.Zero));

            foreach (Z3_ast a in constraints)
            {
                Native.Z3_solver_assert(Context.nCtx, NativeObject, a);
            }
        }

        /// <summary>
        /// Alias for Assert.
        /// </summary>        
        public void Add(params Z3_ast[] constraints)
        {
            Assert(constraints);
        }

        /// <summary>
        /// Alias for Assert.
        /// </summary>        
        public void Add(IEnumerable<Z3_ast> constraints)
        {
            Assert(constraints.ToArray());
        }

        /// <summary>
        /// Assert multiple constraints into the solver, and track them (in the unsat) core 
        /// using the Boolean constants in ps. 
        /// </summary>
        /// <remarks>
        /// This API is an alternative to <see cref="Check(Z3_ast[])"/> with assumptions for extracting unsat cores.
        /// Both APIs can be used in the same solver. The unsat core will contain a combination
        /// of the Boolean variables provided using <see cref="AssertAndTrack(Z3_ast[],Z3_ast[])"/> 
        /// and the Boolean literals
        /// provided using <see cref="Check(Z3_ast[])"/> with assumptions.
        /// </remarks>        
        public void AssertAndTrack(Z3_ast[] constraints, Z3_ast[] ps)
        {
            Debug.Assert(constraints != null);
            Debug.Assert(constraints.All(c => c != IntPtr.Zero));
            Debug.Assert(ps.All(c => c != IntPtr.Zero));
            if (constraints.Length != ps.Length)
                throw new Z3Exception("Argument size mismatch");

            for (int i = 0; i < constraints.Length; i++)
                Native.Z3_solver_assert_and_track(Context.nCtx, NativeObject, constraints[i], ps[i]);
        }

        /// <summary>
        /// Assert a constraint into the solver, and track it (in the unsat) core 
        /// using the Boolean constant p. 
        /// </summary>
        /// <remarks>
        /// This API is an alternative to <see cref="Check(Z3_ast[])"/> with assumptions for extracting unsat cores.
        /// Both APIs can be used in the same solver. The unsat core will contain a combination
        /// of the Boolean variables provided using <see cref="AssertAndTrack(Z3_ast[],Z3_ast[])"/> 
        /// and the Boolean literals
        /// provided using <see cref="Check(Z3_ast[])"/> with assumptions.
        /// </remarks>        
        public void AssertAndTrack(Z3_ast constraint, Z3_ast p)
        {
            Debug.Assert(constraint != null);
            Debug.Assert(p != null);

            Native.Z3_solver_assert_and_track(Context.nCtx, NativeObject, constraint, p);
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
                return (uint)Context.ToArray(Native.Z3_solver_get_assertions(Context.nCtx, NativeObject)).Length;
            }
        }

        /// <summary>
        /// The set of asserted formulas.
        /// </summary>
        public Z3_ast[] Assertions
        {
            get
            {
                return Context.ToArray(Native.Z3_solver_get_assertions(Context.nCtx, NativeObject));
            }
        }

        /// <summary>
        /// Currently inferred units.
        /// </summary>
        public Z3_ast[] Units
        {
            get
            {
                return Context.ToArray(Native.Z3_solver_get_units(Context.nCtx, NativeObject));
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
        public Status Check(params Z3_ast[] assumptions)
        {
            Z3_lbool r;
            if (assumptions == null || assumptions.Length == 0)
                r = (Z3_lbool)Native.Z3_solver_check(Context.nCtx, NativeObject);
            else
                r = (Z3_lbool)Native.Z3_solver_check_assumptions(Context.nCtx, NativeObject, (uint)assumptions.Length, assumptions);
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
        public Status Check(IEnumerable<Z3_ast> assumptions)
        {
            Z3_lbool r;
            Z3_ast[] asms = assumptions.ToArray();
            if (asms.Length == 0)
                r = (Z3_lbool)Native.Z3_solver_check(Context.nCtx, NativeObject);
            else
                r = (Z3_lbool)Native.Z3_solver_check_assumptions(Context.nCtx, NativeObject, (uint)asms.Length, asms);
            return lboolToStatus(r);
        }

        /// <summary>
        /// The model of the last <c>Check(params Expr[] assumptions)</c>.
        /// </summary>
        /// <remarks>
        /// The result is <c>null</c> if <c>Check(params Expr[] assumptions)</c> was not invoked before,
        /// if its results was not <c>SATISFIABLE</c>, or if model production is not enabled.
        /// </remarks>
        public NativeModel Model
        {
            get
            {
                IntPtr x = Native.Z3_solver_get_model(Context.nCtx, NativeObject);
                if (x == IntPtr.Zero)
                    return null;
                else
                    return new NativeModel(Context, x);
            }
        }

        /// <summary>
        /// The proof of the last <c>Check(params Expr[] assumptions)</c>.
        /// </summary>
        /// <remarks>    
        /// The result is <c>null</c> if <c>Check(params Expr[] assumptions)</c> was not invoked before,
        /// if its results was not <c>UNSATISFIABLE</c>, or if proof production is disabled.
        /// </remarks>
        public Z3_ast Proof
        {
            get
            {
                return Native.Z3_solver_get_proof(Context.nCtx, NativeObject);
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
        public Z3_ast[] UnsatCore
        {
            get
            {
                return Context.ToArray(Native.Z3_solver_get_unsat_core(Context.nCtx, NativeObject));
            }
        }

        /// <summary>
        /// A brief justification of why the last call to <c>Check</c> returned <c>UNKNOWN</c>.
        /// </summary>
        public string ReasonUnknown
        {
            get
            {
                return Native.Z3_solver_get_reason_unknown(Context.nCtx, NativeObject);
            }
        }

        /// <summary>
        /// Create a clone of the current solver with respect to <c>ctx</c>.
        /// </summary>
        public NativeSolver Translate(NativeContext ctx)
        {
            Debug.Assert(ctx != null);
            return new NativeSolver(ctx, Native.Z3_solver_translate(Context.nCtx, NativeObject, ctx.nCtx));
        }

        /// <summary>
        /// Import model converter from other solver. 
        /// </summary>
        public void ImportModelConverter(NativeSolver src)
        {
            Native.Z3_solver_import_model_converter(Context.nCtx, src.NativeObject, NativeObject);
        }


        /// <summary>
        /// Solver statistics.
        /// </summary>
        public Statistics.Entry[] Statistics
        {
            get
            {
                var stats = Native.Z3_solver_get_statistics(Context.nCtx, NativeObject);
                return Context.GetStatistics(stats);
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
        NativeContext Context;
        IntPtr NativeObject;
        internal NativeSolver(NativeContext ctx, Z3_solver obj)
        {
            Context = ctx;
            NativeObject = obj;

            Debug.Assert(ctx != null);
            Native.Z3_solver_inc_ref(ctx.nCtx, obj);
        }

        /// <summary>
        /// Finalizer.
        /// </summary>
        ~NativeSolver()
        {
            Dispose();
        }

        /// <summary>
        /// Disposes of the underlying native Z3 object.
        /// </summary>
        public void Dispose()
        {
            if (NativeObject != IntPtr.Zero)
            {
                Native.Z3_solver_dec_ref(Context.nCtx, NativeObject);
                NativeObject = IntPtr.Zero;
            }
            GC.SuppressFinalize(this);
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
