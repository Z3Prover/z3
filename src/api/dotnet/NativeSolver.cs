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
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Z3
{

    using Z3_ast = System.IntPtr;
    using Z3_context = System.IntPtr;
    using Z3_func_decl = System.IntPtr;
    using Z3_params = System.IntPtr;
    using Z3_solver = System.IntPtr;
    using Z3_sort = System.IntPtr;
    using Z3_symbol = System.IntPtr;

    /// <summary>
    /// Solvers.
    /// </summary>
    public class NativeSolver : IDisposable
    {
        /// <summary>
        /// A string that describes all available solver parameters.
        /// </summary>
        public string Help => Native.Z3_solver_get_help(nCtx, z3solver);

        private void SetParam(Action<Z3_params> setter)
        {
            Z3_params p = Native.Z3_mk_params(nCtx);
            Native.Z3_params_inc_ref(nCtx, p);
            setter(p);
            Native.Z3_solver_set_params(nCtx, z3solver, p);
            Native.Z3_params_dec_ref(nCtx, p);
        }

        /// <summary>
        /// Sets parameter on the solver
        /// </summary>
        public void Set(string name, bool value)
        {
            SetParam((Z3_params p) => Native.Z3_params_set_bool(nCtx, p, Native.Z3_mk_string_symbol(nCtx, name), (byte)(value ? 1 : 0)));
        }

        /// <summary>
        /// Sets parameter on the solver
        /// </summary>
        public void Set(string name, uint value)
        {
            SetParam((Z3_params p) => Native.Z3_params_set_uint(nCtx, p, Native.Z3_mk_string_symbol(nCtx, name), value));
        }

        /// <summary>
        /// Sets parameter on the solver
        /// </summary>
        public void Set(string name, double value)
        {
            SetParam((Z3_params p) => Native.Z3_params_set_double(nCtx, p, Native.Z3_mk_string_symbol(nCtx, name), value));
        }

        /// <summary>
        /// Sets parameter on the solver
        /// </summary>
        public void Set(string name, string value)
        {
            var value_sym = Native.Z3_mk_string_symbol(nCtx, value);
            SetParam((Z3_params p) => Native.Z3_params_set_symbol(nCtx, p, Native.Z3_mk_string_symbol(nCtx, name), value_sym));
        }

#if false
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
            get { return new ParamDescrs(Context, Native.Z3_solver_get_param_descrs(nCtx, NativeObject)); }
        }
#endif

        /// <summary>
        /// The current number of backtracking points (scopes).
        /// </summary>
        /// <seealso cref="Pop"/>
        /// <seealso cref="Push"/>
        public uint NumScopes => Native.Z3_solver_get_num_scopes(nCtx, z3solver);

        /// <summary>
        /// Creates a backtracking point.
        /// </summary>
        /// <seealso cref="Pop"/>
        public void Push() => Native.Z3_solver_push(nCtx, z3solver);

        /// <summary>
        /// Backtracks <paramref name="n"/> backtracking points.
        /// </summary>
        /// <remarks>Note that an exception is thrown if <paramref name="n"/> is not smaller than <c>NumScopes</c></remarks>
        /// <seealso cref="Push"/>
        public void Pop(uint n = 1) => Native.Z3_solver_pop(nCtx, z3solver, n);

        /// <summary>
        /// Resets the Solver.
        /// </summary>
        /// <remarks>This removes all assertions from the solver.</remarks>
        public void Reset() => Native.Z3_solver_reset(nCtx, z3solver);

        /// <summary>
        /// Assert a constraint (or multiple) into the solver.
        /// </summary>        
        public void Assert(params Z3_ast[] constraints)
        {
            Debug.Assert(constraints != null);
            Debug.Assert(constraints.All(c => c != IntPtr.Zero));

            foreach (Z3_ast a in constraints)
            {
                Native.Z3_solver_assert(nCtx, z3solver, a);
            }
        }

        /// <summary>
        /// Alias for Assert.
        /// </summary>        
        public void Add(params Z3_ast[] constraints) => Assert(constraints);

        /// <summary>
        /// Alias for Assert.
        /// </summary>        
        public void Add(IEnumerable<Z3_ast> constraints) => Assert(constraints.ToArray());

        /// <summary>
        /// Add constraints to ensure the function f can only be injective.
        /// Example:
        /// for function f : D1 x D2 -> R
        /// assert axioms
        ///   forall (x1 : D1, x2 : D2) x1 = inv1(f(x1,x2))
        ///   forall (x1 : D1, x2 : D2) x2 = inv2(f(x1,x2))
        /// </summary>
        /// <param name="f"></param>
        public void AssertInjective(Z3_func_decl f)
        {
            uint arity = Native.Z3_get_arity(nCtx, f);
            Z3_sort range = Native.Z3_get_range(nCtx, f);
            Z3_ast[] vars = new Z3_ast[arity];
            Z3_sort[] sorts = new Z3_sort[arity];
            Z3_symbol[] names = new Z3_symbol[arity];
            for (uint i = 0; i < arity; ++i)
            {
                Z3_sort domain = Native.Z3_get_domain(nCtx, f, i);
                vars[i] = ntvContext.MkBound(arity - i - 1, domain);
                sorts[i] = domain;
                names[i] = Native.Z3_mk_int_symbol(nCtx, (int)i);
            }
            Z3_ast app_f = IntPtr.Zero; // Context.MkApp(f, vars);
            for (uint i = 0; i < arity; ++i)
            {
                Z3_sort domain = Native.Z3_get_domain(nCtx, f, i);
                Z3_func_decl proj = ntvContext.MkFreshFuncDecl("inv", new Z3_sort[] { range }, domain);
                Z3_ast body = ntvContext.MkEq(vars[i], ntvContext.MkApp(proj, app_f));
                Z3_ast q = ntvContext.MkForall(names, sorts, body);
                Assert(q);
            }
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
                Native.Z3_solver_assert_and_track(nCtx, z3solver, constraints[i], ps[i]);
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

            Native.Z3_solver_assert_and_track(nCtx, z3solver, constraint, p);
        }

        /// <summary>
        /// Load solver assertions from a file.
        /// </summary>
        public void FromFile(string file)
            => Native.Z3_solver_from_file(nCtx, z3solver, file);

        /// <summary>
        /// Load solver assertions from a string.
        /// </summary>
        public void FromString(string str)
            => Native.Z3_solver_from_string(nCtx, z3solver, str);

        /// <summary>
        /// The number of assertions in the solver.
        /// </summary>
        public uint NumAssertions
            => (uint)ntvContext.ToArray(Native.Z3_solver_get_assertions(nCtx, z3solver)).Length;

        /// <summary>
        /// The set of asserted formulas.
        /// </summary>
        public Z3_ast[] Assertions
            => ntvContext.ToArray(Native.Z3_solver_get_assertions(nCtx, z3solver));

        /// <summary>
        /// Currently inferred units.
        /// </summary>
        public Z3_ast[] Units
            => ntvContext.ToArray(Native.Z3_solver_get_units(nCtx, z3solver));

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
                r = (Z3_lbool)Native.Z3_solver_check(nCtx, z3solver);
            else
                r = (Z3_lbool)Native.Z3_solver_check_assumptions(nCtx, z3solver, (uint)assumptions.Length, assumptions);
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
                r = (Z3_lbool)Native.Z3_solver_check(nCtx, z3solver);
            else
                r = (Z3_lbool)Native.Z3_solver_check_assumptions(nCtx, z3solver, (uint)asms.Length, asms);
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
                IntPtr x = Native.Z3_solver_get_model(nCtx, z3solver);
                return x == IntPtr.Zero
                    ? null
                    : new NativeModel(ntvContext, x);
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
            => Native.Z3_solver_get_proof(nCtx, z3solver);

        /// <summary>
        /// The unsat core of the last <c>Check</c>.
        /// </summary>
        /// <remarks>
        /// The unsat core is a subset of <c>Assertions</c>
        /// The result is empty if <c>Check</c> was not invoked before,
        /// if its results was not <c>UNSATISFIABLE</c>, or if core production is disabled.
        /// </remarks>
        public Z3_ast[] UnsatCore
            => ntvContext.ToArray(Native.Z3_solver_get_unsat_core(nCtx, z3solver));

        /// <summary>
        /// A brief justification of why the last call to <c>Check</c> returned <c>UNKNOWN</c>.
        /// </summary>
        public string ReasonUnknown
            => Native.Z3_solver_get_reason_unknown(nCtx, z3solver);

        /// <summary>
        /// Create a clone of the current solver with respect to <c>ctx</c>.
        /// </summary>
        public NativeSolver Translate(NativeContext ctx)
        {
            Debug.Assert(ctx != null);
            return new NativeSolver(ctx, Native.Z3_solver_translate(nCtx, z3solver, ctx.nCtx));
        }

        /// <summary>
        /// Import model converter from other solver. 
        /// </summary>
        public void ImportModelConverter(NativeSolver src)
        {
            Debug.Assert(src != null);

            Native.Z3_solver_import_model_converter(nCtx, src.z3solver, z3solver);
        }

        /// <summary>
        /// Solver statistics.
        /// </summary>
        public Statistics.Entry[] Statistics
        {
            get
            {
                var stats = Native.Z3_solver_get_statistics(nCtx, z3solver);
                return ntvContext.GetStatistics(stats);
            }
        }

        /// <summary>
        /// A string representation of the solver.
        /// </summary>
        public override string ToString()
        {
            return Native.Z3_solver_to_string(nCtx, z3solver);
        }

        #region Internal
        readonly NativeContext ntvContext;
        Z3_solver z3solver;
        Z3_context nCtx => ntvContext.nCtx;

        internal NativeSolver(NativeContext nativeCtx, Z3_solver z3solver)
        {
            Debug.Assert(nativeCtx != null);
            Debug.Assert(z3solver != IntPtr.Zero);

            this.ntvContext = nativeCtx;
            this.z3solver = z3solver;

            Native.Z3_solver_inc_ref(nCtx, z3solver);
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
            if (z3solver != IntPtr.Zero)
            {
                Native.Z3_solver_dec_ref(nCtx, z3solver);
                z3solver = IntPtr.Zero;
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
