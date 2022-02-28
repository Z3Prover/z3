using System;
using System.Diagnostics;
using System.Collections.Generic;
using System.Runtime.InteropServices;
using System.Linq;

namespace Microsoft.Z3
{
    using Z3_config = System.IntPtr;
    using Z3_context = System.IntPtr;
    using Z3_ast = System.IntPtr;
    using Z3_app = System.IntPtr;
    using Z3_sort = System.IntPtr;
    using Z3_func_decl = System.IntPtr;
    using Z3_pattern = System.IntPtr;
    using Z3_model = System.IntPtr;
    using Z3_literals = System.IntPtr;
    using Z3_constructor = System.IntPtr;
    using Z3_constructor_list = System.IntPtr;
    using Z3_solver = System.IntPtr;
    using Z3_solver_callback = System.IntPtr;
    using Z3_goal = System.IntPtr;
    using Z3_tactic = System.IntPtr;
    using Z3_params = System.IntPtr;
    using Z3_probe = System.IntPtr;
    using Z3_stats = System.IntPtr;
    using Z3_ast_vector = System.IntPtr;
    using Z3_ast_map = System.IntPtr;
    using Z3_apply_result = System.IntPtr;
    using Z3_func_interp = System.IntPtr;
    using Z3_func_entry = System.IntPtr;
    using Z3_fixedpoint = System.IntPtr;
    using Z3_optimize = System.IntPtr;
    using Z3_param_descrs = System.IntPtr;
    using Z3_rcf_num = System.IntPtr;

    /// <summary>
    /// The main interaction with Z3 happens via the Context.
    /// NativeContext allows for efficient wrapper-reduced interaction with Z3
    /// expressions.
    /// </summary>

    public class NativeContext: IDisposable
    {
        /// <summary>
        /// Constructor.
        /// </summary>
        /// <remarks>
        /// The following parameters can be set:
        ///     - proof  (Boolean)           Enable proof generation
        ///     - debug_ref_count (Boolean)  Enable debug support for Z3_ast reference counting
        ///     - trace  (Boolean)           Tracing support for VCC
        ///     - trace_file_name (String)   Trace out file for VCC traces
        ///     - timeout (unsigned)         default timeout (in milliseconds) used for solvers
        ///     - well_sorted_check          type checker
        ///     - auto_config                use heuristics to automatically select solver and configure it
        ///     - model                      model generation for solvers, this parameter can be overwritten when creating a solver
        ///     - model_validate             validate models produced by solvers
        ///     - unsat_core                 unsat-core generation for solvers, this parameter can be overwritten when creating a solver
        /// Note that in previous versions of Z3, this constructor was also used to set global and module parameters.
        /// For this purpose we should now use <see cref="Global.SetParameter"/>
        /// </remarks>
        public NativeContext(Dictionary<string, string> settings)
            : base()
        {
            Debug.Assert(settings != null);

            lock (creation_lock)
            {
                IntPtr cfg = Native.Z3_mk_config();
                foreach (KeyValuePair<string, string> kv in settings)
                    Native.Z3_set_param_value(cfg, kv.Key, kv.Value);
                m_ctx = Native.Z3_mk_context_rc(cfg);
                Native.Z3_del_config(cfg);
                InitContext();
            }
        }

        #region Arithmetic
        /// <summary>
        /// Create an expression representing <c>t[0] + t[1] + ...</c>.
        /// </summary>

        public Z3_ast MkAdd(params Z3_ast[] t)
        {
            Debug.Assert(t != null);
            Debug.Assert(t.All(a => a != IntPtr.Zero));
            return Native.Z3_mk_add(nCtx, (uint)t.Length, t);
        }

        #endregion

        #region Sort

        public Z3_sort MkIntSort() => Native.Z3_mk_int_sort(nCtx);
        public Z3_sort MkBoolSort() => Native.Z3_mk_bool_sort(nCtx);
        public Z3_sort MkBvSort(uint size) => Native.Z3_mk_bv_sort(nCtx, size);

        #endregion

        #region Propositional
        /// <summary>
        /// The true Term.
        /// </summary>
        public Z3_ast MkTrue() => Native.Z3_mk_true(nCtx);

        /// <summary>
        /// The false Term.
        /// </summary>
        public Z3_ast MkFalse() => Native.Z3_mk_false(nCtx);

        /// <summary>
        /// Creates a Boolean value.
        /// </summary>
        public Z3_ast MkBool(bool value)
        {

            return value ? MkTrue() : MkFalse();
        }

        #endregion

        #region Terms
        /// <summary>
        /// Create a new function application.
        /// </summary>
        public Z3_ast MkApp(Z3_func_decl f, params Z3_ast[] args)
        {
            Debug.Assert(f != null);
            Debug.Assert(args == null || args.All(a => a != null));

            return Native.Z3_mk_app(nCtx, f, (uint)args.Length, args);
        }
        
        #endregion

        #region Bound Variables
        /// <summary>
        /// Creates a new bound variable.
        /// </summary>
        /// <param name="index">The de-Bruijn index of the variable</param>
        /// <param name="sort">The sort of the variable</param>
        public Z3_ast MkBound(uint index, Z3_sort sort)
        {
            Debug.Assert(sort != IntPtr.Zero);

            return Native.Z3_mk_bound(nCtx, index, sort);
        }
        #endregion

        #region Options
        /// <summary>
        /// Selects the format used for pretty-printing expressions.
        /// </summary>
        /// <remarks>
        /// The default mode for pretty printing expressions is to produce
        /// SMT-LIB style output where common subexpressions are printed
        /// at each occurrence. The mode is called Z3_PRINT_SMTLIB_FULL.
        /// To print shared common subexpressions only once,
        /// use the Z3_PRINT_LOW_LEVEL mode.
        /// To print in way that conforms to SMT-LIB standards and uses let
        /// expressions to share common sub-expressions use Z3_PRINT_SMTLIB_COMPLIANT.
        /// </remarks>
        /// <seealso cref="AST.ToString()"/>
        /// <seealso cref="Pattern.ToString()"/>
        /// <seealso cref="FuncDecl.ToString()"/>
        /// <seealso cref="Sort.ToString()"/>
        public Z3_ast_print_mode PrintMode
        {
            set { Native.Z3_set_ast_print_mode(nCtx, (uint)value); }
        }


        #endregion

        #region Internal
        internal static Object creation_lock = new Object();
        internal IntPtr m_ctx = IntPtr.Zero;
        internal Native.Z3_error_handler m_n_err_handler = null;
        internal IntPtr nCtx { get { return m_ctx; } }

        internal void NativeErrorHandler(IntPtr ctx, Z3_error_code errorCode)
        {
            // Do-nothing error handler. The wrappers in Z3.Native will throw exceptions upon errors.
        }

        internal void InitContext()
        {
            PrintMode = Z3_ast_print_mode.Z3_PRINT_SMTLIB2_COMPLIANT;
            m_n_err_handler = new Native.Z3_error_handler(NativeErrorHandler); // keep reference so it doesn't get collected.
            Native.Z3_set_error_handler(m_ctx, m_n_err_handler);
            GC.SuppressFinalize(this);
        }

        #endregion

        #region Dispose

        /// <summary>
        /// Disposes of the context.
        /// </summary>
        public void Dispose()
        {
            if (m_ctx != IntPtr.Zero)
            {
                m_n_err_handler = null;
                IntPtr ctx = m_ctx;
                m_ctx = IntPtr.Zero;
                Native.Z3_del_context(ctx);
            }
            else
                GC.ReRegisterForFinalize(this);
        }
        #endregion

    }
}