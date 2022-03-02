using System;
using System.Diagnostics;
using System.Collections.Generic;
using System.Runtime.InteropServices;
using System.Linq;

namespace Microsoft.Z3
{
    using Z3_symbol = System.IntPtr;
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

    public class NativeContext
    {

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

        #region Quantifiers
        /// <summary>
        /// Create a universal Quantifier.
        /// </summary>
        /// <remarks>
        /// Creates a forall formula, where <paramref name="weight"/> is the weight,
        /// <paramref name="patterns"/> is an array of patterns, <paramref name="sorts"/> is an array
        /// with the sorts of the bound variables, <paramref name="names"/> is an array with the
        /// 'names' of the bound variables, and <paramref name="body"/> is the body of the
        /// quantifier. Quantifiers are associated with weights indicating the importance of
        /// using the quantifier during instantiation.
        /// Note that the bound variables are de-Bruijn indices created using <see cref="MkBound"/>.
        /// Z3 applies the convention that the last element in <paramref name="names"/> and
        /// <paramref name="sorts"/> refers to the variable with index 0, the second to last element
        /// of <paramref name="names"/> and <paramref name="sorts"/> refers to the variable
        /// with index 1, etc.
        /// </remarks>
        /// <param name="sorts">the sorts of the bound variables.</param>
        /// <param name="names">names of the bound variables</param>
        /// <param name="body">the body of the quantifier.</param>
        /// <param name="weight">quantifiers are associated with weights indicating the importance of using the quantifier during instantiation. By default, pass the weight 0.</param>
        /// <param name="patterns">array containing the patterns created using <c>MkPattern</c>.</param>
        /// <param name="noPatterns">array containing the anti-patterns created using <c>MkPattern</c>.</param>
        /// <param name="quantifierID">optional symbol to track quantifier.</param>
        /// <param name="skolemID">optional symbol to track skolem constants.</param>
        public Z3_ast MkForall(Z3_sort[] sorts, Symbol[] names, Z3_ast body, uint weight = 1, Z3_ast[] patterns = null, Z3_ast[] noPatterns = null, Symbol quantifierID = null, Symbol skolemID = null)
        {
            return MkQuantifier(true, sorts, names, body, weight, patterns, noPatterns, quantifierID, skolemID);
        }

        /// <summary>
        /// Create a quantified expression either forall or exists
        /// </summary>
        /// <param name="is_forall"></param>
        /// <param name="sorts"></param>
        /// <param name="names"></param>
        /// <param name="body"></param>
        /// <param name="weight"></param>
        /// <param name="patterns"></param>
        /// <param name="noPatterns"></param>
        /// <param name="quantifierID"></param>
        /// <param name="skolemID"></param>
        /// <returns></returns>
        private Z3_ast MkQuantifier(bool is_forall, Z3_sort[] sorts, Symbol[] names, Z3_ast body, uint weight, Z3_ast[] patterns, Z3_ast[] noPatterns, Symbol quantifierID, Symbol skolemID)
        {
            Debug.Assert(sorts != null);
            Debug.Assert(names != null);
            Debug.Assert(body != null);
            Debug.Assert(sorts.Length == names.Length);
            Debug.Assert(sorts.All(s => s != IntPtr.Zero));
            Debug.Assert(names.All(n => n != null));
            Debug.Assert(patterns == null || patterns.All(p => p != IntPtr.Zero));
            Debug.Assert(noPatterns == null || noPatterns.All(np => np != IntPtr.Zero));
            uint numPatterns = patterns == null ? 0 : (uint)patterns.Length;
            uint numNoPatterns = noPatterns == null ? 0 : (uint)noPatterns.Length;
            if (noPatterns == null && quantifierID == null && skolemID == null)
            {
                return Native.Z3_mk_quantifier(nCtx, (byte)(is_forall ? 1 : 0), weight,
                                numPatterns, patterns,
                                (uint)sorts.Length, sorts,
                                Symbol.ArrayToNative(names),
                                body);
            }
            else
            {
                return Native.Z3_mk_quantifier_ex(nCtx, (byte)(is_forall ? 1 : 0), weight,
                                  AST.GetNativeObject(quantifierID), AST.GetNativeObject(skolemID),
                                  numPatterns, patterns,
                                  numNoPatterns, noPatterns,
                                  (uint)sorts.Length, sorts,
                                  Symbol.ArrayToNative(names),
                                  body);
            }
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


        /// <summary>
        /// Utility to convert a vector object of ast to a .Net array
        /// </summary>
        /// <param name="vec"></param>
        /// <returns></returns>
        public Z3_ast[] ToArray(Z3_ast_vector vec)
        {
            Native.Z3_ast_vector_inc_ref(nCtx, vec);
            var sz = Native.Z3_ast_vector_size(nCtx, vec);
            var result = new Z3_ast[sz];
            for (uint i = 0; i < sz; ++i)
                result[i] = Native.Z3_ast_vector_get(nCtx, vec, i);
            Native.Z3_ast_vector_dec_ref(nCtx, vec);
            return result;

        }

        public Statistics.Entry[] GetStatistics(Z3_stats stats)
        {
            Native.Z3_stats_inc_ref(nCtx, stats);
            var result = Statistics.NativeEntries(nCtx, stats); 
            Native.Z3_stats_dec_ref(nCtx, stats);
            return result;
        }

    }
}