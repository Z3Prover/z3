
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics.Contracts;
using System.Runtime.InteropServices;

namespace Microsoft.Z3
{
    /// <summary>
    /// The InterpolationContext is suitable for generation of interpolants.
    /// </summary>
    /// <remarks>For more information on interpolation please refer
    /// too the C/C++ API, which is well documented.</remarks>
    [ContractVerification(true)]
    public class InterpolationContext : Context
    {

        /// <summary>
        /// Constructor.
        /// </summary>
        public InterpolationContext() : base() { }

        /// <summary>
        /// Constructor.
        /// </summary>
        /// <remarks><seealso cref="Context"/></remarks>
        public InterpolationContext(Dictionary<string, string> settings) : base(settings) { }

        #region Terms
        /// <summary>
        /// Create an expression that marks a formula position for interpolation.
        /// </summary>
        public BoolExpr MkInterpolant(BoolExpr a)
        {
            Contract.Requires(a != null);
            Contract.Ensures(Contract.Result<BoolExpr>() != null);

            CheckContextMatch(a);
            return new BoolExpr(this, Native.Z3_mk_interpolant(nCtx, a.NativeObject));
        }
        #endregion

        /// <summary> 
        /// Computes an interpolant.
        /// </summary>    
        /// <remarks>For more information on interpolation please refer
        /// too the function Z3_get_interpolant in the C/C++ API, which is 
        /// well documented.</remarks>
        public BoolExpr[] GetInterpolant(Expr pf, Expr pat, Params p)
        {
            Contract.Requires(pf != null);
            Contract.Requires(pat != null);
            Contract.Requires(p != null);
            Contract.Ensures(Contract.Result<Expr>() != null);

            CheckContextMatch(pf);
            CheckContextMatch(pat);
            CheckContextMatch(p);

            ASTVector seq = new ASTVector(this, Native.Z3_get_interpolant(nCtx, pf.NativeObject, pat.NativeObject, p.NativeObject));
            return seq.ToBoolExprArray();
        }

        /// <summary> 
        /// Computes an interpolant.
        /// </summary>    
        /// <remarks>For more information on interpolation please refer
        /// too the function Z3_compute_interpolant in the C/C++ API, which is 
        /// well documented.</remarks>
        public Z3_lbool ComputeInterpolant(Expr pat, Params p, out BoolExpr[] interp, out Model model)
        {
            Contract.Requires(pat != null);
            Contract.Requires(p != null);
            Contract.Ensures(Contract.ValueAtReturn(out interp) != null);
            Contract.Ensures(Contract.ValueAtReturn(out model) != null);

            CheckContextMatch(pat);
            CheckContextMatch(p);

            IntPtr i = IntPtr.Zero, m = IntPtr.Zero;
            int r = Native.Z3_compute_interpolant(nCtx, pat.NativeObject, p.NativeObject, ref i, ref m);
            interp = new ASTVector(this, i).ToBoolExprArray();
            model = new Model(this, m);
            return (Z3_lbool)r;
        }

        /// <summary> 
        /// Return a string summarizing cumulative time used for interpolation.
        /// </summary>    
        /// <remarks>For more information on interpolation please refer
        /// too the function Z3_interpolation_profile in the C/C++ API, which is 
        /// well documented.</remarks>
        public string InterpolationProfile()
        {
            return Native.Z3_interpolation_profile(nCtx);
        }

        /// <summary> 
        /// Checks the correctness of an interpolant.
        /// </summary>    
        /// <remarks>For more information on interpolation please refer
        /// too the function Z3_check_interpolant in the C/C++ API, which is 
        /// well documented.</remarks>
        public int CheckInterpolant(Expr[] cnsts, uint[] parents, BoolExpr[] interps, out string error, Expr[] theory)
        {
            Contract.Requires(cnsts.Length == parents.Length);
            Contract.Requires(cnsts.Length == interps.Length + 1);
            IntPtr n_err_str;
            int r = Native.Z3_check_interpolant(nCtx,
                                                (uint)cnsts.Length,
                                                Expr.ArrayToNative(cnsts),
                                                parents,
                                                Expr.ArrayToNative(interps),
                                                out n_err_str,
                                                (uint)theory.Length,
                                                Expr.ArrayToNative(theory));
            error = Marshal.PtrToStringAnsi(n_err_str);
            return r;
        }

        /// <summary> 
        /// Reads an interpolation problem from a file.
        /// </summary>    
        /// <remarks>For more information on interpolation please refer
        /// too the function Z3_read_interpolation_problem in the C/C++ API, which is 
        /// well documented.</remarks>
        public int ReadInterpolationProblem(string filename, out Expr[] cnsts, out uint[] parents, out string error, out Expr[] theory)
        {
            uint num = 0, num_theory = 0;
            IntPtr[] n_cnsts;
            IntPtr[] n_theory;
            IntPtr n_err_str;
            int r = Native.Z3_read_interpolation_problem(nCtx, ref num, out n_cnsts, out parents, filename, out n_err_str, ref num_theory, out n_theory);
            error = Marshal.PtrToStringAnsi(n_err_str);
            cnsts = new Expr[num];
            parents = new uint[num];
            theory = new Expr[num_theory];
            for (int i = 0; i < num; i++)
                cnsts[i] = Expr.Create(this, n_cnsts[i]);
            for (int i = 0; i < num_theory; i++)
                theory[i] = Expr.Create(this, n_theory[i]);
            return r;
        }

        /// <summary> 
        /// Writes an interpolation problem to a file.
        /// </summary>    
        /// <remarks>For more information on interpolation please refer
        /// too the function Z3_write_interpolation_problem in the C/C++ API, which is 
        /// well documented.</remarks>
        public void WriteInterpolationProblem(string filename, Expr[] cnsts, uint[] parents, Expr[] theory)
        {
            Contract.Requires(cnsts.Length == parents.Length);
            Native.Z3_write_interpolation_problem(nCtx, (uint)cnsts.Length, Expr.ArrayToNative(cnsts), parents, filename, (uint)theory.Length, Expr.ArrayToNative(theory));
        }
    }
}
