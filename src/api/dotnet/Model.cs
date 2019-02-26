/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    Model.cs

Abstract:

    Z3 Managed API: Models

Author:

    Christoph Wintersteiger (cwinter) 2012-03-21

Notes:
    
--*/

using System;
using System.Diagnostics;
using System.Collections.Generic;

namespace Microsoft.Z3
{
    /// <summary>
    /// A Model contains interpretations (assignments) of constants and functions. 
    /// </summary>
    public class Model : Z3Object
    {
        /// <summary>
        /// Retrieves the interpretation (the assignment) of <paramref name="a"/> in the model. 
        /// </summary>
        /// <param name="a">A Constant</param>
        /// <returns>An expression if the constant has an interpretation in the model, null otherwise.</returns>
        public Expr ConstInterp(Expr a)
        {
            Debug.Assert(a != null);

            Context.CheckContextMatch(a);
            return ConstInterp(a.FuncDecl);
        }

        /// <summary>
        /// Retrieves the interpretation (the assignment) of <paramref name="f"/> in the model. 
        /// </summary>
        /// <param name="f">A function declaration of zero arity</param>
        /// <returns>An expression if the function has an interpretation in the model, null otherwise.</returns>    
        public Expr ConstInterp(FuncDecl f)
        {
            Debug.Assert(f != null);

            Context.CheckContextMatch(f);
            if (f.Arity != 0 ||
                Native.Z3_get_sort_kind(Context.nCtx, Native.Z3_get_range(Context.nCtx, f.NativeObject)) == (uint)Z3_sort_kind.Z3_ARRAY_SORT)
                throw new Z3Exception("Non-zero arity functions and arrays have FunctionInterpretations as a model. Use FuncInterp.");

            IntPtr n = Native.Z3_model_get_const_interp(Context.nCtx, NativeObject, f.NativeObject);
            if (n == IntPtr.Zero)
                return null;
            else
                return Expr.Create(Context, n);
        }

        /// <summary>
        /// Retrieves the interpretation (the assignment) of a non-constant <paramref name="f"/> in the model. 
        /// </summary>
        /// <param name="f">A function declaration of non-zero arity</param>
        /// <returns>A FunctionInterpretation if the function has an interpretation in the model, null otherwise.</returns> 
        public FuncInterp FuncInterp(FuncDecl f)
        {
            Debug.Assert(f != null);

            Context.CheckContextMatch(f);

            Z3_sort_kind sk = (Z3_sort_kind)Native.Z3_get_sort_kind(Context.nCtx, Native.Z3_get_range(Context.nCtx, f.NativeObject));

            if (f.Arity == 0)
            {
                IntPtr n = Native.Z3_model_get_const_interp(Context.nCtx, NativeObject, f.NativeObject);

                if (sk == Z3_sort_kind.Z3_ARRAY_SORT)
                {
                    if (n == IntPtr.Zero)
                        return null;
                    else
                    {
                        if (Native.Z3_is_as_array(Context.nCtx, n) == 0)
                            throw new Z3Exception("Argument was not an array constant");
                        IntPtr fd = Native.Z3_get_as_array_func_decl(Context.nCtx, n);
                        return FuncInterp(new FuncDecl(Context, fd));
                    }
                }
                else
                {
                    throw new Z3Exception("Constant functions do not have a function interpretation; use ConstInterp");
                }
            }
            else
            {
                IntPtr n = Native.Z3_model_get_func_interp(Context.nCtx, NativeObject, f.NativeObject);
                if (n == IntPtr.Zero)
                    return null;
                else
                    return new FuncInterp(Context, n);
            }
        }

        /// <summary>
        /// The number of constants that have an interpretation in the model.
        /// </summary>
        public uint NumConsts
        {
            get { return Native.Z3_model_get_num_consts(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// The function declarations of the constants in the model.
        /// </summary>
        public FuncDecl[] ConstDecls
        {
            get
            {

                uint n = NumConsts;
                FuncDecl[] res = new FuncDecl[n];
                for (uint i = 0; i < n; i++)
                    res[i] = new FuncDecl(Context, Native.Z3_model_get_const_decl(Context.nCtx, NativeObject, i));
                return res;
            }
        }

        /// <summary>
        /// Enumerate constants in model.
        /// </summary>
        public IEnumerable<KeyValuePair<FuncDecl, Expr>> Consts
        {
            get
            {
                uint nc = NumConsts;
                for (uint i = 0; i < nc; ++i)
                {
                    var f = new FuncDecl(Context, Native.Z3_model_get_const_decl(Context.nCtx, NativeObject, i));
                    IntPtr n = Native.Z3_model_get_const_interp(Context.nCtx, NativeObject, f.NativeObject);
                    if (n == IntPtr.Zero) continue;
                    yield return new KeyValuePair<FuncDecl, Expr>(f, Expr.Create(Context, n));
                }
            }
        }

        /// <summary>
        /// The number of function interpretations in the model.
        /// </summary>
        public uint NumFuncs
        {
            get { return Native.Z3_model_get_num_funcs(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// The function declarations of the function interpretations in the model.
        /// </summary>
        public FuncDecl[] FuncDecls
        {
            get
            {

                uint n = NumFuncs;
                FuncDecl[] res = new FuncDecl[n];
                for (uint i = 0; i < n; i++)
                    res[i] = new FuncDecl(Context, Native.Z3_model_get_func_decl(Context.nCtx, NativeObject, i));
                return res;
            }
        }

        /// <summary>
        /// All symbols that have an interpretation in the model.
        /// </summary>
        public FuncDecl[] Decls
        {
            get
            {

                uint nFuncs = NumFuncs;
                uint nConsts = NumConsts;
                uint n = nFuncs + nConsts;
                FuncDecl[] res = new FuncDecl[n];
                for (uint i = 0; i < nConsts; i++)
                    res[i] = new FuncDecl(Context, Native.Z3_model_get_const_decl(Context.nCtx, NativeObject, i));
                for (uint i = 0; i < nFuncs; i++)
                    res[nConsts + i] = new FuncDecl(Context, Native.Z3_model_get_func_decl(Context.nCtx, NativeObject, i));                
                return res;
            }
        }

        /// <summary>
        /// A ModelEvaluationFailedException is thrown when an expression cannot be evaluated by the model.
        /// </summary>
        public class ModelEvaluationFailedException : Z3Exception
        {
            /// <summary>
            /// An exception that is thrown when model evaluation fails.
            /// </summary>
            public ModelEvaluationFailedException() : base() { }
        }

        /// <summary>
        /// Evaluates the expression <paramref name="t"/> in the current model.
        /// </summary>
        /// <remarks>
        /// This function may fail if <paramref name="t"/> contains quantifiers, 
        /// is partial (MODEL_PARTIAL enabled), or if <paramref name="t"/> is not well-sorted.
        /// In this case a <c>ModelEvaluationFailedException</c> is thrown.
        /// </remarks>
        /// <param name="t">An expression</param>
        /// <param name="completion">
        /// When this flag is enabled, a model value will be assigned to any constant 
        /// or function that does not have an interpretation in the model.
        /// </param>
        /// <returns>The evaluation of <paramref name="t"/> in the model.</returns>        
        public Expr Eval(Expr t, bool completion = false)
        {
            Debug.Assert(t != null);

            IntPtr v = IntPtr.Zero;
            if (Native.Z3_model_eval(Context.nCtx, NativeObject, t.NativeObject, (byte)(completion ? 1 : 0), ref v) == (byte)0)
                throw new ModelEvaluationFailedException();
            else
                return Expr.Create(Context, v);
        }

        /// <summary>
        /// Alias for <c>Eval</c>.
        /// </summary>        
        public Expr Evaluate(Expr t, bool completion = false)
        {
            Debug.Assert(t != null);

            return Eval(t, completion);
        }

        /// <summary>
        /// Evaluate expression to a double, assuming it is a numeral already.
        /// </summary>
        public double Double(Expr t) {
            var r = Eval(t, true);
            return Native.Z3_get_numeral_double(Context.nCtx, r.NativeObject);
        }

        /// <summary>
        /// The number of uninterpreted sorts that the model has an interpretation for.
        /// </summary>    
        public uint NumSorts { get { return Native.Z3_model_get_num_sorts(Context.nCtx, NativeObject); } }

        /// <summary>
        /// The uninterpreted sorts that the model has an interpretation for. 
        /// </summary>
        /// <remarks>
        /// Z3 also provides an interpretation for uninterpreted sorts used in a formula.
        /// The interpretation for a sort is a finite set of distinct values. We say this finite set is
        /// the "universe" of the sort.
        /// </remarks>
        /// <seealso cref="NumSorts"/>
        /// <seealso cref="SortUniverse"/>
        public Sort[] Sorts
        {
            get
            {

                uint n = NumSorts;
                Sort[] res = new Sort[n];
                for (uint i = 0; i < n; i++)
                    res[i] = Sort.Create(Context, Native.Z3_model_get_sort(Context.nCtx, NativeObject, i));
                return res;
            }
        }

        /// <summary>
        /// The finite set of distinct values that represent the interpretation for sort <paramref name="s"/>.
        /// </summary>
        /// <seealso cref="Sorts"/>
        /// <param name="s">An uninterpreted sort</param>
        /// <returns>An array of expressions, where each is an element of the universe of <paramref name="s"/></returns>
        public Expr[] SortUniverse(Sort s)
        {
            Debug.Assert(s != null);

            ASTVector av = new ASTVector(Context, Native.Z3_model_get_sort_universe(Context.nCtx, NativeObject, s.NativeObject));            
            return av.ToExprArray();
        }

        /// <summary>
        /// Conversion of models to strings. 
        /// </summary>
        /// <returns>A string representation of the model.</returns>
        public override string ToString()
        {
            return Native.Z3_model_to_string(Context.nCtx, NativeObject);
        }

        #region Internal
        internal Model(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Debug.Assert(ctx != null);
        }

        internal class DecRefQueue : IDecRefQueue
        {
            public DecRefQueue() : base() { }
            public DecRefQueue(uint move_limit) : base(move_limit) { }
            internal override void IncRef(Context ctx, IntPtr obj)
            {
                Native.Z3_model_inc_ref(ctx.nCtx, obj);
            }

            internal override void DecRef(Context ctx, IntPtr obj)
            {
                Native.Z3_model_dec_ref(ctx.nCtx, obj);
            }
        };        

        internal override void IncRef(IntPtr o)
        {
            Context.Model_DRQ.IncAndClear(Context, o);
            base.IncRef(o);
        }

        internal override void DecRef(IntPtr o)
        {
            Context.Model_DRQ.Add(o);
            base.DecRef(o);
        }
        #endregion
    }
}
