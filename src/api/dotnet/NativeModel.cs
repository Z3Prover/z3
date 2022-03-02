﻿/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    NativeModel.cs

Abstract:

    Z3 Managed API: Models
    Native interface to model objects.    

Author:

    Christoph Wintersteiger (cwinter) 2012-03-21
    Nikolaj Bjorner (nbjorner) 2022-03-01

Notes:
    
--*/

using System;
using System.Diagnostics;
using System.Collections.Generic;

namespace Microsoft.Z3
{
    using Z3_context = System.IntPtr;
    using Z3_ast = System.IntPtr;
    using Z3_app = System.IntPtr;
    using Z3_sort = System.IntPtr;
    using Z3_func_decl = System.IntPtr;
    using Z3_model = System.IntPtr;
    using Z3_func_interp = System.IntPtr;
    using Z3_func_entry = System.IntPtr;

    /// <summary>
    /// A Model contains interpretations (assignments) of constants and functions. 
    /// </summary>
    public class NativeModel : IDisposable
    {
        /// <summary>
        /// Retrieves the interpretation (the assignment) of <paramref name="a"/> in the model. 
        /// </summary>
        /// <param name="a">A Constant</param>
        /// <returns>An expression if the constant has an interpretation in the model, null otherwise.</returns>
        public Z3_ast ConstInterp(Z3_ast a) => ConstInterp(Native.Z3_get_app_decl(Context.nCtx, a));

        /// <summary>
        /// Retrieves the interpretation (the assignment) of <paramref name="f"/> in the model. 
        /// </summary>
        /// <param name="f">A function declaration of zero arity</param>
        /// <returns>An expression if the function has an interpretation in the model, null otherwise.</returns>    
        public Z3_ast ConstFuncInterp(Z3_func_decl f)
        {
            if (Native.Z3_get_arity(Context.nCtx, f) != 0)
                throw new Z3Exception("Non-zero arity functions have FunctionInterpretations as a model. Use FuncInterp.");

            return Native.Z3_model_get_const_interp(Context.nCtx, NativeObject, f);
        }

        /// <summary>
        /// Retrieves the interpretation (the assignment) of a non-constant <paramref name="f"/> in the model. 
        /// </summary>
        /// <param name="f">A function declaration of non-zero arity</param>
        /// <returns>A FunctionInterpretation if the function has an interpretation in the model, null otherwise.</returns> 
        public NativeFuncInterp FuncInterp(Z3_func_decl f)
        {

            Z3_sort_kind sk = (Z3_sort_kind)Native.Z3_get_sort_kind(Context.nCtx, Native.Z3_get_range(Context.nCtx, f));

            if (Native.Z3_get_arity(Context.nCtx, f) == 0)
            {
                IntPtr n = Native.Z3_model_get_const_interp(Context.nCtx, NativeObject, f);

                if (sk == Z3_sort_kind.Z3_ARRAY_SORT)
                {
                    if (n == IntPtr.Zero)
                        return null;
                    else
                    {
                        if (Native.Z3_is_as_array(Context.nCtx, n) == 0)
                            throw new Z3Exception("Argument was not an array constant");
                        var fd = Native.Z3_get_as_array_func_decl(Context.nCtx, n);
                        return new NativeFuncInterp(Context, this, f, fd);
                    }
                }
                else
                {
                    throw new Z3Exception("Constant functions do not have a function interpretation; use ConstInterp");
                }
            }
            else
            {
                IntPtr n = Native.Z3_model_get_func_interp(Context.nCtx, NativeObject, f);
                if (n == IntPtr.Zero)
                    return null;
                else
                    return new NativeFuncInterp(Context, this, f, n);
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
        public Z3_func_decl[] ConstDecls
        {
            get
            {

                uint n = NumConsts;
                Z3_func_decl[] res = new Z3_func_decl[n];
                for (uint i = 0; i < n; i++)
                    res[i] = Native.Z3_model_get_const_decl(Context.nCtx, NativeObject, i);
                return res;
            }
        }


        /// <summary>
        /// Enumerate constants in model.
        /// </summary>
        public IEnumerable<KeyValuePair<Z3_func_decl, Z3_ast>> Consts
        {
            get
            {
                uint nc = NumConsts;
                for (uint i = 0; i < nc; ++i)
                {
                    var f = Native.Z3_model_get_const_decl(Context.nCtx, NativeObject, i);
                    IntPtr n = Native.Z3_model_get_const_interp(Context.nCtx, NativeObject, f);
                    if (n == IntPtr.Zero) continue;
                    yield return new KeyValuePair<Z3_func_decl, Z3_ast>(f, n);
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
        public Z3_func_decl[] FuncDecls
        {
            get
            {

                uint n = NumFuncs;
                Z3_func_decl[] res = new Z3_func_decl[n];
                for (uint i = 0; i < n; i++)
                    res[i] = Native.Z3_model_get_func_decl(Context.nCtx, NativeObject, i);
                return res;
            }
        }


        /// <summary>
        /// All symbols that have an interpretation in the model.
        /// </summary>
        public Z3_func_decl[] Decls
        {
            get
            {

                uint nFuncs = NumFuncs;
                uint nConsts = NumConsts;
                uint n = nFuncs + nConsts;
                Z3_func_decl[] res = new Z3_func_decl[n];
                for (uint i = 0; i < nConsts; i++)
                    res[i] = Native.Z3_model_get_const_decl(Context.nCtx, NativeObject, i);
                for (uint i = 0; i < nFuncs; i++)
                    res[nConsts + i] = Native.Z3_model_get_func_decl(Context.nCtx, NativeObject, i);
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
        public Z3_ast Eval(Z3_ast t, bool completion = false)
        {

            IntPtr v = IntPtr.Zero;
            if (Native.Z3_model_eval(Context.nCtx, NativeObject, t, (byte)(completion ? 1 : 0), ref v) == (byte)0)
                throw new ModelEvaluationFailedException();
            else
                return v;
        }

        /// <summary>
        /// Alias for <c>Eval</c>.
        /// </summary>        
        public Z3_ast Evaluate(Z3_ast t, bool completion = false) => Eval(t, completion);


        /// <summary>
        /// Evaluate expression to a double, assuming it is a numeral already.
        /// </summary>
        public double Double(Z3_ast t)
        {
            var r = Eval(t, true);
            return Native.Z3_get_numeral_double(Context.nCtx, r);
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
        public Z3_sort[] Sorts
        {
            get
            {

                uint n = NumSorts;
                Z3_sort[] res = new Z3_sort[n];
                for (uint i = 0; i < n; i++)
                    res[i] = Native.Z3_model_get_sort(Context.nCtx, NativeObject, i);
                return res;
            }
        }


        /// <summary>
        /// Conversion of models to strings. 
        /// </summary>
        /// <returns>A string representation of the model.</returns>
        public override string ToString()
        {
            return Native.Z3_model_to_string(Context.nCtx, NativeObject);
        }


        IntPtr NativeObject;
        NativeContext Context;

        internal NativeModel(NativeContext ctx, IntPtr obj)
        {
            Context = ctx;
            NativeObject = obj;
            Debug.Assert(ctx != null);
            Native.Z3_model_inc_ref(ctx.nCtx, obj);
        }


        /// <summary>
        /// Finalizer.
        /// </summary>
        ~NativeModel()
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
                Native.Z3_model_dec_ref(Context.nCtx, NativeObject);
                NativeObject = IntPtr.Zero;
            }
            GC.SuppressFinalize(this);
        }


    }
}



