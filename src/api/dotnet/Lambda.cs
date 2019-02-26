/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    Lambda.cs

Abstract:

    Z3 Managed API: Lambda

Author:

    Christoph Wintersteiger (cwinter) 2012-03-19

Notes:

--*/

using System;
using System.Diagnostics;
using System.Linq;

namespace Microsoft.Z3
{
    /// <summary>
    /// Lambda expressions.
    /// </summary>
    public class Lambda : ArrayExpr
    {
        /// <summary>
        /// The number of bound variables.
        /// </summary>
        public uint NumBound
        {
            get { return Native.Z3_get_quantifier_num_bound(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// The symbols for the bound variables.
        /// </summary>
        public Symbol[] BoundVariableNames
        {
            get
            {

                uint n = NumBound;
                Symbol[] res = new Symbol[n];
                for (uint i = 0; i < n; i++)
                    res[i] = Symbol.Create(Context, Native.Z3_get_quantifier_bound_name(Context.nCtx, NativeObject, i));
                return res;
            }
        }

        /// <summary>
        /// The sorts of the bound variables.
        /// </summary>
        public Sort[] BoundVariableSorts
        {
            get
            {

                uint n = NumBound;
                Sort[] res = new Sort[n];
                for (uint i = 0; i < n; i++)
                    res[i] = Sort.Create(Context, Native.Z3_get_quantifier_bound_sort(Context.nCtx, NativeObject, i));
                return res;
            }
        }

        /// <summary>
        /// The body of the lambda.
        /// </summary>
        public Expr Body
        {
            get
            {

                return Expr.Create(Context, Native.Z3_get_quantifier_body(Context.nCtx, NativeObject));
            }
        }

        /// <summary>
        /// Translates (copies) the lambda to the Context <paramref name="ctx"/>.
        /// </summary>
        /// <param name="ctx">A context</param>
        /// <returns>A copy of the lambda which is associated with <paramref name="ctx"/></returns>
        new public Lambda Translate(Context ctx)
        {
            return (Lambda)base.Translate(ctx);
        }

        #region Internal
        internal Lambda(Context ctx, Sort[] sorts, Symbol[] names, Expr body)
            : base(ctx, IntPtr.Zero)
        {
            Debug.Assert(ctx != null);
            Debug.Assert(sorts != null);
            Debug.Assert(names != null);
            Debug.Assert(body != null);
            Debug.Assert(sorts.Length == names.Length);
            Debug.Assert(sorts.All(s => s != null));
            Debug.Assert(names.All(n => n != null));
            Context.CheckContextMatch<Sort>(sorts);
            Context.CheckContextMatch<Symbol>(names);
            Context.CheckContextMatch(body);

            if (sorts.Length != names.Length)
                throw new Z3Exception("Number of sorts does not match number of names");

            NativeObject = Native.Z3_mk_lambda(ctx.nCtx, 
                                  AST.ArrayLength(sorts), AST.ArrayToNative(sorts),
                                  Symbol.ArrayToNative(names),
                                  body.NativeObject);
            
        }

        internal Lambda(Context ctx, Expr[] bound, Expr body)
            : base(ctx, IntPtr.Zero)
        {
            Debug.Assert(ctx != null);
            Debug.Assert(body != null);

            Debug.Assert(bound != null && bound.Length > 0 && bound.All(n => n != null));

            Context.CheckContextMatch<Expr>(bound);
            Context.CheckContextMatch(body);

            NativeObject = Native.Z3_mk_lambda_const(ctx.nCtx, 
                                                 AST.ArrayLength(bound), AST.ArrayToNative(bound),
                                                 body.NativeObject);
        }


        internal Lambda(Context ctx, IntPtr obj) : base(ctx, obj) { Debug.Assert(ctx != null); }

#if DEBUG
        internal override void CheckNativeObject(IntPtr obj)
        {
            if ((Z3_ast_kind)Native.Z3_get_ast_kind(Context.nCtx, obj) != Z3_ast_kind.Z3_QUANTIFIER_AST)
                throw new Z3Exception("Underlying object is not a quantifier");
            base.CheckNativeObject(obj);
        }
#endif
        #endregion
    }
}
