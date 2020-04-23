/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    Quantifier.cs

Abstract:

    Z3 Managed API: Quantifiers

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
    /// Quantifier expressions.
    /// </summary>
    public class Quantifier : BoolExpr
    {
        /// <summary>
        /// Indicates whether the quantifier is universal.
        /// </summary>
        public bool IsUniversal
        {
            get { return 0 != Native.Z3_is_quantifier_forall(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// Indicates whether the quantifier is existential.
        /// </summary>
        public bool IsExistential
        {
            get { return 0 != Native.Z3_is_quantifier_exists(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// The weight of the quantifier.
        /// </summary>
        public uint Weight
        {
            get { return Native.Z3_get_quantifier_weight(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// The number of patterns.
        /// </summary>
        public uint NumPatterns
        {
            get { return Native.Z3_get_quantifier_num_patterns(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// The patterns.
        /// </summary>
        public Pattern[] Patterns
        {
            get
            {

                uint n = NumPatterns;
                Pattern[] res = new Pattern[n];
                for (uint i = 0; i < n; i++)
                    res[i] = new Pattern(Context, Native.Z3_get_quantifier_pattern_ast(Context.nCtx, NativeObject, i));
                return res;
            }
        }

        /// <summary>
        /// The number of no-patterns.
        /// </summary>
        public uint NumNoPatterns
        {
            get { return Native.Z3_get_quantifier_num_no_patterns(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// The no-patterns.
        /// </summary>
        public Pattern[] NoPatterns
        {
            get
            {

                uint n = NumNoPatterns;
                Pattern[] res = new Pattern[n];
                for (uint i = 0; i < n; i++)
                    res[i] = new Pattern(Context, Native.Z3_get_quantifier_no_pattern_ast(Context.nCtx, NativeObject, i));
                return res;
            }
        }

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
        /// The body of the quantifier.
        /// </summary>
        public Expr Body
        {
            get
            {

                return Expr.Create(Context, Native.Z3_get_quantifier_body(Context.nCtx, NativeObject));
            }
        }

        /// <summary>
        /// Translates (copies) the quantifier to the Context <paramref name="ctx"/>.
        /// </summary>
        /// <param name="ctx">A context</param>
        /// <returns>A copy of the quantifier which is associated with <paramref name="ctx"/></returns>
        new public Quantifier Translate(Context ctx)
        {
            return (Quantifier)base.Translate(ctx);
        }

        #region Internal
        internal Quantifier(Context ctx, bool isForall, Sort[] sorts, Symbol[] names, Expr body, uint weight = 1, Pattern[] patterns = null, Expr[] noPatterns = null, Symbol quantifierID = null, Symbol skolemID = null)
            : base(ctx, IntPtr.Zero)
        {
            Debug.Assert(ctx != null);
            Debug.Assert(sorts != null);
            Debug.Assert(names != null);
            Debug.Assert(body != null);
            Debug.Assert(sorts.Length == names.Length);
            Debug.Assert(sorts.All(s => s != null));
            Debug.Assert(names.All(n => n != null));
            Debug.Assert(patterns == null || patterns.All(p => p != null));
            Debug.Assert(noPatterns == null || noPatterns.All(np => np != null));

            Context.CheckContextMatch<Pattern>(patterns);
            Context.CheckContextMatch<Expr>(noPatterns);
            Context.CheckContextMatch<Sort>(sorts);
            Context.CheckContextMatch<Symbol>(names);
            Context.CheckContextMatch(body);

            if (sorts.Length != names.Length)
                throw new Z3Exception("Number of sorts does not match number of names");

            if (noPatterns == null && quantifierID == null && skolemID == null)
            {
                NativeObject = Native.Z3_mk_quantifier(ctx.nCtx, (byte)(isForall ? 1 : 0) , weight,
                                           AST.ArrayLength(patterns), AST.ArrayToNative(patterns),
                                           AST.ArrayLength(sorts), AST.ArrayToNative(sorts),
                                           Symbol.ArrayToNative(names),
                                           body.NativeObject);
            }
            else
            {
                NativeObject = Native.Z3_mk_quantifier_ex(ctx.nCtx, (byte)(isForall ? 1 : 0), weight,
                                  AST.GetNativeObject(quantifierID), AST.GetNativeObject(skolemID),
                                  AST.ArrayLength(patterns), AST.ArrayToNative(patterns),
                                  AST.ArrayLength(noPatterns), AST.ArrayToNative(noPatterns),
                                  AST.ArrayLength(sorts), AST.ArrayToNative(sorts),
                                  Symbol.ArrayToNative(names),
                                  body.NativeObject);
            }
        }

        internal Quantifier(Context ctx, bool isForall, Expr[] bound, Expr body, uint weight = 1, Pattern[] patterns = null, Expr[] noPatterns = null, Symbol quantifierID = null, Symbol skolemID = null)
            : base(ctx, IntPtr.Zero)
        {
            Debug.Assert(ctx != null);
            Debug.Assert(body != null);

            Debug.Assert(patterns == null || patterns.All(p => p != null));
            Debug.Assert(noPatterns == null || noPatterns.All(np => np != null));
            Debug.Assert(bound == null || bound.All(n => n != null));

            Context.CheckContextMatch<Expr>(noPatterns);
            Context.CheckContextMatch<Pattern>(patterns);
            //Context.CheckContextMatch(bound);
            Context.CheckContextMatch(body);

            if (noPatterns == null && quantifierID == null && skolemID == null)
            {
                NativeObject = Native.Z3_mk_quantifier_const(ctx.nCtx, (byte)(isForall ? 1 : 0) , weight,
                                                 AST.ArrayLength(bound), AST.ArrayToNative(bound),
                                                 AST.ArrayLength(patterns), AST.ArrayToNative(patterns),
                                                 body.NativeObject);
            }
            else
            {
                NativeObject = Native.Z3_mk_quantifier_const_ex(ctx.nCtx, (byte)(isForall ? 1 : 0), weight,
                                        AST.GetNativeObject(quantifierID), AST.GetNativeObject(skolemID),
                                        AST.ArrayLength(bound), AST.ArrayToNative(bound),
                                        AST.ArrayLength(patterns), AST.ArrayToNative(patterns),
                                        AST.ArrayLength(noPatterns), AST.ArrayToNative(noPatterns),
                                        body.NativeObject);
            }
        }


        internal Quantifier(Context ctx, IntPtr obj) : base(ctx, obj) { Debug.Assert(ctx != null); }

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
