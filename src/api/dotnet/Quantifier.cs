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
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// Quantifier expressions.
    /// </summary>
    [ContractVerification(true)]
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
                Contract.Ensures(Contract.Result<Pattern[]>() != null);

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
                Contract.Ensures(Contract.Result<Pattern[]>() != null);

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
                Contract.Ensures(Contract.Result<Symbol[]>() != null);

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
                Contract.Ensures(Contract.Result<Sort[]>() != null);

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
        public BoolExpr Body
        {
            get
            {
                Contract.Ensures(Contract.Result<BoolExpr>() != null);

                return new BoolExpr(Context, Native.Z3_get_quantifier_body(Context.nCtx, NativeObject));
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
        [ContractVerification(false)] // F: Clousot ForAll decompilation gets confused below. Setting verification off until I fixed the bug
        internal Quantifier(Context ctx, bool isForall, Sort[] sorts, Symbol[] names, Expr body, uint weight = 1, Pattern[] patterns = null, Expr[] noPatterns = null, Symbol quantifierID = null, Symbol skolemID = null)
            : base(ctx, IntPtr.Zero)
        {
            Contract.Requires(ctx != null);
            Contract.Requires(sorts != null);
            Contract.Requires(names != null);
            Contract.Requires(body != null);
            Contract.Requires(sorts.Length == names.Length);
            Contract.Requires(Contract.ForAll(sorts, s => s != null));
            Contract.Requires(Contract.ForAll(names, n => n != null));
            Contract.Requires(patterns == null || Contract.ForAll(patterns, p => p != null));
            Contract.Requires(noPatterns == null || Contract.ForAll(noPatterns, np => np != null));

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

        [ContractVerification(false)] // F: Clousot ForAll decompilation gets confused below. Setting verification off until I fixed the bug
        internal Quantifier(Context ctx, bool isForall, Expr[] bound, Expr body, uint weight = 1, Pattern[] patterns = null, Expr[] noPatterns = null, Symbol quantifierID = null, Symbol skolemID = null)
            : base(ctx, IntPtr.Zero)
        {
            Contract.Requires(ctx != null);
            Contract.Requires(body != null);

            Contract.Requires(patterns == null || Contract.ForAll(patterns, p => p != null));
            Contract.Requires(noPatterns == null || Contract.ForAll(noPatterns, np => np != null));
            Contract.Requires(bound == null || Contract.ForAll(bound, n => n != null));

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


        internal Quantifier(Context ctx, IntPtr obj) : base(ctx, obj) { Contract.Requires(ctx != null); }

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
