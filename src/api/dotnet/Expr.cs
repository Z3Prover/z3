/*++
Copyright (<c>) 2012 Microsoft Corporation

Module Name:

    Expr.cs

Abstract:

    Z3 Managed API: Expressions

Author:

    Christoph Wintersteiger (cwinter) 2012-03-20

Notes:

--*/

using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// Expressions are terms.
    /// </summary>
    [ContractVerification(true)]
    public class Expr : AST
    {
        /// <summary>
        /// Returns a simplified version of the expression.
        /// </summary>
        /// <param name="p">A set of parameters to configure the simplifier</param>
        /// <seealso cref="Context.SimplifyHelp"/>
        public Expr Simplify(Params p = null)
        {
            Contract.Ensures(Contract.Result<Expr>() != null);

            if (p == null)
                return Expr.Create(Context, Native.Z3_simplify(Context.nCtx, NativeObject));
            else
                return Expr.Create(Context, Native.Z3_simplify_ex(Context.nCtx, NativeObject, p.NativeObject));
        }

        /// <summary>
        /// The function declaration of the function that is applied in this expression.
        /// </summary>
        public FuncDecl FuncDecl
        {
            get
            {
                Contract.Ensures(Contract.Result<FuncDecl>() != null);
                return new FuncDecl(Context, Native.Z3_get_app_decl(Context.nCtx, NativeObject));
            }
        }

        /// <summary>
        /// Indicates whether the expression is the true or false expression
        /// or something else (Z3_L_UNDEF).
        /// </summary>
        public Z3_lbool BoolValue
        {
            get { return (Z3_lbool)Native.Z3_get_bool_value(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// The number of arguments of the expression.
        /// </summary>
        public uint NumArgs
        {
            get { return Native.Z3_get_app_num_args(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// The arguments of the expression.
        /// </summary>
        public Expr[] Args
        {
            get
            {
                Contract.Ensures(Contract.Result<Expr[]>() != null);

                uint n = NumArgs;
                Expr[] res = new Expr[n];
                for (uint i = 0; i < n; i++)
                    res[i] = Expr.Create(Context, Native.Z3_get_app_arg(Context.nCtx, NativeObject, i));
                return res;
            }
        }

        /// <summary>
        /// Update the arguments of the expression using the arguments <paramref name="args"/>
        /// The number of new arguments should coincide with the current number of arguments.
        /// </summary>
        public void Update(Expr[] args)
        {
            Contract.Requires(args != null);
            Contract.Requires(Contract.ForAll(args, a => a != null));

            Context.CheckContextMatch<Expr>(args);
            if (IsApp && args.Length != NumArgs)
                throw new Z3Exception("Number of arguments does not match");
            NativeObject = Native.Z3_update_term(Context.nCtx, NativeObject, (uint)args.Length, Expr.ArrayToNative(args));
        }

        /// <summary>
        /// Substitute every occurrence of <c>from[i]</c> in the expression with <c>to[i]</c>, for <c>i</c> smaller than <c>num_exprs</c>.
        /// </summary>
        /// <remarks>
        /// The result is the new expression. The arrays <c>from</c> and <c>to</c> must have size <c>num_exprs</c>.
        /// For every <c>i</c> smaller than <c>num_exprs</c>, we must have that
        /// sort of <c>from[i]</c> must be equal to sort of <c>to[i]</c>.
        /// </remarks>
        public Expr Substitute(Expr[] from, Expr[] to)
        {
            Contract.Requires(from != null);
            Contract.Requires(to != null);
            Contract.Requires(Contract.ForAll(from, f => f != null));
            Contract.Requires(Contract.ForAll(to, t => t != null));
            Contract.Ensures(Contract.Result<Expr>() != null);

            Context.CheckContextMatch<Expr>(from);
            Context.CheckContextMatch<Expr>(to);
            if (from.Length != to.Length)
                throw new Z3Exception("Argument sizes do not match");
            return Expr.Create(Context, Native.Z3_substitute(Context.nCtx, NativeObject, (uint)from.Length, Expr.ArrayToNative(from), Expr.ArrayToNative(to)));
        }

        /// <summary>
        /// Substitute every occurrence of <c>from</c> in the expression with <c>to</c>.
        /// </summary>
        /// <seealso cref="Substitute(Expr[],Expr[])"/>
        public Expr Substitute(Expr from, Expr to)
        {
            Contract.Requires(from != null);
            Contract.Requires(to != null);
            Contract.Ensures(Contract.Result<Expr>() != null);

            return Substitute(new Expr[] { from }, new Expr[] { to });
        }

        /// <summary>
        /// Substitute the free variables in the expression with the expressions in <paramref name="to"/>
        /// </summary>
        /// <remarks>
        /// For every <c>i</c> smaller than <c>num_exprs</c>, the variable with de-Bruijn index <c>i</c> is replaced with term <c>to[i]</c>.
        /// </remarks>
        public Expr SubstituteVars(Expr[] to)
        {
            Contract.Requires(to != null);
            Contract.Requires(Contract.ForAll(to, t => t != null));
            Contract.Ensures(Contract.Result<Expr>() != null);

            Context.CheckContextMatch<Expr>(to);
            return Expr.Create(Context, Native.Z3_substitute_vars(Context.nCtx, NativeObject, (uint)to.Length, Expr.ArrayToNative(to)));
        }

        /// <summary>
        /// Translates (copies) the term to the Context <paramref name="ctx"/>.
        /// </summary>
        /// <param name="ctx">A context</param>
        /// <returns>A copy of the term which is associated with <paramref name="ctx"/></returns>
        new public Expr Translate(Context ctx)
        {
            Contract.Requires(ctx != null);
            Contract.Ensures(Contract.Result<Expr>() != null);

            if (ReferenceEquals(Context, ctx))
                return this;
            else
                return Expr.Create(ctx, Native.Z3_translate(Context.nCtx, NativeObject, ctx.nCtx));
        }

        /// <summary>
        /// Returns a string representation of the expression.
        /// </summary>
        public override string ToString()
        {
            return base.ToString();
        }

        /// <summary>
        /// Indicates whether the term is a numeral
        /// </summary>
        public bool IsNumeral
        {
            get { return Native.Z3_is_numeral_ast(Context.nCtx, NativeObject) != 0; }
        }

        /// <summary>
        /// Indicates whether the term is well-sorted.
        /// </summary>
        /// <returns>True if the term is well-sorted, false otherwise.</returns>
        public bool IsWellSorted
        {
            get { return Native.Z3_is_well_sorted(Context.nCtx, NativeObject) != 0; }
        }

        /// <summary>
        /// The Sort of the term.
        /// </summary>
        public Sort Sort
        {
            get
            {
                Contract.Ensures(Contract.Result<Sort>() != null);
                return Sort.Create(Context, Native.Z3_get_sort(Context.nCtx, NativeObject));
            }
        }

        #region Constants
        /// <summary>
        /// Indicates whether the term represents a constant.
        /// </summary>
        public bool IsConst
        {
            get { return IsApp && NumArgs == 0 && FuncDecl.DomainSize == 0; }
        }
        #endregion

        #region Integer Numerals
        /// <summary>
        /// Indicates whether the term is an integer numeral.
        /// </summary>
        public bool IsIntNum
        {
            get { return IsNumeral && IsInt; }
        }
        #endregion

        #region Real Numerals
        /// <summary>
        /// Indicates whether the term is a real numeral.
        /// </summary>
        public bool IsRatNum
        {
            get { return IsNumeral && IsReal; }
        }
        #endregion

        #region Algebraic Numbers
        /// <summary>
        /// Indicates whether the term is an algebraic number
        /// </summary>
        public bool IsAlgebraicNumber
        {
            get { return Native.Z3_is_algebraic_number(Context.nCtx, NativeObject) != 0; }
        }
        #endregion

        #region Term Kind Tests

        #region Boolean Terms
        /// <summary>
        /// Indicates whether the term has Boolean sort.
        /// </summary>
        public bool IsBool
        {
            get
            {
                return (IsExpr &&
                        Native.Z3_is_eq_sort(Context.nCtx,
                                              Native.Z3_mk_bool_sort(Context.nCtx),
                                              Native.Z3_get_sort(Context.nCtx, NativeObject)) != 0);
            }
        }

        /// <summary>
        /// Indicates whether the term is the constant true.
        /// </summary>
        public bool IsTrue { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_TRUE; } }

        /// <summary>
        /// Indicates whether the term is the constant false.
        /// </summary>
        public bool IsFalse { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FALSE; } }

        /// <summary>
        /// Indicates whether the term is an equality predicate.
        /// </summary>
        public bool IsEq { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_EQ; } }

        /// <summary>
        /// Indicates whether the term is an n-ary distinct predicate (every argument is mutually distinct).
        /// </summary>
        public bool IsDistinct { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_DISTINCT; } }

        /// <summary>
        /// Indicates whether the term is a ternary if-then-else term
        /// </summary>
        public bool IsITE { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_ITE; } }

        /// <summary>
        /// Indicates whether the term is an n-ary conjunction
        /// </summary>
        public bool IsAnd { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_AND; } }

        /// <summary>
        /// Indicates whether the term is an n-ary disjunction
        /// </summary>
        public bool IsOr { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_OR; } }

        /// <summary>
        /// Indicates whether the term is an if-and-only-if (Boolean equivalence, binary)
        /// </summary>
        public bool IsIff { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_IFF; } }

        /// <summary>
        /// Indicates whether the term is an exclusive or
        /// </summary>
        public bool IsXor { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_XOR; } }

        /// <summary>
        /// Indicates whether the term is a negation
        /// </summary>
        public bool IsNot { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_NOT; } }

        /// <summary>
        /// Indicates whether the term is an implication
        /// </summary>
        public bool IsImplies { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_IMPLIES; } }

        #endregion

        #region Interpolation
        /// <summary>
        /// Indicates whether the term is marked for interpolation.
        /// </summary>
        /// <remarks></remarks>
        public bool IsInterpolant { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_INTERP; } }
        #endregion

        #region Arithmetic Terms
        /// <summary>
        /// Indicates whether the term is of integer sort.
        /// </summary>
        public bool IsInt
        {
            get { return Native.Z3_get_sort_kind(Context.nCtx, Native.Z3_get_sort(Context.nCtx, NativeObject)) == (uint)Z3_sort_kind.Z3_INT_SORT; }
        }

        /// <summary>
        /// Indicates whether the term is of sort real.
        /// </summary>
        public bool IsReal
        {
            get { return Native.Z3_get_sort_kind(Context.nCtx, Native.Z3_get_sort(Context.nCtx, NativeObject)) == (uint)Z3_sort_kind.Z3_REAL_SORT; }
        }

        /// <summary>
        /// Indicates whether the term is an arithmetic numeral.
        /// </summary>
        public bool IsArithmeticNumeral { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_ANUM; } }

        /// <summary>
        /// Indicates whether the term is a less-than-or-equal
        /// </summary>
        public bool IsLE { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_LE; } }

        /// <summary>
        /// Indicates whether the term is a greater-than-or-equal
        /// </summary>
        public bool IsGE { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_GE; } }

        /// <summary>
        /// Indicates whether the term is a less-than
        /// </summary>
        public bool IsLT { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_LT; } }

        /// <summary>
        /// Indicates whether the term is a greater-than
        /// </summary>
        public bool IsGT { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_GT; } }

        /// <summary>
        /// Indicates whether the term is addition (binary)
        /// </summary>
        public bool IsAdd { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_ADD; } }

        /// <summary>
        /// Indicates whether the term is subtraction (binary)
        /// </summary>
        public bool IsSub { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_SUB; } }

        /// <summary>
        /// Indicates whether the term is a unary minus
        /// </summary>
        public bool IsUMinus { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_UMINUS; } }

        /// <summary>
        /// Indicates whether the term is multiplication (binary)
        /// </summary>
        public bool IsMul { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_MUL; } }

        /// <summary>
        /// Indicates whether the term is division (binary)
        /// </summary>
        public bool IsDiv { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_DIV; } }

        /// <summary>
        /// Indicates whether the term is integer division (binary)
        /// </summary>
        public bool IsIDiv { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_IDIV; } }

        /// <summary>
        /// Indicates whether the term is remainder (binary)
        /// </summary>
        public bool IsRemainder { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_REM; } }

        /// <summary>
        /// Indicates whether the term is modulus (binary)
        /// </summary>
        public bool IsModulus { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_MOD; } }

        /// <summary>
        /// Indicates whether the term is a coercion of integer to real (unary)
        /// </summary>
        public bool IsIntToReal { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_TO_REAL; } }

        /// <summary>
        /// Indicates whether the term is a coercion of real to integer (unary)
        /// </summary>
        public bool IsRealToInt { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_TO_INT; } }

        /// <summary>
        /// Indicates whether the term is a check that tests whether a real is integral (unary)
        /// </summary>
        public bool IsRealIsInt { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_IS_INT; } }
        #endregion

        #region Array Terms
        /// <summary>
        /// Indicates whether the term is of an array sort.
        /// </summary>
        public bool IsArray
        {
            get
            {
                return (Native.Z3_is_app(Context.nCtx, NativeObject) != 0 &&
                        (Z3_sort_kind)Native.Z3_get_sort_kind(Context.nCtx, Native.Z3_get_sort(Context.nCtx, NativeObject))
                        == Z3_sort_kind.Z3_ARRAY_SORT);
            }
        }

        /// <summary>
        /// Indicates whether the term is an array store.
        /// </summary>
        /// <remarks>It satisfies select(store(a,i,v),j) = if i = j then v else select(a,j).
        /// Array store takes at least 3 arguments. </remarks>
        public bool IsStore { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_STORE; } }

        /// <summary>
        /// Indicates whether the term is an array select.
        /// </summary>
        public bool IsSelect { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_SELECT; } }

        /// <summary>
        /// Indicates whether the term is a constant array.
        /// </summary>
        /// <remarks>For example, select(const(v),i) = v holds for every v and i. The function is unary.</remarks>
        public bool IsConstantArray { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_CONST_ARRAY; } }

        /// <summary>
        /// Indicates whether the term is a default array.
        /// </summary>
        /// <remarks>For example default(const(v)) = v. The function is unary.</remarks>
        public bool IsDefaultArray { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_ARRAY_DEFAULT; } }

        /// <summary>
        /// Indicates whether the term is an array map.
        /// </summary>
        /// <remarks>It satisfies map[f](a1,..,a_n)[i] = f(a1[i],...,a_n[i]) for every i.</remarks>
        public bool IsArrayMap { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_ARRAY_MAP; } }

        /// <summary>
        /// Indicates whether the term is an as-array term.
        /// </summary>
        /// <remarks>An as-array term is n array value that behaves as the function graph of the
        /// function passed as parameter.</remarks>
        public bool IsAsArray { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_AS_ARRAY; } }
        #endregion

        #region Set Terms
        /// <summary>
        /// Indicates whether the term is set union
        /// </summary>
        public bool IsSetUnion { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_SET_UNION; } }

        /// <summary>
        /// Indicates whether the term is set intersection
        /// </summary>
        public bool IsSetIntersect { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_SET_INTERSECT; } }

        /// <summary>
        /// Indicates whether the term is set difference
        /// </summary>
        public bool IsSetDifference { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_SET_DIFFERENCE; } }

        /// <summary>
        /// Indicates whether the term is set complement
        /// </summary>
        public bool IsSetComplement { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_SET_COMPLEMENT; } }

        /// <summary>
        /// Indicates whether the term is set subset
        /// </summary>
        public bool IsSetSubset { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_SET_SUBSET; } }
        #endregion

        #region Bit-vector terms
        /// <summary>
        ///  Indicates whether the terms is of bit-vector sort.
        /// </summary>
        public bool IsBV
        {
            get { return Native.Z3_get_sort_kind(Context.nCtx, Native.Z3_get_sort(Context.nCtx, NativeObject)) == (uint)Z3_sort_kind.Z3_BV_SORT; }
        }

        /// <summary>
        /// Indicates whether the term is a bit-vector numeral
        /// </summary>
        public bool IsBVNumeral { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BNUM; } }

        /// <summary>
        /// Indicates whether the term is a one-bit bit-vector with value one
        /// </summary>
        public bool IsBVBitOne { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BIT1; } }

        /// <summary>
        /// Indicates whether the term is a one-bit bit-vector with value zero
        /// </summary>
        public bool IsBVBitZero { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BIT0; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector unary minus
        /// </summary>
        public bool IsBVUMinus { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BNEG; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector addition (binary)
        /// </summary>
        public bool IsBVAdd { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BADD; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector subtraction (binary)
        /// </summary>
        public bool IsBVSub { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BSUB; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector multiplication (binary)
        /// </summary>
        public bool IsBVMul { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BMUL; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector signed division (binary)
        /// </summary>
        public bool IsBVSDiv { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BSDIV; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector unsigned division (binary)
        /// </summary>
        public bool IsBVUDiv { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BUDIV; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector signed remainder (binary)
        /// </summary>
        public bool IsBVSRem { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BSREM; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector unsigned remainder (binary)
        /// </summary>
        public bool IsBVURem { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BUREM; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector signed modulus
        /// </summary>
        public bool IsBVSMod { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BSMOD; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector signed division by zero
        /// </summary>
        internal bool IsBVSDiv0 { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BSDIV0; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector unsigned division by zero
        /// </summary>
        internal bool IsBVUDiv0 { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BUDIV0; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector signed remainder by zero
        /// </summary>
        internal bool IsBVSRem0 { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BSREM0; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector unsigned remainder by zero
        /// </summary>
        internal bool IsBVURem0 { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BUREM0; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector signed modulus by zero
        /// </summary>
        internal bool IsBVSMod0 { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BSMOD0; } }

        /// <summary>
        /// Indicates whether the term is an unsigned bit-vector less-than-or-equal
        /// </summary>
        public bool IsBVULE { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_ULEQ; } }

        /// <summary>
        /// Indicates whether the term is a signed bit-vector less-than-or-equal
        /// </summary>
        public bool IsBVSLE { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_SLEQ; } }

        /// <summary>
        /// Indicates whether the term is an unsigned bit-vector greater-than-or-equal
        /// </summary>
        public bool IsBVUGE { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_UGEQ; } }

        /// <summary>
        /// Indicates whether the term is a signed bit-vector greater-than-or-equal
        /// </summary>
        public bool IsBVSGE { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_SGEQ; } }

        /// <summary>
        /// Indicates whether the term is an unsigned bit-vector less-than
        /// </summary>
        public bool IsBVULT { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_ULT; } }

        /// <summary>
        /// Indicates whether the term is a signed bit-vector less-than
        /// </summary>
        public bool IsBVSLT { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_SLT; } }

        /// <summary>
        /// Indicates whether the term is an unsigned bit-vector greater-than
        /// </summary>
        public bool IsBVUGT { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_UGT; } }

        /// <summary>
        /// Indicates whether the term is a signed bit-vector greater-than
        /// </summary>
        public bool IsBVSGT { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_SGT; } }

        /// <summary>
        /// Indicates whether the term is a bit-wise AND
        /// </summary>
        public bool IsBVAND { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BAND; } }

        /// <summary>
        /// Indicates whether the term is a bit-wise OR
        /// </summary>
        public bool IsBVOR { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BOR; } }

        /// <summary>
        /// Indicates whether the term is a bit-wise NOT
        /// </summary>
        public bool IsBVNOT { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BNOT; } }

        /// <summary>
        /// Indicates whether the term is a bit-wise XOR
        /// </summary>
        public bool IsBVXOR { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BXOR; } }

        /// <summary>
        /// Indicates whether the term is a bit-wise NAND
        /// </summary>
        public bool IsBVNAND { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BNAND; } }

        /// <summary>
        /// Indicates whether the term is a bit-wise NOR
        /// </summary>
        public bool IsBVNOR { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BNOR; } }

        /// <summary>
        /// Indicates whether the term is a bit-wise XNOR
        /// </summary>
        public bool IsBVXNOR { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BXNOR; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector concatenation (binary)
        /// </summary>
        public bool IsBVConcat { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_CONCAT; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector sign extension
        /// </summary>
        public bool IsBVSignExtension { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_SIGN_EXT; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector zero extension
        /// </summary>
        public bool IsBVZeroExtension { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_ZERO_EXT; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector extraction
        /// </summary>
        public bool IsBVExtract { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_EXTRACT; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector repetition
        /// </summary>
        public bool IsBVRepeat { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_REPEAT; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector reduce OR
        /// </summary>
        public bool IsBVReduceOR { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BREDOR; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector reduce AND
        /// </summary>
        public bool IsBVReduceAND { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BREDAND; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector comparison
        /// </summary>
        public bool IsBVComp { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BCOMP; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector shift left
        /// </summary>
        public bool IsBVShiftLeft { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BSHL; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector logical shift right
        /// </summary>
        public bool IsBVShiftRightLogical { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BLSHR; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector arithmetic shift left
        /// </summary>
        public bool IsBVShiftRightArithmetic { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BASHR; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector rotate left
        /// </summary>
        public bool IsBVRotateLeft { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_ROTATE_LEFT; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector rotate right
        /// </summary>
        public bool IsBVRotateRight { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_ROTATE_RIGHT; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector rotate left (extended)
        /// </summary>
        /// <remarks>Similar to Z3_OP_ROTATE_LEFT, but it is a binary operator instead of a parametric one.</remarks>
        public bool IsBVRotateLeftExtended { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_EXT_ROTATE_LEFT; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector rotate right (extended)
        /// </summary>
        /// <remarks>Similar to Z3_OP_ROTATE_RIGHT, but it is a binary operator instead of a parametric one.</remarks>
        public bool IsBVRotateRightExtended { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_EXT_ROTATE_RIGHT; } }

        /// <summary>
        /// Indicates whether the term is a coercion from integer to bit-vector
        /// </summary>
        /// <remarks>This function is not supported by the decision procedures. Only the most
        /// rudimentary simplification rules are applied to this function.</remarks>
        public bool IsIntToBV { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_INT2BV; } }

        /// <summary>
        /// Indicates whether the term is a coercion from bit-vector to integer
        /// </summary>
        /// <remarks>This function is not supported by the decision procedures. Only the most
        /// rudimentary simplification rules are applied to this function.</remarks>
        public bool IsBVToInt { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_BV2INT; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector carry
        /// </summary>
        /// <remarks>Compute the carry bit in a full-adder.  The meaning is given by the
        /// equivalence (carry l1 l2 l3) &lt;=&gt; (or (and l1 l2) (and l1 l3) (and l2 l3)))</remarks>
        public bool IsBVCarry { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_CARRY; } }

        /// <summary>
        /// Indicates whether the term is a bit-vector ternary XOR
        /// </summary>
        /// <remarks>The meaning is given by the equivalence (xor3 l1 l2 l3) &lt;=&gt; (xor (xor l1 l2) l3)</remarks>
        public bool IsBVXOR3 { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_XOR3; } }

        #endregion

        #region Labels
        /// <summary>
        /// Indicates whether the term is a label (used by the Boogie Verification condition generator).
        /// </summary>
        /// <remarks>The label has two parameters, a string and a Boolean polarity. It takes one argument, a formula.</remarks>
        public bool IsLabel { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_LABEL; } }

        /// <summary>
        /// Indicates whether the term is a label literal (used by the Boogie Verification condition generator).
        /// </summary>
        /// <remarks>A label literal has a set of string parameters. It takes no arguments.</remarks>
        public bool IsLabelLit { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_LABEL_LIT; } }
        #endregion

        #region Proof Terms
        /// <summary>
        /// Indicates whether the term is a binary equivalence modulo namings.
        /// </summary>
        /// <remarks>This binary predicate is used in proof terms.
        /// It captures equisatisfiability and equivalence modulo renamings.</remarks>
        public bool IsOEQ { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_OEQ; } }

        /// <summary>
        /// Indicates whether the term is a Proof for the expression 'true'.
        /// </summary>
        public bool IsProofTrue { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_TRUE; } }

        /// <summary>
        /// Indicates whether the term is a proof for a fact asserted by the user.
        /// </summary>
        public bool IsProofAsserted { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_ASSERTED; } }

        /// <summary>
        /// Indicates whether the term is a proof for a fact (tagged as goal) asserted by the user.
        /// </summary>
        public bool IsProofGoal { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_GOAL; } }

        /// <summary>
        /// Indicates whether the term is proof via modus ponens
        /// </summary>
        /// <remarks>
        /// Given a proof for p and a proof for (implies p q), produces a proof for q.
        /// T1: p
        /// T2: (implies p q)
        /// [mp T1 T2]: q
        /// The second antecedents may also be a proof for (iff p q).</remarks>
        public bool IsProofModusPonens { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_MODUS_PONENS; } }

        /// <summary>
        /// Indicates whether the term is a proof for (R t t), where R is a reflexive relation.
        /// </summary>
        /// <remarks>This proof object has no antecedents.
        /// The only reflexive relations that are used are
        /// equivalence modulo namings, equality and equivalence.
        /// That is, R is either '~', '=' or 'iff'.</remarks>
        public bool IsProofReflexivity { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_REFLEXIVITY; } }

        /// <summary>
        /// Indicates whether the term is proof by symmetricity of a relation
        /// </summary>
        /// <remarks>
        /// Given an symmetric relation R and a proof for (R t s), produces a proof for (R s t).
        /// T1: (R t s)
        /// [symmetry T1]: (R s t)
        /// T1 is the antecedent of this proof object.
        /// </remarks>
        public bool IsProofSymmetry { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_SYMMETRY; } }

        /// <summary>
        /// Indicates whether the term is a proof by transitivity of a relation
        /// </summary>
        /// <remarks>
        /// Given a transitive relation R, and proofs for (R t s) and (R s u), produces a proof
        /// for (R t u).
        /// T1: (R t s)
        /// T2: (R s u)
        /// [trans T1 T2]: (R t u)
        /// </remarks>
        public bool IsProofTransitivity { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_TRANSITIVITY; } }

        /// <summary>
        /// Indicates whether the term is a proof by condensed transitivity of a relation
        /// </summary>
        /// <remarks>
        /// Condensed transitivity proof. This proof object is only used if the parameter PROOF_MODE is 1.
        /// It combines several symmetry and transitivity proofs.
        /// Example:
        /// T1: (R a b)
        /// T2: (R c b)
        /// T3: (R c d)
        /// [trans* T1 T2 T3]: (R a d)
        /// R must be a symmetric and transitive relation.
        ///
        /// Assuming that this proof object is a proof for (R s t), then
        /// a proof checker must check if it is possible to prove (R s t)
        /// using the antecedents, symmetry and transitivity.  That is,
        /// if there is a path from s to t, if we view every
        /// antecedent (R a b) as an edge between a and b.
        /// </remarks>
        public bool IsProofTransitivityStar { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_TRANSITIVITY_STAR; } }


        /// <summary>
        /// Indicates whether the term is a monotonicity proof object.
        /// </summary>
        /// <remarks>
        /// T1: (R t_1 s_1)
        /// ...
        /// Tn: (R t_n s_n)
        /// [monotonicity T1 ... Tn]: (R (f t_1 ... t_n) (f s_1 ... s_n))
        /// Remark: if t_i == s_i, then the antecedent Ti is suppressed.
        /// That is, reflexivity proofs are supressed to save space.
        /// </remarks>
        public bool IsProofMonotonicity { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_MONOTONICITY; } }

        /// <summary>
        /// Indicates whether the term is a quant-intro proof
        /// </summary>
        /// <remarks>
        /// Given a proof for (~ p q), produces a proof for (~ (forall (x) p) (forall (x) q)).
        /// T1: (~ p q)
        /// [quant-intro T1]: (~ (forall (x) p) (forall (x) q))
        /// </remarks>
        public bool IsProofQuantIntro { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_QUANT_INTRO; } }

        /// <summary>
        /// Indicates whether the term is a distributivity proof object.
        /// </summary>
        /// <remarks>
        /// Given that f (= or) distributes over g (= and), produces a proof for
        /// (= (f a (g c d))
        /// (g (f a c) (f a d)))
        /// If f and g are associative, this proof also justifies the following equality:
        /// (= (f (g a b) (g c d))
        /// (g (f a c) (f a d) (f b c) (f b d)))
        /// where each f and g can have arbitrary number of arguments.
        ///
        /// This proof object has no antecedents.
        /// Remark. This rule is used by the CNF conversion pass and
        /// instantiated by f = or, and g = and.
        /// </remarks>
        public bool IsProofDistributivity { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_DISTRIBUTIVITY; } }

        /// <summary>
        /// Indicates whether the term is a proof by elimination of AND
        /// </summary>
        /// <remarks>
        /// Given a proof for (and l_1 ... l_n), produces a proof for l_i
        /// T1: (and l_1 ... l_n)
        /// [and-elim T1]: l_i
        /// </remarks>
        public bool IsProofAndElimination { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_AND_ELIM; } }

        /// <summary>
        /// Indicates whether the term is a proof by eliminiation of not-or
        /// </summary>
        /// <remarks>
        /// Given a proof for (not (or l_1 ... l_n)), produces a proof for (not l_i).
        /// T1: (not (or l_1 ... l_n))
        /// [not-or-elim T1]: (not l_i)
        /// </remarks>
        public bool IsProofOrElimination { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_NOT_OR_ELIM; } }

        /// <summary>
        /// Indicates whether the term is a proof by rewriting
        /// </summary>
        /// <remarks>
        /// A proof for a local rewriting step (= t s).
        /// The head function symbol of t is interpreted.
        ///
        /// This proof object has no antecedents.
        /// The conclusion of a rewrite rule is either an equality (= t s),
        /// an equivalence (iff t s), or equi-satisfiability (~ t s).
        /// Remark: if f is bool, then = is iff.
        ///
        /// Examples:
        /// (= (+ x 0) x)
        /// (= (+ x 1 2) (+ 3 x))
        /// (iff (or x false) x)
        /// </remarks>
        public bool IsProofRewrite { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_REWRITE; } }

        /// <summary>
        /// Indicates whether the term is a proof by rewriting
        /// </summary>
        /// <remarks>
        /// A proof for rewriting an expression t into an expression s.
        /// This proof object is used if the parameter PROOF_MODE is 1.
        /// This proof object can have n antecedents.
        /// The antecedents are proofs for equalities used as substitution rules.
        /// The object is also used in a few cases if the parameter PROOF_MODE is 2.
        /// The cases are:
        /// - When applying contextual simplification (CONTEXT_SIMPLIFIER=true)
        /// - When converting bit-vectors to Booleans (BIT2BOOL=true)
        /// - When pulling ite expression up (PULL_CHEAP_ITE_TREES=true)
        /// </remarks>
        public bool IsProofRewriteStar { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_REWRITE_STAR; } }

        /// <summary>
        /// Indicates whether the term is a proof for pulling quantifiers out.
        /// </summary>
        /// <remarks>
        /// A proof for (iff (f (forall (x) q(x)) r) (forall (x) (f (q x) r))). This proof object has no antecedents.
        /// </remarks>
        public bool IsProofPullQuant { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_PULL_QUANT; } }

        /// <summary>
        /// Indicates whether the term is a proof for pulling quantifiers out.
        /// </summary>
        /// <remarks>
        /// A proof for (iff P Q) where Q is in prenex normal form.
        /// This proof object is only used if the parameter PROOF_MODE is 1.
        /// This proof object has no antecedents
        /// </remarks>
        public bool IsProofPullQuantStar { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_PULL_QUANT_STAR; } }

        /// <summary>
        /// Indicates whether the term is a proof for pushing quantifiers in.
        /// </summary>
        /// <remarks>
        /// A proof for:
        /// (iff (forall (x_1 ... x_m) (and p_1[x_1 ... x_m] ... p_n[x_1 ... x_m]))
        ///         (and (forall (x_1 ... x_m) p_1[x_1 ... x_m])
        ///          ...
        ///      (forall (x_1 ... x_m) p_n[x_1 ... x_m])))
        ///  This proof object has no antecedents
        /// </remarks>
        public bool IsProofPushQuant { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_PUSH_QUANT; } }

        /// <summary>
        /// Indicates whether the term is a proof for elimination of unused variables.
        /// </summary>
        /// <remarks>
        /// A proof for (iff (forall (x_1 ... x_n y_1 ... y_m) p[x_1 ... x_n])
        ///                  (forall (x_1 ... x_n) p[x_1 ... x_n]))
        ///
        /// It is used to justify the elimination of unused variables.
        /// This proof object has no antecedents.
        /// </remarks>
        public bool IsProofElimUnusedVars { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_ELIM_UNUSED_VARS; } }

        /// <summary>
        /// Indicates whether the term is a proof for destructive equality resolution
        /// </summary>
        /// <remarks>
        /// A proof for destructive equality resolution:
        /// (iff (forall (x) (or (not (= x t)) P[x])) P[t])
        /// if x does not occur in t.
        ///
        /// This proof object has no antecedents.
        ///
        /// Several variables can be eliminated simultaneously.
        /// </remarks>
        public bool IsProofDER { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_DER; } }

        /// <summary>
        /// Indicates whether the term is a proof for quantifier instantiation
        /// </summary>
        /// <remarks>
        /// A proof of (or (not (forall (x) (P x))) (P a))
        /// </remarks>
        public bool IsProofQuantInst { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_QUANT_INST; } }

        /// <summary>
        /// Indicates whether the term is a hypthesis marker.
        /// </summary>
        /// <remarks>Mark a hypothesis in a natural deduction style proof.</remarks>
        public bool IsProofHypothesis { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_HYPOTHESIS; } }

        /// <summary>
        /// Indicates whether the term is a proof by lemma
        /// </summary>
        /// <remarks>
        /// T1: false
        /// [lemma T1]: (or (not l_1) ... (not l_n))
        ///
        /// This proof object has one antecedent: a hypothetical proof for false.
        /// It converts the proof in a proof for (or (not l_1) ... (not l_n)),
        /// when T1 contains the hypotheses: l_1, ..., l_n.
        /// </remarks>
        public bool IsProofLemma { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_LEMMA; } }

        /// <summary>
        /// Indicates whether the term is a proof by unit resolution
        /// </summary>
        /// <remarks>
        /// T1:      (or l_1 ... l_n l_1' ... l_m')
        /// T2:      (not l_1)
        /// ...
        /// T(n+1):  (not l_n)
        /// [unit-resolution T1 ... T(n+1)]: (or l_1' ... l_m')
        /// </remarks>
        public bool IsProofUnitResolution { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_UNIT_RESOLUTION; } }

        /// <summary>
        /// Indicates whether the term is a proof by iff-true
        /// </summary>
        /// <remarks>
        /// T1: p
        /// [iff-true T1]: (iff p true)
        /// </remarks>
        public bool IsProofIFFTrue { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_IFF_TRUE; } }

        /// <summary>
        /// Indicates whether the term is a proof by iff-false
        /// </summary>
        /// <remarks>
        /// T1: (not p)
        /// [iff-false T1]: (iff p false)
        /// </remarks>
        public bool IsProofIFFFalse { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_IFF_FALSE; } }

        /// <summary>
        /// Indicates whether the term is a proof by commutativity
        /// </summary>
        /// <remarks>
        /// [comm]: (= (f a b) (f b a))
        ///
        /// f is a commutative operator.
        ///
        /// This proof object has no antecedents.
        /// Remark: if f is bool, then = is iff.
        /// </remarks>
        public bool IsProofCommutativity { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_COMMUTATIVITY; } }

        /// <summary>
        /// Indicates whether the term is a proof for Tseitin-like axioms
        /// </summary>
        /// <remarks>
        /// Proof object used to justify Tseitin's like axioms:
        ///
        /// (or (not (and p q)) p)
        /// (or (not (and p q)) q)
        /// (or (not (and p q r)) p)
        /// (or (not (and p q r)) q)
        /// (or (not (and p q r)) r)
        /// ...
        /// (or (and p q) (not p) (not q))
        /// (or (not (or p q)) p q)
        /// (or (or p q) (not p))
        /// (or (or p q) (not q))
        /// (or (not (iff p q)) (not p) q)
        /// (or (not (iff p q)) p (not q))
        /// (or (iff p q) (not p) (not q))
        /// (or (iff p q) p q)
        /// (or (not (ite a b c)) (not a) b)
        /// (or (not (ite a b c)) a c)
        /// (or (ite a b c) (not a) (not b))
        /// (or (ite a b c) a (not c))
        /// (or (not (not a)) (not a))
        /// (or (not a) a)
        ///
        /// This proof object has no antecedents.
        /// Note: all axioms are propositional tautologies.
        /// Note also that 'and' and 'or' can take multiple arguments.
        /// You can recover the propositional tautologies by
        /// unfolding the Boolean connectives in the axioms a small
        /// bounded number of steps (=3).
        /// </remarks>
        public bool IsProofDefAxiom { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_DEF_AXIOM; } }

        /// <summary>
        /// Indicates whether the term is a proof for introduction of a name
        /// </summary>
        /// <remarks>
        /// Introduces a name for a formula/term.
        /// Suppose e is an expression with free variables x, and def-intro
        /// introduces the name n(x). The possible cases are:
        ///
        /// When e is of Boolean type:
        /// [def-intro]: (and (or n (not e)) (or (not n) e))
        ///
        /// or:
        /// [def-intro]: (or (not n) e)
        /// when e only occurs positively.
        ///
        /// When e is of the form (ite cond th el):
        /// [def-intro]: (and (or (not cond) (= n th)) (or cond (= n el)))
        ///
        /// Otherwise:
        /// [def-intro]: (= n e)
        /// </remarks>
        public bool IsProofDefIntro { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_DEF_INTRO; } }

        /// <summary>
        /// Indicates whether the term is a proof for application of a definition
        /// </summary>
        /// <remarks>
        ///  [apply-def T1]: F ~ n
        ///  F is 'equivalent' to n, given that T1 is a proof that
        ///  n is a name for F.
        /// </remarks>
        public bool IsProofApplyDef { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_APPLY_DEF; } }

        /// <summary>
        /// Indicates whether the term is a proof iff-oeq
        /// </summary>
        /// <remarks>
        /// T1: (iff p q)
        /// [iff~ T1]: (~ p q)
        /// </remarks>
        public bool IsProofIFFOEQ { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_IFF_OEQ; } }

        /// <summary>
        /// Indicates whether the term is a proof for a positive NNF step
        /// </summary>
        /// <remarks>
        /// Proof for a (positive) NNF step. Example:
        ///
        /// T1: (not s_1) ~ r_1
        /// T2: (not s_2) ~ r_2
        /// T3: s_1 ~ r_1'
        /// T4: s_2 ~ r_2'
        /// [nnf-pos T1 T2 T3 T4]: (~ (iff s_1 s_2)
        ///                           (and (or r_1 r_2') (or r_1' r_2)))
        ///
        /// The negation normal form steps NNF_POS and NNF_NEG are used in the following cases:
        /// (a) When creating the NNF of a positive force quantifier.
        /// The quantifier is retained (unless the bound variables are eliminated).
        /// Example
        ///    T1: q ~ q_new
        ///    [nnf-pos T1]: (~ (forall (x T) q) (forall (x T) q_new))
        ///
        /// (b) When recursively creating NNF over Boolean formulas, where the top-level
        /// connective is changed during NNF conversion. The relevant Boolean connectives
        /// for NNF_POS are 'implies', 'iff', 'xor', 'ite'.
        /// NNF_NEG furthermore handles the case where negation is pushed
        /// over Boolean connectives 'and' and 'or'.
        /// </remarks>
        public bool IsProofNNFPos { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_NNF_POS; } }

        /// <summary>
        /// Indicates whether the term is a proof for a negative NNF step
        /// </summary>
        /// <remarks>
        /// Proof for a (negative) NNF step. Examples:
        ///
        ///   T1: (not s_1) ~ r_1
        ///   ...
        ///   Tn: (not s_n) ~ r_n
        ///   [nnf-neg T1 ... Tn]: (not (and s_1 ... s_n)) ~ (or r_1 ... r_n)
        /// and
        ///   T1: (not s_1) ~ r_1
        ///   ...
        ///   Tn: (not s_n) ~ r_n
        ///   [nnf-neg T1 ... Tn]: (not (or s_1 ... s_n)) ~ (and r_1 ... r_n)
        /// and
        ///   T1: (not s_1) ~ r_1
        ///   T2: (not s_2) ~ r_2
        ///   T3: s_1 ~ r_1'
        ///   T4: s_2 ~ r_2'
        ///   [nnf-neg T1 T2 T3 T4]: (~ (not (iff s_1 s_2))
        ///                             (and (or r_1 r_2) (or r_1' r_2')))
        /// </remarks>
        public bool IsProofNNFNeg { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_NNF_NEG; } }

        /// <summary>
        /// Indicates whether the term is a proof for (~ P Q) here Q is in negation normal form.
        /// </summary>
        /// <remarks>
        /// A proof for (~ P Q) where Q is in negation normal form.
        ///
        /// This proof object is only used if the parameter PROOF_MODE is 1.
        ///
        /// This proof object may have n antecedents. Each antecedent is a PR_DEF_INTRO.
        /// </remarks>
        public bool IsProofNNFStar { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_NNF_STAR; } }

        /// <summary>
        /// Indicates whether the term is a proof for (~ P Q) where Q is in conjunctive normal form.
        /// </summary>
        /// <remarks>
        /// A proof for (~ P Q) where Q is in conjunctive normal form.
        /// This proof object is only used if the parameter PROOF_MODE is 1.
        /// This proof object may have n antecedents. Each antecedent is a PR_DEF_INTRO.
        /// </remarks>
        public bool IsProofCNFStar { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_CNF_STAR; } }

        /// <summary>
        /// Indicates whether the term is a proof for a Skolemization step
        /// </summary>
        /// <remarks>
        /// Proof for:
        ///
        ///   [sk]: (~ (not (forall x (p x y))) (not (p (sk y) y)))
        ///   [sk]: (~ (exists x (p x y)) (p (sk y) y))
        ///
        /// This proof object has no antecedents.
        /// </remarks>
        public bool IsProofSkolemize { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_SKOLEMIZE; } }

        /// <summary>
        /// Indicates whether the term is a proof by modus ponens for equi-satisfiability.
        /// </summary>
        /// <remarks>
        /// Modus ponens style rule for equi-satisfiability.
        /// T1: p
        /// T2: (~ p q)
        /// [mp~ T1 T2]: q
        /// </remarks>
        public bool IsProofModusPonensOEQ { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_MODUS_PONENS_OEQ; } }

        /// <summary>
        /// Indicates whether the term is a proof for theory lemma
        /// </summary>
        /// <remarks>
        /// Generic proof for theory lemmas.
        ///
        /// The theory lemma function comes with one or more parameters.
        /// The first parameter indicates the name of the theory.
        /// For the theory of arithmetic, additional parameters provide hints for
        /// checking the theory lemma.
        /// The hints for arithmetic are:
        /// - farkas - followed by rational coefficients. Multiply the coefficients to the
        ///   inequalities in the lemma, add the (negated) inequalities and obtain a contradiction.
        /// - triangle-eq - Indicates a lemma related to the equivalence:
        ///   (iff (= t1 t2) (and (&lt;= t1 t2) (&lt;= t2 t1)))
        /// - gcd-test - Indicates an integer linear arithmetic lemma that uses a gcd test.
        /// </remarks>
        public bool IsProofTheoryLemma { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_PR_TH_LEMMA; } }
        #endregion

        #region Relational Terms
        /// <summary>
        /// Indicates whether the term is of relation sort.
        /// </summary>
        public bool IsRelation
        {
            get
            {
                return (Native.Z3_is_app(Context.nCtx, NativeObject) != 0 &&
                        Native.Z3_get_sort_kind(Context.nCtx, Native.Z3_get_sort(Context.nCtx, NativeObject))
                        == (uint)Z3_sort_kind.Z3_RELATION_SORT);
            }
        }

        /// <summary>
        /// Indicates whether the term is an relation store
        /// </summary>
        /// <remarks>
        /// Insert a record into a relation.
        /// The function takes <c>n+1</c> arguments, where the first argument is the relation and the remaining <c>n</c> elements
        /// correspond to the <c>n</c> columns of the relation.
        /// </remarks>
        public bool IsRelationStore { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_RA_STORE; } }

        /// <summary>
        /// Indicates whether the term is an empty relation
        /// </summary>
        public bool IsEmptyRelation { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_RA_EMPTY; } }

        /// <summary>
        /// Indicates whether the term is a test for the emptiness of a relation
        /// </summary>
        public bool IsIsEmptyRelation { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_RA_IS_EMPTY; } }

        /// <summary>
        /// Indicates whether the term is a relational join
        /// </summary>
        public bool IsRelationalJoin { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_RA_JOIN; } }

        /// <summary>
        /// Indicates whether the term is the union or convex hull of two relations.
        /// </summary>
        /// <remarks>The function takes two arguments.</remarks>
        public bool IsRelationUnion { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_RA_UNION; } }

        /// <summary>
        /// Indicates whether the term is the widening of two relations
        /// </summary>
        /// <remarks>The function takes two arguments.</remarks>
        public bool IsRelationWiden { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_RA_WIDEN; } }

        /// <summary>
        /// Indicates whether the term is a projection of columns (provided as numbers in the parameters).
        /// </summary>
        /// <remarks>The function takes one argument.</remarks>
        public bool IsRelationProject { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_RA_PROJECT; } }

        /// <summary>
        /// Indicates whether the term is a relation filter
        /// </summary>
        /// <remarks>
        /// Filter (restrict) a relation with respect to a predicate.
        /// The first argument is a relation.
        /// The second argument is a predicate with free de-Brujin indices
        /// corresponding to the columns of the relation.
        /// So the first column in the relation has index 0.
        /// </remarks>
        public bool IsRelationFilter { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_RA_FILTER; } }

        /// <summary>
        /// Indicates whether the term is an intersection of a relation with the negation of another.
        /// </summary>
        /// <remarks>
        /// Intersect the first relation with respect to negation
        /// of the second relation (the function takes two arguments).
        /// Logically, the specification can be described by a function
        ///
        ///   target = filter_by_negation(pos, neg, columns)
        ///
        /// where columns are pairs c1, d1, .., cN, dN of columns from pos and neg, such that
        /// target are elements in x in pos, such that there is no y in neg that agrees with
        /// x on the columns c1, d1, .., cN, dN.
        /// </remarks>
        public bool IsRelationNegationFilter { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_RA_NEGATION_FILTER; } }

        /// <summary>
        /// Indicates whether the term is the renaming of a column in a relation
        /// </summary>
        /// <remarks>
        /// The function takes one argument.
        /// The parameters contain the renaming as a cycle.
        /// </remarks>
        public bool IsRelationRename { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_RA_RENAME; } }

        /// <summary>
        /// Indicates whether the term is the complement of a relation
        /// </summary>
        public bool IsRelationComplement { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_RA_COMPLEMENT; } }

        /// <summary>
        /// Indicates whether the term is a relational select
        /// </summary>
        /// <remarks>
        /// Check if a record is an element of the relation.
        /// The function takes <c>n+1</c> arguments, where the first argument is a relation,
        /// and the remaining <c>n</c> arguments correspond to a record.
        /// </remarks>
        public bool IsRelationSelect { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_RA_SELECT; } }

        /// <summary>
        /// Indicates whether the term is a relational clone (copy)
        /// </summary>
        /// <remarks>
        /// Create a fresh copy (clone) of a relation.
        /// The function is logically the identity, but
        /// in the context of a register machine allows
        /// for terms of kind <seealso cref="IsRelationUnion"/>
        /// to perform destructive updates to the first argument.
        /// </remarks>
        public bool IsRelationClone { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_RA_CLONE; } }
        #endregion

        #region Finite domain terms
        /// <summary>
        /// Indicates whether the term is of an array sort.
        /// </summary>
        public bool IsFiniteDomain
        {
            get
            {
                return (Native.Z3_is_app(Context.nCtx, NativeObject) != 0 &&
                        Native.Z3_get_sort_kind(Context.nCtx, Native.Z3_get_sort(Context.nCtx, NativeObject)) == (uint)Z3_sort_kind.Z3_FINITE_DOMAIN_SORT);
            }
        }

        /// <summary>
        /// Indicates whether the term is a less than predicate over a finite domain.
        /// </summary>
        public bool IsFiniteDomainLT { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FD_LT; } }
        #endregion

        #region Floating-point terms
        /// <summary>
        ///  Indicates whether the terms is of floating-point sort.
        /// </summary>
        public bool IsFP
        {
            get { return Native.Z3_get_sort_kind(Context.nCtx, Native.Z3_get_sort(Context.nCtx, NativeObject)) == (uint)Z3_sort_kind.Z3_FLOATING_POINT_SORT; }
        }

        /// <summary>
        ///  Indicates whether the terms is of floating-point rounding mode sort.
        /// </summary>
        public bool IsFPRM
        {
            get { return Native.Z3_get_sort_kind(Context.nCtx, Native.Z3_get_sort(Context.nCtx, NativeObject)) == (uint)Z3_sort_kind.Z3_ROUNDING_MODE_SORT; }
        }

        /// <summary>
        /// Indicates whether the term is a floating-point numeral
        /// </summary>
        public bool IsFPNumeral { get { return IsFP && IsNumeral; } }

        /// <summary>
        /// Indicates whether the term is a floating-point rounding mode numeral
        /// </summary>
        public bool IsFPRMNumeral { get { return IsFPRM && IsNumeral; } }

        /// <summary>
        /// Indicates whether the term is the floating-point rounding numeral roundNearestTiesToEven
        /// </summary>
        public bool IsFPRMRoundNearestTiesToEven{ get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN; } }

        /// <summary>
        /// Indicates whether the term is the floating-point rounding numeral roundNearestTiesToAway
        /// </summary>
        public bool IsFPRMRoundNearestTiesToAway{ get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY; } }

        /// <summary>
        /// Indicates whether the term is the floating-point rounding numeral roundTowardNegative
        /// </summary>
        public bool IsFPRMRoundTowardNegative{ get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_RM_TOWARD_NEGATIVE; } }

        /// <summary>
        /// Indicates whether the term is the floating-point rounding numeral roundTowardPositive
        /// </summary>
        public bool IsFPRMRoundTowardPositive{ get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_RM_TOWARD_POSITIVE; } }

        /// <summary>
        /// Indicates whether the term is the floating-point rounding numeral roundTowardZero
        /// </summary>
        public bool IsFPRMRoundTowardZero{ get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_RM_TOWARD_ZERO; } }

        /// <summary>
        /// Indicates whether the term is the floating-point rounding numeral roundNearestTiesToEven
        /// </summary>
        public bool IsFPRMExprRNE{ get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN; } }

        /// <summary>
        /// Indicates whether the term is the floating-point rounding numeral roundNearestTiesToAway
        /// </summary>
        public bool IsFPRMExprRNA { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY; } }

        /// <summary>
        /// Indicates whether the term is the floating-point rounding numeral roundTowardNegative
        /// </summary>
        public bool IsFPRMExprRTN { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_RM_TOWARD_NEGATIVE; } }

        /// <summary>
        /// Indicates whether the term is the floating-point rounding numeral roundTowardPositive
        /// </summary>
        public bool IsFPRMExprRTP { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_RM_TOWARD_POSITIVE; } }

        /// <summary>
        /// Indicates whether the term is the floating-point rounding numeral roundTowardZero
        /// </summary>
        public bool IsFPRMExprRTZ { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_RM_TOWARD_ZERO; } }

        /// <summary>
        /// Indicates whether the term is a floating-point rounding mode numeral
        /// </summary>
        public bool IsFPRMExpr {
            get {
                return IsApp &&
                       (FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY||
                       FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN ||
                       FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_RM_TOWARD_POSITIVE ||
                       FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_RM_TOWARD_NEGATIVE ||
                       FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_RM_TOWARD_ZERO);
            }
        }

        /// <summary>
        /// Indicates whether the term is a floating-point +oo
        /// </summary>
        public bool IsFPPlusInfinity{ get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_PLUS_INF; } }

        /// <summary>
        /// Indicates whether the term is a floating-point -oo
        /// </summary>
        public bool IsFPMinusInfinity{ get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_MINUS_INF; } }

        /// <summary>
        /// Indicates whether the term is a floating-point NaN
        /// </summary>
        public bool IsFPNaN { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_NAN; } }

                /// <summary>
        /// Indicates whether the term is a floating-point +zero
        /// </summary>
        public bool IsFPPlusZero { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_PLUS_ZERO; } }

        /// <summary>
        /// Indicates whether the term is a floating-point -zero
        /// </summary>
        public bool IsFPMinusZero { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_MINUS_ZERO; } }

        /// <summary>
        /// Indicates whether the term is a floating-point addition term
        /// </summary>
        public bool IsFPAdd { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_ADD; } }


        /// <summary>
        /// Indicates whether the term is a floating-point subtraction term
        /// </summary>
        public bool IsFPSub { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_SUB; } }

        /// <summary>
        /// Indicates whether the term is a floating-point negation term
        /// </summary>
        public bool IsFPNeg { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_NEG; } }

        /// <summary>
        /// Indicates whether the term is a floating-point multiplication term
        /// </summary>
        public bool IsFPMul { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_MUL; } }

        /// <summary>
        /// Indicates whether the term is a floating-point divison term
        /// </summary>
        public bool IsFPDiv { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_DIV; } }

        /// <summary>
        /// Indicates whether the term is a floating-point remainder term
        /// </summary>
        public bool IsFPRem { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_REM; } }

        /// <summary>
        /// Indicates whether the term is a floating-point term absolute value term
        /// </summary>
        public bool IsFPAbs { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_ABS; } }

        /// <summary>
        /// Indicates whether the term is a floating-point minimum term
        /// </summary>
        public bool IsFPMin { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_MIN; } }

        /// <summary>
        /// Indicates whether the term is a floating-point maximum term
        /// </summary>
        public bool IsFPMax { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_MAX; } }

        /// <summary>
        /// Indicates whether the term is a floating-point fused multiply-add term
        /// </summary>
        public bool IsFPFMA { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_FMA; } }

        /// <summary>
        /// Indicates whether the term is a floating-point square root term
        /// </summary>
        public bool IsFPSqrt { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_SQRT; } }

        /// <summary>
        /// Indicates whether the term is a floating-point roundToIntegral term
        /// </summary>
        public bool IsFPRoundToIntegral { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_ROUND_TO_INTEGRAL; } }

        /// <summary>
        /// Indicates whether the term is a floating-point equality term
        /// </summary>
        public bool IsFPEq { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_EQ; } }

        /// <summary>
        /// Indicates whether the term is a floating-point less-than term
        /// </summary>
        public bool IsFPLt { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_LT; } }

        /// <summary>
        /// Indicates whether the term is a floating-point greater-than term
        /// </summary>
        public bool IsFPGt { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_GT; } }

        /// <summary>
        /// Indicates whether the term is a floating-point less-than or equal term
        /// </summary>
        public bool IsFPLe { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_LE; } }

        /// <summary>
        /// Indicates whether the term is a floating-point greater-than or erqual term
        /// </summary>
        public bool IsFPGe { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_GE; } }

        /// <summary>
        /// Indicates whether the term is a floating-point isNaN predicate term
        /// </summary>
        public bool IsFPisNaN { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_IS_NAN; } }

        /// <summary>
        /// Indicates whether the term is a floating-point isInf predicate term
        /// </summary>
        public bool IsFPisInf { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_IS_INF; } }

        /// <summary>
        /// Indicates whether the term is a floating-point isZero predicate term
        /// </summary>
        public bool IsFPisZero { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_IS_ZERO; } }

        /// <summary>
        /// Indicates whether the term is a floating-point isNormal term
        /// </summary>
        public bool IsFPisNormal { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_IS_NORMAL; } }

        /// <summary>
        /// Indicates whether the term is a floating-point isSubnormal predicate term
        /// </summary>
        public bool IsFPisSubnormal { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_IS_SUBNORMAL; } }

        /// <summary>
        /// Indicates whether the term is a floating-point isNegative predicate term
        /// </summary>
        public bool IsFPisNegative { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_IS_NEGATIVE; } }

        /// <summary>
        /// Indicates whether the term is a floating-point isPositive predicate term
        /// </summary>
        public bool IsFPisPositive { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_IS_POSITIVE; } }

        /// <summary>
        /// Indicates whether the term is a floating-point constructor term
        /// </summary>
        public bool IsFPFP { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_FP; } }

        /// <summary>
        /// Indicates whether the term is a floating-point conversion term
        /// </summary>
        public bool IsFPToFp { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_TO_FP; } }

        /// <summary>
        /// Indicates whether the term is a floating-point conversion from unsigned bit-vector term
        /// </summary>
        public bool IsFPToFpUnsigned { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_TO_FP_UNSIGNED; } }

        /// <summary>
        /// Indicates whether the term is a floating-point conversion to unsigned bit-vector term
        /// </summary>
        public bool IsFPToUBV { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_TO_UBV; } }

        /// <summary>
        /// Indicates whether the term is a floating-point conversion to signed bit-vector term
        /// </summary>
        public bool IsFPToSBV { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_TO_SBV; } }

        /// <summary>
        /// Indicates whether the term is a floating-point conversion to real term
        /// </summary>
        public bool IsFPToReal { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_TO_REAL; } }


        /// <summary>
        /// Indicates whether the term is a floating-point conversion to IEEE-754 bit-vector term
        /// </summary>
        public bool IsFPToIEEEBV { get { return IsApp && FuncDecl.DeclKind == Z3_decl_kind.Z3_OP_FPA_TO_IEEE_BV; } }

        #endregion
        #endregion

        #region Bound Variables
        /// <summary>
        /// The de-Burijn index of a bound variable.
        /// </summary>
        /// <remarks>
        /// Bound variables are indexed by de-Bruijn indices. It is perhaps easiest to explain
        /// the meaning of de-Bruijn indices by indicating the compilation process from
        /// non-de-Bruijn formulas to de-Bruijn format.
        /// <code>
        /// abs(forall (x1) phi) = forall (x1) abs1(phi, x1, 0)
        /// abs(forall (x1, x2) phi) = abs(forall (x1) abs(forall (x2) phi))
        /// abs1(x, x, n) = b_n
        /// abs1(y, x, n) = y
        /// abs1(f(t1,...,tn), x, n) = f(abs1(t1,x,n), ..., abs1(tn,x,n))
        /// abs1(forall (x1) phi, x, n) = forall (x1) (abs1(phi, x, n+1))
        /// </code>
        /// The last line is significant: the index of a bound variable is different depending
        /// on the scope in which it appears. The deeper x appears, the higher is its
        /// index.
        /// </remarks>
        public uint Index
        {
            get
            {
                if (!IsVar)
                    throw new Z3Exception("Term is not a bound variable.");

                Contract.EndContractBlock();

                return Native.Z3_get_index_value(Context.nCtx, NativeObject);
            }
        }
        #endregion

        #region Internal
        /// <summary>
        /// Constructor for Expr
        /// </summary>
        internal protected Expr(Context ctx, IntPtr obj) : base(ctx, obj) { Contract.Requires(ctx != null); }

#if DEBUG
        [Pure]
        internal override void CheckNativeObject(IntPtr obj)
        {
            if (Native.Z3_is_app(Context.nCtx, obj) == 0 &&
                Native.Z3_get_ast_kind(Context.nCtx, obj) != (uint)Z3_ast_kind.Z3_VAR_AST &&
                Native.Z3_get_ast_kind(Context.nCtx, obj) != (uint)Z3_ast_kind.Z3_QUANTIFIER_AST)
                throw new Z3Exception("Underlying object is not a term");
            base.CheckNativeObject(obj);
        }
#endif

        [Pure]
        internal static Expr Create(Context ctx, FuncDecl f, params Expr[] arguments)
        {
            Contract.Requires(ctx != null);
            Contract.Requires(f != null);
            Contract.Ensures(Contract.Result<Expr>() != null);

            IntPtr obj = Native.Z3_mk_app(ctx.nCtx, f.NativeObject,
                                          AST.ArrayLength(arguments),
                                          AST.ArrayToNative(arguments));
            return Create(ctx, obj);
        }

        [Pure]
        new internal static Expr Create(Context ctx, IntPtr obj)
        {
            Contract.Requires(ctx != null);
            Contract.Ensures(Contract.Result<Expr>() != null);

            Z3_ast_kind k = (Z3_ast_kind)Native.Z3_get_ast_kind(ctx.nCtx, obj);
            if (k == Z3_ast_kind.Z3_QUANTIFIER_AST)
                return new Quantifier(ctx, obj);
            IntPtr s = Native.Z3_get_sort(ctx.nCtx, obj);
            Z3_sort_kind sk = (Z3_sort_kind)Native.Z3_get_sort_kind(ctx.nCtx, s);

            if (Native.Z3_is_algebraic_number(ctx.nCtx, obj) != 0) // is this a numeral ast?
                return new AlgebraicNum(ctx, obj);

            if (Native.Z3_is_numeral_ast(ctx.nCtx, obj) != 0)
            {
                switch (sk)
                {
                    case Z3_sort_kind.Z3_INT_SORT: return new IntNum(ctx, obj);
                    case Z3_sort_kind.Z3_REAL_SORT: return new RatNum(ctx, obj);
                    case Z3_sort_kind.Z3_BV_SORT: return new BitVecNum(ctx, obj);
                    case Z3_sort_kind.Z3_FLOATING_POINT_SORT: return new FPNum(ctx, obj);
                    case Z3_sort_kind.Z3_ROUNDING_MODE_SORT: return new FPRMNum(ctx, obj);
                    case Z3_sort_kind.Z3_FINITE_DOMAIN_SORT: return new FiniteDomainNum(ctx, obj);
                }
            }

            switch (sk)
            {
                case Z3_sort_kind.Z3_BOOL_SORT: return new BoolExpr(ctx, obj);
                case Z3_sort_kind.Z3_INT_SORT: return new IntExpr(ctx, obj);
                case Z3_sort_kind.Z3_REAL_SORT: return new RealExpr(ctx, obj);
                case Z3_sort_kind.Z3_BV_SORT: return new BitVecExpr(ctx, obj);
                case Z3_sort_kind.Z3_ARRAY_SORT: return new ArrayExpr(ctx, obj);
                case Z3_sort_kind.Z3_DATATYPE_SORT: return new DatatypeExpr(ctx, obj);
                case Z3_sort_kind.Z3_FLOATING_POINT_SORT: return new FPExpr(ctx, obj);
                case Z3_sort_kind.Z3_ROUNDING_MODE_SORT: return new FPRMExpr(ctx, obj);
                case Z3_sort_kind.Z3_FINITE_DOMAIN_SORT: return new FiniteDomainExpr(ctx, obj);
                case Z3_sort_kind.Z3_RE_SORT: return new ReExpr(ctx, obj);
                case Z3_sort_kind.Z3_SEQ_SORT: return new SeqExpr(ctx, obj);
            }

            return new Expr(ctx, obj);
        }
        #endregion
    }
}
