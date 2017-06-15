/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    AST.cs

Abstract:

    Z3 Managed API: ASTs

Author:

    Christoph Wintersteiger (cwinter) 2012-03-16

Notes:

--*/

using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// The abstract syntax tree (AST) class.
    /// </summary>
    [ContractVerification(true)]
    public class AST : Z3Object, IComparable
    {
        /// <summary>
        /// Comparison operator.
        /// </summary>
        /// <param name="a">An AST</param>
        /// <param name="b">An AST</param>
        /// <returns>True if <paramref name="a"/> and <paramref name="b"/> are from the same context
        /// and represent the same sort; false otherwise.</returns>
        public static bool operator ==(AST a, AST b)
        {
            return Object.ReferenceEquals(a, b) ||
                   (!Object.ReferenceEquals(a, null) &&
                    !Object.ReferenceEquals(b, null) &&
                    a.Context.nCtx == b.Context.nCtx &&
                    Native.Z3_is_eq_ast(a.Context.nCtx, a.NativeObject, b.NativeObject) != 0);
        }

        /// <summary>
        /// Comparison operator.
        /// </summary>
        /// <param name="a">An AST</param>
        /// <param name="b">An AST</param>
        /// <returns>True if <paramref name="a"/> and <paramref name="b"/> are not from the same context
        /// or represent different sorts; false otherwise.</returns>
        public static bool operator !=(AST a, AST b)
        {
            return !(a == b);
        }

        /// <summary>
        /// Object comparison.
        /// </summary>
        public override bool Equals(object o)
        {
            AST casted = o as AST;
            if (casted == null) return false;
            return this == casted;
        }

        /// <summary>
        /// Object Comparison.
        /// </summary>
        /// <param name="other">Another AST</param>
        /// <returns>Negative if the object should be sorted before <paramref name="other"/>, positive if after else zero.</returns>
        public virtual int CompareTo(object other)
        {
            if (other == null) return 1;
            AST oAST = other as AST;
            if (oAST == null)
                return 1;
            else
            {
                if (Id < oAST.Id)
                    return -1;
                else if (Id > oAST.Id)
                    return +1;
                else
                    return 0;
            }
        }

        /// <summary>
        /// The AST's hash code.
        /// </summary>
        /// <returns>A hash code</returns>
        public override int GetHashCode()
        {
            return (int)Native.Z3_get_ast_hash(Context.nCtx, NativeObject);
        }

        /// <summary>
        /// A unique identifier for the AST (unique among all ASTs).
        /// </summary>
        public uint Id
        {
            get { return Native.Z3_get_ast_id(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// Translates (copies) the AST to the Context <paramref name="ctx"/>.
        /// </summary>
        /// <param name="ctx">A context</param>
        /// <returns>A copy of the AST which is associated with <paramref name="ctx"/></returns>
        public AST Translate(Context ctx)
        {
            Contract.Requires(ctx != null);
            Contract.Ensures(Contract.Result<AST>() != null);

            if (ReferenceEquals(Context, ctx))
                return this;
            else
                return Create(ctx, Native.Z3_translate(Context.nCtx, NativeObject, ctx.nCtx));
        }

        /// <summary>
        /// The kind of the AST.
        /// </summary>
        public Z3_ast_kind ASTKind
        {
            get { return (Z3_ast_kind)Native.Z3_get_ast_kind(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// Indicates whether the AST is an Expr
        /// </summary>
        public bool IsExpr
        {
            get
            {
                switch (ASTKind)
                {
                    case Z3_ast_kind.Z3_APP_AST:
                    case Z3_ast_kind.Z3_NUMERAL_AST:
                    case Z3_ast_kind.Z3_QUANTIFIER_AST:
                    case Z3_ast_kind.Z3_VAR_AST: return true;
                    default: return false;
                }
            }
        }

        /// <summary>
        /// Indicates whether the AST is an application
        /// </summary>
        public bool IsApp
        {
            get { return this.ASTKind == Z3_ast_kind.Z3_APP_AST; }
        }

        /// <summary>
        /// Indicates whether the AST is a BoundVariable
        /// </summary>
        public bool IsVar
        {
            get { return this.ASTKind == Z3_ast_kind.Z3_VAR_AST; }
        }

        /// <summary>
        /// Indicates whether the AST is a Quantifier
        /// </summary>
        public bool IsQuantifier
        {
            get { return this.ASTKind == Z3_ast_kind.Z3_QUANTIFIER_AST; }
        }

        /// <summary>
        /// Indicates whether the AST is a Sort
        /// </summary>
        public bool IsSort
        {
            get { return this.ASTKind == Z3_ast_kind.Z3_SORT_AST; }
        }

        /// <summary>
        /// Indicates whether the AST is a FunctionDeclaration
        /// </summary>
        public bool IsFuncDecl
        {
            get { return this.ASTKind == Z3_ast_kind.Z3_FUNC_DECL_AST; }
        }

        /// <summary>
        /// A string representation of the AST.
        /// </summary>
        public override string ToString()
        {
            return Native.Z3_ast_to_string(Context.nCtx, NativeObject);
        }

        /// <summary>
        /// A string representation of the AST in s-expression notation.
        /// </summary>
        public string SExpr()
        {
            Contract.Ensures(Contract.Result<string>() != null);

            return Native.Z3_ast_to_string(Context.nCtx, NativeObject);
        }

        #region Internal
        internal AST(Context ctx) : base(ctx) { Contract.Requires(ctx != null); }
        internal AST(Context ctx, IntPtr obj) : base(ctx, obj) { Contract.Requires(ctx != null); }

        internal class DecRefQueue : IDecRefQueue
        {
            public DecRefQueue() : base() { }
            public DecRefQueue(uint move_limit) : base(move_limit) { }
            internal override void IncRef(Context ctx, IntPtr obj)
            {
                Native.Z3_inc_ref(ctx.nCtx, obj);
            }

            internal override void DecRef(Context ctx, IntPtr obj)
            {
                Native.Z3_dec_ref(ctx.nCtx, obj);
            }
        };

        internal override void IncRef(IntPtr o)
        {
            // Console.WriteLine("AST IncRef()");
            if (Context == null || o == IntPtr.Zero)
                return;
            Context.AST_DRQ.IncAndClear(Context, o);
            base.IncRef(o);
        }

        internal override void DecRef(IntPtr o)
        {
            // Console.WriteLine("AST DecRef()");
            if (Context == null || o == IntPtr.Zero)
                return;
            Context.AST_DRQ.Add(o);
            base.DecRef(o);
        }

        internal static AST Create(Context ctx, IntPtr obj)
        {
            Contract.Requires(ctx != null);
            Contract.Ensures(Contract.Result<AST>() != null);

            switch ((Z3_ast_kind)Native.Z3_get_ast_kind(ctx.nCtx, obj))
            {
                case Z3_ast_kind.Z3_FUNC_DECL_AST: return new FuncDecl(ctx, obj);
                case Z3_ast_kind.Z3_QUANTIFIER_AST: return new Quantifier(ctx, obj);
                case Z3_ast_kind.Z3_SORT_AST: return Sort.Create(ctx, obj);
                case Z3_ast_kind.Z3_APP_AST:
                case Z3_ast_kind.Z3_NUMERAL_AST:
                case Z3_ast_kind.Z3_VAR_AST: return Expr.Create(ctx, obj);
                default:
                    throw new Z3Exception("Unknown AST kind");
            }
        }
        #endregion
    }
}
