/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    FuncDecl.cs

Abstract:

    Z3 Managed API: Function Declarations

Author:

    Christoph Wintersteiger (cwinter) 2012-03-16

Notes:
    
--*/

using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// Function declarations. 
    /// </summary>
    [ContractVerification(true)]
    public class FuncDecl : AST
    {
        /// <summary>
        /// Comparison operator.
        /// </summary>
        /// <returns>True if <paramref name="a"/> and <paramref name="b"/> share the same context and are equal, false otherwise.</returns>
        public static bool operator ==(FuncDecl a, FuncDecl b)
        {
            return Object.ReferenceEquals(a, b) ||
                   (!Object.ReferenceEquals(a, null) &&
                    !Object.ReferenceEquals(b, null) &&
                    a.Context.nCtx == b.Context.nCtx &&
                    Native.Z3_is_eq_func_decl(a.Context.nCtx, a.NativeObject, b.NativeObject) != 0);
        }

        /// <summary>
        /// Comparison operator.
        /// </summary>
        /// <returns>True if <paramref name="a"/> and <paramref name="b"/> do not share the same context or are not equal, false otherwise.</returns>
        public static bool operator !=(FuncDecl a, FuncDecl b)
        {
            return !(a == b);
        }

        /// <summary>
        /// Object comparison.
        /// </summary>
        public override bool Equals(object o)
        {
            FuncDecl casted = o as FuncDecl;
            if (casted == null) return false;
            return this == casted;
        }

        /// <summary>
        /// A hash code.
        /// </summary>    
        public override int GetHashCode()
        {
            return base.GetHashCode();
        }

        /// <summary>
        /// A string representations of the function declaration.
        /// </summary>
        public override string ToString()
        {
            return Native.Z3_func_decl_to_string(Context.nCtx, NativeObject);
        }

        /// <summary>
        /// Returns a unique identifier for the function declaration.
        /// </summary>
        new public uint Id
        {
            get { return Native.Z3_get_func_decl_id(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// The arity of the function declaration
        /// </summary>
        public uint Arity
        {
            get { return Native.Z3_get_arity(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// The size of the domain of the function declaration
        /// <seealso cref="Arity"/>
        /// </summary>
        public uint DomainSize
        {
            get { return Native.Z3_get_domain_size(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// The domain of the function declaration
        /// </summary>
        public Sort[] Domain
        {
            get
            {
                Contract.Ensures(Contract.Result<Sort[]>() != null);

                uint n = DomainSize;

                Sort[] res = new Sort[n];
                for (uint i = 0; i < n; i++)
                    res[i] = Sort.Create(Context, Native.Z3_get_domain(Context.nCtx, NativeObject, i));
                return res;
            }
        }

        /// <summary>
        /// The range of the function declaration
        /// </summary>
        public Sort Range
        {
            get
            {
                Contract.Ensures(Contract.Result<Sort>() != null);
                return Sort.Create(Context, Native.Z3_get_range(Context.nCtx, NativeObject));
            }
        }

        /// <summary>
        /// The kind of the function declaration.
        /// </summary>
        public Z3_decl_kind DeclKind
        {
            get { return (Z3_decl_kind)Native.Z3_get_decl_kind(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// The name of the function declaration
        /// </summary>
        public Symbol Name
        {
            get
            {
                Contract.Ensures(Contract.Result<Symbol>() != null);
                return Symbol.Create(Context, Native.Z3_get_decl_name(Context.nCtx, NativeObject));
            }
        }

        /// <summary>
        /// The number of parameters of the function declaration
        /// </summary>
        public uint NumParameters
        {
            get { return Native.Z3_get_decl_num_parameters(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// The parameters of the function declaration
        /// </summary>
        public Parameter[] Parameters
        {
            get
            {
                Contract.Ensures(Contract.Result<Parameter[]>() != null);

                uint num = NumParameters;
                Parameter[] res = new Parameter[num];
                for (uint i = 0; i < num; i++)
                {
                    Z3_parameter_kind k = (Z3_parameter_kind)Native.Z3_get_decl_parameter_kind(Context.nCtx, NativeObject, i);
                    switch (k)
                    {
                        case Z3_parameter_kind.Z3_PARAMETER_INT:
                            res[i] = new Parameter(k, Native.Z3_get_decl_int_parameter(Context.nCtx, NativeObject, i));
                            break;
                        case Z3_parameter_kind.Z3_PARAMETER_DOUBLE:
                            res[i] = new Parameter(k, Native.Z3_get_decl_double_parameter(Context.nCtx, NativeObject, i));
                            break;
                        case Z3_parameter_kind.Z3_PARAMETER_SYMBOL:
                            res[i] = new Parameter(k, Symbol.Create(Context, Native.Z3_get_decl_symbol_parameter(Context.nCtx, NativeObject, i)));
                            break;
                        case Z3_parameter_kind.Z3_PARAMETER_SORT:
                            res[i] = new Parameter(k, Sort.Create(Context, Native.Z3_get_decl_sort_parameter(Context.nCtx, NativeObject, i)));
                            break;
                        case Z3_parameter_kind.Z3_PARAMETER_AST:
                            res[i] = new Parameter(k, new AST(Context, Native.Z3_get_decl_ast_parameter(Context.nCtx, NativeObject, i)));
                            break;
                        case Z3_parameter_kind.Z3_PARAMETER_FUNC_DECL:
                            res[i] = new Parameter(k, new FuncDecl(Context, Native.Z3_get_decl_func_decl_parameter(Context.nCtx, NativeObject, i)));
                            break;
                        case Z3_parameter_kind.Z3_PARAMETER_RATIONAL:
                            res[i] = new Parameter(k, Native.Z3_get_decl_rational_parameter(Context.nCtx, NativeObject, i));
                            break;
                        default:
                            throw new Z3Exception("Unknown function declaration parameter kind encountered");
                    }
                }
                return res;
            }
        }

        /// <summary>
        /// Function declarations can have Parameters associated with them. 
        /// </summary>
        public class Parameter
        {
            readonly private Z3_parameter_kind kind;
            readonly private int i;
            readonly private double d;
            readonly private Symbol sym;
            readonly private Sort srt;
            readonly private AST ast;
            readonly private FuncDecl fd;
            readonly private string r;

            /// <summary>The int value of the parameter.</summary>
            public int Int { get { if (ParameterKind != Z3_parameter_kind.Z3_PARAMETER_INT) throw new Z3Exception("parameter is not an int"); return i; } }
            /// <summary>The double value of the parameter.</summary>
            public double Double { get { if (ParameterKind != Z3_parameter_kind.Z3_PARAMETER_DOUBLE) throw new Z3Exception("parameter is not a double "); return d; } }
            /// <summary>The Symbol value of the parameter.</summary>
            public Symbol Symbol { get { if (ParameterKind != Z3_parameter_kind.Z3_PARAMETER_SYMBOL) throw new Z3Exception("parameter is not a Symbol"); return sym; } }
            /// <summary>The Sort value of the parameter.</summary>
            public Sort Sort { get { if (ParameterKind != Z3_parameter_kind.Z3_PARAMETER_SORT) throw new Z3Exception("parameter is not a Sort"); return srt; } }
            /// <summary>The AST value of the parameter.</summary>
            public AST AST { get { if (ParameterKind != Z3_parameter_kind.Z3_PARAMETER_AST) throw new Z3Exception("parameter is not an AST"); return ast; } }
            /// <summary>The FunctionDeclaration value of the parameter.</summary>
            public FuncDecl FuncDecl { get { if (ParameterKind != Z3_parameter_kind.Z3_PARAMETER_FUNC_DECL) throw new Z3Exception("parameter is not a function declaration"); return fd; } }
            /// <summary>The rational string value of the parameter.</summary>
            public string Rational { get { if (ParameterKind != Z3_parameter_kind.Z3_PARAMETER_RATIONAL) throw new Z3Exception("parameter is not a rational string"); return r; } }

            /// <summary>
            /// The kind of the parameter.
            /// </summary>
            public Z3_parameter_kind ParameterKind { get { return kind; } }

            #region Internal
            internal Parameter(Z3_parameter_kind k, int i)
            {
                this.kind = k;
                this.i = i;
            }

            internal Parameter(Z3_parameter_kind k, double d)
            {
                this.kind = k;
                this.d = d;
            }

            internal Parameter(Z3_parameter_kind k, Symbol s)
            {
                this.kind = k;
                this.sym = s;
            }

            internal Parameter(Z3_parameter_kind k, Sort s)
            {
                this.kind = k;
                this.srt = s;
            }

            internal Parameter(Z3_parameter_kind k, AST a)
            {
                this.kind = k;
                this.ast = a;
            }

            internal Parameter(Z3_parameter_kind k, FuncDecl fd)
            {
                this.kind = k;
                this.fd = fd;
            }

            internal Parameter(Z3_parameter_kind k, string r)
            {
                this.kind = k;
                this.r = r;
            }
            #endregion
        }

        #region Internal
        internal FuncDecl(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }

        internal FuncDecl(Context ctx, Symbol name, Sort[] domain, Sort range)
            : base(ctx, Native.Z3_mk_func_decl(ctx.nCtx, name.NativeObject, AST.ArrayLength(domain), AST.ArrayToNative(domain), range.NativeObject))
        {
            Contract.Requires(ctx != null);
            Contract.Requires(name != null);
            Contract.Requires(range != null);
        }

        internal FuncDecl(Context ctx, string prefix, Sort[] domain, Sort range)
            : base(ctx, Native.Z3_mk_fresh_func_decl(ctx.nCtx, prefix, AST.ArrayLength(domain), AST.ArrayToNative(domain), range.NativeObject))
        {
            Contract.Requires(ctx != null);
            Contract.Requires(range != null);
        }

#if DEBUG
        internal override void CheckNativeObject(IntPtr obj)
        {
            if (Native.Z3_get_ast_kind(Context.nCtx, obj) != (uint)Z3_ast_kind.Z3_FUNC_DECL_AST)
                throw new Z3Exception("Underlying object is not a function declaration");
            base.CheckNativeObject(obj);
        }
#endif
        #endregion

        /// <summary>
        /// Create expression that applies function to arguments.
        /// </summary>
        /// <param name="args"></param>
        /// <returns></returns>
        public Expr this[params Expr[] args]
        {
            get
            {
                Contract.Requires(args == null || Contract.ForAll(args, a => a != null));

                return Apply(args);
            }
        }

        /// <summary>
        /// Create expression that applies function to arguments.
        /// </summary>
        /// <param name="args"></param>
        /// <returns></returns>
        public Expr Apply(params Expr[] args)
        {
            Contract.Requires(args == null || Contract.ForAll(args, a => a != null));

            Context.CheckContextMatch<Expr>(args);
            return Expr.Create(Context, this, args);
        }

    }
}
