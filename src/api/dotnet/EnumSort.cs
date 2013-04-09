/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    EnumSort.cs

Abstract:

    Z3 Managed API: Enum Sorts

Author:

    Christoph Wintersteiger (cwinter) 2012-11-23

Notes:
    
--*/

using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// Enumeration sorts.
    /// </summary>
    [ContractVerification(true)]
    public class EnumSort : Sort
    {
        /// <summary>
        /// The function declarations of the constants in the enumeration.
        /// </summary>
        public FuncDecl[] ConstDecls
        {
            get
            {
                Contract.Ensures(Contract.Result<FuncDecl[]>() != null);
                uint n = Native.Z3_get_datatype_sort_num_constructors(Context.nCtx, NativeObject);
                FuncDecl[] t = new FuncDecl[n];
                for (uint i = 0; i < n; i++)
                    t[i] = new FuncDecl(Context, Native.Z3_get_datatype_sort_constructor(Context.nCtx, NativeObject, i));
                return t;                
            }
        }

        /// <summary>
        /// The constants in the enumeration.
        /// </summary>
        public Expr[] Consts
        {
            get
            {
                Contract.Ensures(Contract.Result<Expr[]>() != null);
                FuncDecl[] cds = ConstDecls;
                Expr[] t = new Expr[cds.Length];
                for (uint i = 0; i < t.Length; i++)
                    t[i] = Context.MkApp(cds[i]);
                return t;
            }
        }

        /// <summary>
        /// The test predicates for the constants in the enumeration.
        /// </summary>
        public FuncDecl[] TesterDecls
        {
            get
            {
                Contract.Ensures(Contract.Result<FuncDecl[]>() != null);
                uint n = Native.Z3_get_datatype_sort_num_constructors(Context.nCtx, NativeObject);
                FuncDecl[] t = new FuncDecl[n];
                for (uint i = 0; i < n; i++)
                    t[i] = new FuncDecl(Context, Native.Z3_get_datatype_sort_recognizer(Context.nCtx, NativeObject, i));
                return t;
            }
        }

        #region Internal
        internal EnumSort(Context ctx, Symbol name, Symbol[] enumNames)
            : base(ctx)
        {
            Contract.Requires(ctx != null);
            Contract.Requires(name != null);
            Contract.Requires(enumNames != null);

            int n = enumNames.Length;
            IntPtr[] n_constdecls = new IntPtr[n];
            IntPtr[] n_testers = new IntPtr[n];
            NativeObject = Native.Z3_mk_enumeration_sort(ctx.nCtx, name.NativeObject, (uint)n,
                                                         Symbol.ArrayToNative(enumNames), n_constdecls, n_testers);
        }
        #endregion
    };
}
