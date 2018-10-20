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

using System.Diagnostics;
using System;

namespace Microsoft.Z3
{
    /// <summary>
    /// Enumeration sorts.
    /// </summary>
    public class EnumSort : Sort
    {
        /// <summary>
        /// The function declarations of the constants in the enumeration.
        /// </summary>
        public FuncDecl[] ConstDecls
        {
            get
            {
                uint n = Native.Z3_get_datatype_sort_num_constructors(Context.nCtx, NativeObject);
                FuncDecl[] t = new FuncDecl[n];
                for (uint i = 0; i < n; i++)
                    t[i] = new FuncDecl(Context, Native.Z3_get_datatype_sort_constructor(Context.nCtx, NativeObject, i));
                return t;                
            }
        }

        /// <summary>
        /// Retrieves the inx'th constant declaration in the enumeration.
        /// </summary>
        /// <param name="inx"></param>
        /// <returns></returns>
        public FuncDecl ConstDecl(uint inx)
        {
            return new FuncDecl(Context, Native.Z3_get_datatype_sort_constructor(Context.nCtx, NativeObject, inx));
        }

        /// <summary>
        /// The constants in the enumeration.
        /// </summary>
        public Expr[] Consts
        {
            get
            {
                FuncDecl[] cds = ConstDecls;
                Expr[] t = new Expr[cds.Length];
                for (uint i = 0; i < t.Length; i++)
                    t[i] = Context.MkApp(cds[i]);
                return t;
            }
        }

        /// <summary>
        /// Retrieves the inx'th constant in the enumeration.
        /// </summary>
        /// <param name="inx"></param>
        /// <returns></returns>
        public Expr Const(uint inx)
        {
            return Context.MkApp(ConstDecl(inx));
        }

        /// <summary>
        /// The test predicates (recognizers) for the constants in the enumeration.
        /// </summary>
        public FuncDecl[] TesterDecls
        {
            get
            {
                uint n = Native.Z3_get_datatype_sort_num_constructors(Context.nCtx, NativeObject);
                FuncDecl[] t = new FuncDecl[n];
                for (uint i = 0; i < n; i++)
                    t[i] = new FuncDecl(Context, Native.Z3_get_datatype_sort_recognizer(Context.nCtx, NativeObject, i));
                return t;
            }
        }

        /// <summary>
        /// Retrieves the inx'th tester/recognizer declaration in the enumeration.
        /// </summary>
        /// <param name="inx"></param>
        /// <returns></returns>
        public FuncDecl TesterDecl(uint inx)
        {
            return new FuncDecl(Context, Native.Z3_get_datatype_sort_recognizer(Context.nCtx, NativeObject, inx));
        }

        #region Internal
        internal EnumSort(Context ctx, Symbol name, Symbol[] enumNames)
            : base(ctx, IntPtr.Zero)
        {
            Debug.Assert(ctx != null);
            Debug.Assert(name != null);
            Debug.Assert(enumNames != null);

            int n = enumNames.Length;
            IntPtr[] n_constdecls = new IntPtr[n];
            IntPtr[] n_testers = new IntPtr[n];
            NativeObject = Native.Z3_mk_enumeration_sort(ctx.nCtx, name.NativeObject, (uint)n,
                                                         Symbol.ArrayToNative(enumNames), n_constdecls, n_testers);
        }
        #endregion
    };
}
