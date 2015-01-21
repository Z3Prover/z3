/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    ListSort.cs

Abstract:

    Z3 Managed API: List Sorts

Author:

    Christoph Wintersteiger (cwinter) 2012-11-23

Notes:
    
--*/

using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// List sorts.
    /// </summary>
    [ContractVerification(true)]
    public class ListSort : Sort
    {
        /// <summary>
        /// The declaration of the nil function of this list sort.
        /// </summary>
        public FuncDecl NilDecl
        {
            get
            {
                Contract.Ensures(Contract.Result<FuncDecl>() != null);
                return new FuncDecl(Context, Native.Z3_get_datatype_sort_constructor(Context.nCtx, NativeObject, 0));                                
            }
        }

        /// <summary>
        /// The empty list.
        /// </summary>
        public Expr Nil
        {
            get
            {
                Contract.Ensures(Contract.Result<Expr>() != null);
                return Context.MkApp(NilDecl);
            }
        }

        /// <summary>
        /// The declaration of the isNil function of this list sort.
        /// </summary>
        public FuncDecl IsNilDecl
        {
            get
            {
                Contract.Ensures(Contract.Result<FuncDecl>() != null);
                return new FuncDecl(Context, Native.Z3_get_datatype_sort_recognizer(Context.nCtx, NativeObject, 0));
            }
        }

        /// <summary>
        /// The declaration of the cons function of this list sort.
        /// </summary>
        public FuncDecl ConsDecl
        {
            get
            {
                Contract.Ensures(Contract.Result<FuncDecl>() != null);
                return new FuncDecl(Context, Native.Z3_get_datatype_sort_constructor(Context.nCtx, NativeObject, 1));
            }
        }

        /// <summary>
        /// The declaration of the isCons function of this list sort.
        /// </summary>
        /// 
        public FuncDecl IsConsDecl
        {
            get
            {
                Contract.Ensures(Contract.Result<FuncDecl>() != null);
                return new FuncDecl(Context, Native.Z3_get_datatype_sort_recognizer(Context.nCtx, NativeObject, 1));
            }
        }

        /// <summary>
        /// The declaration of the head function of this list sort.
        /// </summary>
        public FuncDecl HeadDecl
        {
            get
            {
                Contract.Ensures(Contract.Result<FuncDecl>() != null);
                return new FuncDecl(Context, Native.Z3_get_datatype_sort_constructor_accessor(Context.nCtx, NativeObject, 1, 0));
            }
        }

        /// <summary>
        /// The declaration of the tail function of this list sort.
        /// </summary>
        public FuncDecl TailDecl
        {
            get
            {
                Contract.Ensures(Contract.Result<FuncDecl>() != null);
                return new FuncDecl(Context, Native.Z3_get_datatype_sort_constructor_accessor(Context.nCtx, NativeObject, 1, 1));
            }
        }

        #region Internal
        internal ListSort(Context ctx, Symbol name, Sort elemSort)
            : base(ctx, IntPtr.Zero)
        {
            Contract.Requires(ctx != null);
            Contract.Requires(name != null);
            Contract.Requires(elemSort != null);

            IntPtr inil = IntPtr.Zero, iisnil = IntPtr.Zero, 
                   icons = IntPtr.Zero, iiscons = IntPtr.Zero,
                   ihead = IntPtr.Zero, itail = IntPtr.Zero;

            NativeObject = Native.Z3_mk_list_sort(ctx.nCtx, name.NativeObject, elemSort.NativeObject,
                                                  ref inil, ref iisnil, ref icons, ref iiscons, ref ihead, ref itail);            
        }
        #endregion
    };
}
