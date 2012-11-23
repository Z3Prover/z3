/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    DatatypeSort.cs

Abstract:

    Z3 Managed API: Datatype Sorts

Author:

    Christoph Wintersteiger (cwinter) 2012-11-23

Notes:
    
--*/

using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// Datatype sorts.
    /// </summary>
    [ContractVerification(true)]
    public class DatatypeSort : Sort
    {
        /// <summary>
        /// The number of constructors of the datatype sort.
        /// </summary>
        public uint NumConstructors
        {
            get { return Native.Z3_get_datatype_sort_num_constructors(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// The constructors.
        /// </summary>
        public FuncDecl[] Constructors
        {
            get
            {
                Contract.Ensures(Contract.Result<FuncDecl[]>() != null);

                uint n = NumConstructors;
                FuncDecl[] res = new FuncDecl[n];
                for (uint i = 0; i < n; i++)
                    res[i] = new FuncDecl(Context, Native.Z3_get_datatype_sort_constructor(Context.nCtx, NativeObject, i));
                return res;
            }
        }

        /// <summary>
        /// The recognizers.
        /// </summary>
        public FuncDecl[] Recognizers
        {
            get
            {
                Contract.Ensures(Contract.Result<FuncDecl[]>() != null);

                uint n = NumConstructors;
                FuncDecl[] res = new FuncDecl[n];
                for (uint i = 0; i < n; i++)
                    res[i] = new FuncDecl(Context, Native.Z3_get_datatype_sort_recognizer(Context.nCtx, NativeObject, i));
                return res;
            }
        }

        /// <summary>
        /// The constructor accessors.
        /// </summary>
        public FuncDecl[][] Accessors
        {
            get
            {
                Contract.Ensures(Contract.Result<FuncDecl[][]>() != null);

                uint n = NumConstructors;
                FuncDecl[][] res = new FuncDecl[n][];
                for (uint i = 0; i < n; i++)
                {
                    FuncDecl fd = new FuncDecl(Context, Native.Z3_get_datatype_sort_constructor(Context.nCtx, NativeObject, i));
                    uint ds = fd.DomainSize;
                    FuncDecl[] tmp = new FuncDecl[ds];
                    for (uint j = 0; j < ds; j++)
                        tmp[j] = new FuncDecl(Context, Native.Z3_get_datatype_sort_constructor_accessor(Context.nCtx, NativeObject, i, j));
                    res[i] = tmp;
                }
                return res;
            }
        }

        #region Internal
        internal DatatypeSort(Context ctx, IntPtr obj) : base(ctx, obj) { Contract.Requires(ctx != null); }

        internal DatatypeSort(Context ctx, Symbol name, Constructor[] constructors)
            : base(ctx, Native.Z3_mk_datatype(ctx.nCtx, name.NativeObject, (uint)constructors.Length, ArrayToNative(constructors)))
        {
            Contract.Requires(ctx != null);
            Contract.Requires(name != null);
            Contract.Requires(constructors != null);
        }
        #endregion
    };
}
