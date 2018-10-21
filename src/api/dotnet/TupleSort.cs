/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    TupleSort.cs

Abstract:

    Z3 Managed API: Tuple Sorts

Author:

    Christoph Wintersteiger (cwinter) 2012-11-23

Notes:
    
--*/

using System;
using System.Diagnostics;

namespace Microsoft.Z3
{
    /// <summary>
    /// Tuple sorts.
    /// </summary>
    public class TupleSort : Sort
    {
        /// <summary>
        /// The constructor function of the tuple.
        /// </summary>
        public FuncDecl MkDecl
        {
            get
            {

                return new FuncDecl(Context, Native.Z3_get_tuple_sort_mk_decl(Context.nCtx, NativeObject));
            }
        }

        /// <summary>
        /// The number of fields in the tuple.
        /// </summary>
        public uint NumFields
        {
            get { return Native.Z3_get_tuple_sort_num_fields(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// The field declarations.
        /// </summary>
        public FuncDecl[] FieldDecls
        {
            get
            {

                uint n = NumFields;
                FuncDecl[] res = new FuncDecl[n];
                for (uint i = 0; i < n; i++)
                    res[i] = new FuncDecl(Context, Native.Z3_get_tuple_sort_field_decl(Context.nCtx, NativeObject, i));
                return res;
            }
        }

        #region Internal
        internal TupleSort(Context ctx, Symbol name, uint numFields, Symbol[] fieldNames, Sort[] fieldSorts)
            : base(ctx, IntPtr.Zero)
        {
            Debug.Assert(ctx != null);
            Debug.Assert(name != null);

            IntPtr t = IntPtr.Zero;
            IntPtr[] f = new IntPtr[numFields];
            NativeObject = Native.Z3_mk_tuple_sort(ctx.nCtx, name.NativeObject, numFields,
                                                   Symbol.ArrayToNative(fieldNames), AST.ArrayToNative(fieldSorts),
                                                   ref t, f);
        }
        #endregion
    };
}
