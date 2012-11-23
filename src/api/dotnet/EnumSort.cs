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

                return _constdecls;
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

                return _consts;
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

                return _testerdecls;
            }
        }

        #region Object Invariant

        [ContractInvariantMethod]
        private void ObjectInvariant()
        {
            Contract.Invariant(this._constdecls != null);
            Contract.Invariant(this._testerdecls != null);
            Contract.Invariant(this._consts != null);
        }


        #endregion

        #region Internal
        readonly private FuncDecl[] _constdecls = null, _testerdecls = null;
        readonly private Expr[] _consts = null;

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
            _constdecls = new FuncDecl[n];
            for (uint i = 0; i < n; i++)
                _constdecls[i] = new FuncDecl(ctx, n_constdecls[i]);
            _testerdecls = new FuncDecl[n];
            for (uint i = 0; i < n; i++)
                _testerdecls[i] = new FuncDecl(ctx, n_testers[i]);
            _consts = new Expr[n];
            for (uint i = 0; i < n; i++)
                _consts[i] = ctx.MkApp(_constdecls[i]);
        }
        #endregion
    };
}
