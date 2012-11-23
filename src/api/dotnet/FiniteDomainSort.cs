/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    FiniteDomainSort.cs

Abstract:

    Z3 Managed API: Finite Domain Sorts

Author:

    Christoph Wintersteiger (cwinter) 2012-11-23

Notes:
    
--*/

using System;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// Finite domain sorts.
    /// </summary>
    [ContractVerification(true)]
    public class FiniteDomainSort : Sort
    {
        /// <summary>
        /// The size of the finite domain sort.
        /// </summary>
        public ulong Size
        {
            get
            {
                ulong res = 0;
                Native.Z3_get_finite_domain_sort_size(Context.nCtx, NativeObject, ref res);
                return res;
            }
        }

        #region Internal
        internal FiniteDomainSort(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }
        internal FiniteDomainSort(Context ctx, Symbol name, ulong size)
            : base(ctx, Native.Z3_mk_finite_domain_sort(ctx.nCtx, name.NativeObject, size))
        {
            Contract.Requires(ctx != null);
            Contract.Requires(name != null);

        }
        #endregion
    }
}
