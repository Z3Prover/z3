/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    ConstructorList.cs

Abstract:

    Z3 Managed API: Constructor Lists

Author:

    Christoph Wintersteiger (cwinter) 2012-11-23

Notes:
    
--*/

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// Lists of constructors
    /// </summary>
    public class ConstructorList : Z3Object
    {
        /// <summary>
        /// Destructor.
        /// </summary>
        ~ConstructorList()
        {
            Native.Z3_del_constructor_list(Context.nCtx, NativeObject);
        }

        #region Internal
        internal ConstructorList(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }

        internal ConstructorList(Context ctx, Constructor[] constructors)
            : base(ctx)
        {
            Contract.Requires(ctx != null);
            Contract.Requires(constructors != null);

            NativeObject = Native.Z3_mk_constructor_list(Context.nCtx, (uint)constructors.Length, Constructor.ArrayToNative(constructors));
        }
        #endregion
    }
}
