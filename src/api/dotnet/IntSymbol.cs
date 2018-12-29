/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    IntSymbol.cs

Abstract:

    Z3 Managed API: Int Symbols

Author:

    Christoph Wintersteiger (cwinter) 2012-11-23

Notes:
    
--*/

using System;
using System.Diagnostics;
using System.Runtime.InteropServices;

namespace Microsoft.Z3
{
    /// <summary>
    /// Numbered symbols
    /// </summary>
    public class IntSymbol : Symbol
    {
        /// <summary>
        /// The int value of the symbol.
        /// </summary>
        /// <remarks>Throws an exception if the symbol is not of int kind. </remarks>
        public int Int
        {
            get
            {
                if (!IsIntSymbol())
                    throw new Z3Exception("Int requested from non-Int symbol");
                return Native.Z3_get_symbol_int(Context.nCtx, NativeObject);
            }
        }

        #region Internal
        internal IntSymbol(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Debug.Assert(ctx != null);
        }
        internal IntSymbol(Context ctx, int i)
            : base(ctx, Native.Z3_mk_int_symbol(ctx.nCtx, i))
        {
            Debug.Assert(ctx != null);
        }

#if DEBUG
        internal override void CheckNativeObject(IntPtr obj)
        {
            if ((Z3_symbol_kind)Native.Z3_get_symbol_kind(Context.nCtx, obj) != Z3_symbol_kind.Z3_INT_SYMBOL)
                throw new Z3Exception("Symbol is not of integer kind");
            base.CheckNativeObject(obj);
        }
#endif
        #endregion
    }
}
