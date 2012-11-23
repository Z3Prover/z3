/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    StringSymbol.cs

Abstract:

    Z3 Managed API: String Symbols

Author:

    Christoph Wintersteiger (cwinter) 2012-11-23

Notes:
    
--*/

using System;
using System.Runtime.InteropServices;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{

    /// <summary>
    /// Named symbols
    /// </summary>
    [ContractVerification(true)]
    public class StringSymbol : Symbol
    {
        /// <summary>
        /// The string value of the symbol.
        /// </summary>
        /// <remarks>Throws an exception if the symbol is not of string kind.</remarks>
        public string String
        {
            get
            {
                Contract.Ensures(Contract.Result<string>() != null);

                if (!IsStringSymbol())
                    throw new Z3Exception("String requested from non-String symbol");
                return Native.Z3_get_symbol_string(Context.nCtx, NativeObject);
            }
        }

        #region Internal
        internal StringSymbol(Context ctx, IntPtr obj)
            : base(ctx, obj)
        {
            Contract.Requires(ctx != null);
        }

        internal StringSymbol(Context ctx, string s)
            : base(ctx, Native.Z3_mk_string_symbol(ctx.nCtx, s))
        {
            Contract.Requires(ctx != null);
        }

#if DEBUG
        internal override void CheckNativeObject(IntPtr obj)
        {
            if ((Z3_symbol_kind)Native.Z3_get_symbol_kind(Context.nCtx, obj) != Z3_symbol_kind.Z3_STRING_SYMBOL)
                throw new Z3Exception("Symbol is not of string kind");

            base.CheckNativeObject(obj);
        }
#endif
        #endregion
    }
}
