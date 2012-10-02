/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    Symbol.cs

Abstract:

    Z3 Managed API: Symbols

Author:

    Christoph Wintersteiger (cwinter) 2012-03-16

Notes:
    
--*/

using System;
using System.Runtime.InteropServices;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// Symbols are used to name several term and type constructors.
    /// </summary>
    [ContractVerification(true)]
    public class Symbol : Z3Object
    {
        /// <summary>
        /// The kind of the symbol (int or string)
        /// </summary>
        protected Z3_symbol_kind Kind
        {
            get { return (Z3_symbol_kind)Native.Z3_get_symbol_kind(Context.nCtx, NativeObject); }
        }

        /// <summary>
        /// Indicates whether the symbol is of Int kind
        /// </summary>    
        public bool IsIntSymbol()
        {
            return Kind == Z3_symbol_kind.Z3_INT_SYMBOL;
        }

        /// <summary>
        /// Indicates whether the symbol is of string kind.
        /// </summary>
        public bool IsStringSymbol()
        {
            return Kind == Z3_symbol_kind.Z3_STRING_SYMBOL;
        }

        /// <summary>
        /// A string representation of the symbol.
        /// </summary>
        public override string ToString()
        {
            if (IsIntSymbol())
                return ((IntSymbol)this).Int.ToString();
            else if (IsStringSymbol())
                return ((StringSymbol)this).String;
            else
                throw new Z3Exception("Unknown symbol kind encountered");
        }

        #region Internal
        /// <summary>
        /// Symbol constructor
        /// </summary>
        internal protected Symbol(Context ctx, IntPtr obj) : base(ctx, obj) 
        {
            Contract.Requires(ctx != null);
        }

        internal static Symbol Create(Context ctx, IntPtr obj)
        {
            Contract.Requires(ctx != null);
            Contract.Ensures(Contract.Result<Symbol>() != null);

            switch ((Z3_symbol_kind)Native.Z3_get_symbol_kind(ctx.nCtx, obj))
            {
                case Z3_symbol_kind.Z3_INT_SYMBOL: return new IntSymbol(ctx, obj);
                case Z3_symbol_kind.Z3_STRING_SYMBOL: return new StringSymbol(ctx, obj);
                default:
                    throw new Z3Exception("Unknown symbol kind encountered");
            }
        }
        #endregion
    }

    /// <summary>
    /// Numbered symbols
    /// </summary>
    [ContractVerification(true)]
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
            Contract.Requires(ctx != null);
        }
        internal IntSymbol(Context ctx, int i)
            : base(ctx, Native.Z3_mk_int_symbol(ctx.nCtx, i))
        {
            Contract.Requires(ctx != null);
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
        internal StringSymbol(Context ctx, IntPtr obj) : base(ctx, obj) 
        {            
            Contract.Requires(ctx != null);
        }

        internal StringSymbol(Context ctx, string s) : base(ctx, Native.Z3_mk_string_symbol(ctx.nCtx, s)) 
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
