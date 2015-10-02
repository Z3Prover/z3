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


        /// <summary>
        /// Equality overloading.
        /// </summary>
        public static bool operator ==(Symbol s1, Symbol s2)
        {
            
            return Object.ReferenceEquals(s1, s2) ||
                   (!Object.ReferenceEquals(s1, null) &&
                    !Object.ReferenceEquals(s2, null) &&
                    s1.NativeObject == s2.NativeObject);
        }

        /// <summary>
        /// Equality overloading.
        /// </summary>
        public static bool operator !=(Symbol s1, Symbol s2)
        {
            return !(s1.NativeObject == s2.NativeObject);
        }

        /// <summary>
        /// Object comparison.
        /// </summary>
        public override bool Equals(object o)
        {
            Symbol casted = o as Symbol;
            if (casted == null) return false;
            return this == casted;
        }

        /// <summary>
        /// The Symbols's hash code.
        /// </summary>
        /// <returns>A hash code</returns>
        public override int GetHashCode()
        {
            return (int)NativeObject;
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
}
