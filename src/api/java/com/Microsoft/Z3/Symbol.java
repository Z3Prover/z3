/**
 * This file was automatically generated from Symbol.cs 
 **/

package com.Microsoft.Z3;

/* using System; */
/* using System.Runtime.InteropServices; */

    /**
     * Symbols are used to name several term and type constructors.
     **/
    public class Symbol extends Z3Object
    {
        /**
         * The kind of the symbol (int or string)
         **/
        protected Z3_symbol_kind Kind
        {
            get { return (Z3_symbol_kind)Native.getSymbolKind(Context.nCtx, NativeObject); }
        }

        /**
         * Indicates whether the symbol is of Int kind
         **/
        public boolean IsIntSymbol()
        {
            return Kind == Z3_symbol_kind.Z3_INT_SYMBOL;
        }

        /**
         * Indicates whether the symbol is of string kind.
         **/
        public boolean IsStringSymbol()
        {
            return Kind == Z3_symbol_kind.Z3_STRING_SYMBOL;
        }

        /**
         * A string representation of the symbol.
         **/
        public String toString()
        {
            if (IsIntSymbol())
                return ((IntSymbol)this).Int.toString();
            else if (IsStringSymbol())
                return ((StringSymbol)this).String;
            else
                throw new Z3Exception("Unknown symbol kind encountered");
        }

        /**
         * Symbol constructor
         **/
        protected Symbol(Context ctx, IntPtr obj) { super(ctx, obj); 
            
        }

        static Symbol Create(Context ctx, IntPtr obj)
        {
            
            

            switch ((Z3_symbol_kind)Native.getSymbolKind(ctx.nCtx, obj))
            {
                case Z3_symbol_kind.Z3_INT_SYMBOL: return new IntSymbol(ctx, obj);
                case Z3_symbol_kind.Z3_STRING_SYMBOL: return new StringSymbol(ctx, obj);
                default:
                    throw new Z3Exception("Unknown symbol kind encountered");
            }
        }
    }

    /**
     * Numbered symbols
     **/
    public class IntSymbol extends Symbol
    {
        /**
         * The int value of the symbol.
         * <remarks>Throws an exception if the symbol is not of int kind. </remarks>
         **/
        public int Int() 
            {
                if (!IsIntSymbol())
                    throw new Z3Exception("Int requested from non-Int symbol");
                return Native.getSymbolInt(Context.nCtx, NativeObject);
            }

        IntSymbol(Context ctx, IntPtr obj)
            { super(ctx, obj);
            
        }
        IntSymbol(Context ctx, int i)
            { super(ctx, Native.mkIntSymbol(ctx.nCtx, i));
            
        }

        void CheckNativeObject(IntPtr obj)
        {
            if ((Z3_symbol_kind)Native.getSymbolKind(Context.nCtx, obj) != Z3_symbol_kind.Z3_INT_SYMBOL)
                throw new Z3Exception("Symbol is not of integer kind");
            super.CheckNativeObject(obj);
        }
    }

    /**
     * Named symbols
     **/
    public class StringSymbol extends Symbol
    {
        /**
         * The string value of the symbol.
         * <remarks>Throws an exception if the symbol is not of string kind.</remarks>
         **/
        public String String() 
            {
                

                if (!IsStringSymbol())
                    throw new Z3Exception("String requested from non-String symbol");
                return Native.getSymbolString(Context.nCtx, NativeObject);                
            }

        StringSymbol(Context ctx, IntPtr obj) { super(ctx, obj); 
            
        }

        StringSymbol(Context ctx, String s) { super(ctx, Native.mkStringSymbol(ctx.nCtx, s)); 
            
        }

        void CheckNativeObject(IntPtr obj)
        {
            if ((Z3_symbol_kind)Native.getSymbolKind(Context.nCtx, obj) != Z3_symbol_kind.Z3_STRING_SYMBOL)
                throw new Z3Exception("Symbol is not of String kind");

            super.CheckNativeObject(obj);
        }
    }
