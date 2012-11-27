/**
 * This file was automatically generated from Symbol.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

import com.microsoft.z3.enumerations.*;

/**
 * Symbols are used to name several term and type constructors.
 **/
public class Symbol extends Z3Object
{
    /**
     * The kind of the symbol (int or string)
     **/
    protected Z3_symbol_kind Kind()
    {
        return Z3_symbol_kind.fromInt(Native.getSymbolKind(Context().nCtx(),
                NativeObject()));
    }

    /**
     * Indicates whether the symbol is of Int kind
     **/
    public boolean IsIntSymbol()
    {
        return Kind() == Z3_symbol_kind.Z3_INT_SYMBOL;
    }

    /**
     * Indicates whether the symbol is of string kind.
     **/
    public boolean IsStringSymbol()
    {
        return Kind() == Z3_symbol_kind.Z3_STRING_SYMBOL;
    }

    /**
     * A string representation of the symbol.
     **/
    public String toString()
    {
        try
        {
            if (IsIntSymbol())
                return Integer.toString(((IntSymbol) this).Int());
            else if (IsStringSymbol())
                return ((StringSymbol) this).String();
            else
                return new String(
                        "Z3Exception: Unknown symbol kind encountered.");
        } catch (Z3Exception ex)
        {
            return new String("Z3Exception: " + ex.getMessage());
        }
    }

    /**
     * Symbol constructor
     **/
    protected Symbol(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }

    static Symbol Create(Context ctx, long obj) throws Z3Exception
    {
        switch (Z3_symbol_kind.fromInt(Native.getSymbolKind(ctx.nCtx(), obj)))
        {
        case Z3_INT_SYMBOL:
            return new IntSymbol(ctx, obj);
        case Z3_STRING_SYMBOL:
            return new StringSymbol(ctx, obj);
        default:
            throw new Z3Exception("Unknown symbol kind encountered");
        }
    }
}
