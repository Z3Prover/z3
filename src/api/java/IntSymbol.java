/**
 * This file was automatically generated from IntSymbol.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

import com.microsoft.z3.enumerations.Z3_symbol_kind;

/**
 * Numbered symbols
 **/
public class IntSymbol extends Symbol
{
    /**
     * The int value of the symbol. <remarks>Throws an exception if the symbol
     * is not of int kind. </remarks>
     **/
    public int getInt() throws Z3Exception
    {
        if (!isIntSymbol())
            throw new Z3Exception("Int requested from non-Int symbol");
        return Native.getSymbolInt(getContext().nCtx(), getNativeObject());
    }

    IntSymbol(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }

    IntSymbol(Context ctx, int i) throws Z3Exception
    {
        super(ctx, Native.mkIntSymbol(ctx.nCtx(), i));
    }

    void checkNativeObject(long obj) throws Z3Exception
    {
        if (Native.getSymbolKind(getContext().nCtx(), obj) != Z3_symbol_kind.Z3_INT_SYMBOL
                .toInt())
            throw new Z3Exception("Symbol is not of integer kind");
        super.checkNativeObject(obj);
    }
}
