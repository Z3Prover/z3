/**
 * This file was automatically generated from StringSymbol.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.Microsoft.Z3;

import com.Microsoft.Z3.Enumerations.*;

/**
 * Named symbols
 **/
public class StringSymbol extends Symbol
{
    /**
     * The string value of the symbol. <remarks>Throws an exception if the
     * symbol is not of string kind.</remarks>
     **/
    public String String() throws Z3Exception
    {
        return Native.getSymbolString(Context().nCtx(), NativeObject());
    }

    StringSymbol(Context ctx, long obj) throws Z3Exception
    {
        super(ctx, obj);
    }

    StringSymbol(Context ctx, String s) throws Z3Exception
    {
        super(ctx, Native.mkStringSymbol(ctx.nCtx(), s));
    }

    void CheckNativeObject(long obj) throws Z3Exception
    {
        if (Native.getSymbolKind(Context().nCtx(), obj) != Z3_symbol_kind.Z3_STRING_SYMBOL
                .toInt())
            throw new Z3Exception("Symbol is not of String kind");

        super.CheckNativeObject(obj);
    }
}
