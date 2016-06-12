/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    StringSymbol.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

import com.microsoft.z3.enumerations.Z3_symbol_kind;

/**
 * Named symbols
 **/
public class StringSymbol extends Symbol
{
    /**
     * The string value of the symbol.
     * Remarks: Throws an exception if the
     * symbol is not of string kind.
     **/
    public String getString()
    {
        return Native.getSymbolString(getContext().nCtx(), getNativeObject());
    }

    StringSymbol(Context ctx, long obj)
    {
        super(ctx, obj);
    }

    StringSymbol(Context ctx, String s)
    {
        super(ctx, Native.mkStringSymbol(ctx.nCtx(), s));
    }

    @Override
    void checkNativeObject(long obj)
    {
        if (Native.getSymbolKind(getContext().nCtx(), obj) != Z3_symbol_kind.Z3_STRING_SYMBOL
                .toInt()) {
            throw new Z3Exception("Symbol is not of String kind");
        }
        super.checkNativeObject(obj);
    }
}
