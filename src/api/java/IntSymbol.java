/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    IntSymbol.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

import com.microsoft.z3.enumerations.Z3_symbol_kind;

/**
 * Numbered symbols
 **/
public class IntSymbol extends Symbol
{
    /**
     * The int value of the symbol.
     * Remarks: Throws an exception if the symbol
     * is not of int kind. 
     **/
    public int getInt()
    {
        if (!isIntSymbol())
            throw new Z3Exception("Int requested from non-Int symbol");
        return Native.getSymbolInt(getContext().nCtx(), getNativeObject());
    }

    IntSymbol(Context ctx, long obj)
    {
        super(ctx, obj);
    }

    IntSymbol(Context ctx, int i)
    {
        super(ctx, Native.mkIntSymbol(ctx.nCtx(), i));
    }

    @Override
    void checkNativeObject(long obj)
    {
        if (Native.getSymbolKind(getContext().nCtx(), obj) != Z3_symbol_kind.Z3_INT_SYMBOL
                .toInt())
            throw new Z3Exception("Symbol is not of integer kind");
        super.checkNativeObject(obj);
    }
}
