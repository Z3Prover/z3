/**
 *  Automatically generated file
 **/

package com.Microsoft.Z3;

/**
 * Z3_symbol_kind
 **/
public enum Z3_symbol_kind {
    Z3_INT_SYMBOL (0),
    Z3_STRING_SYMBOL (1);

    private final int intValue;

    Z3_symbol_kind(int v) {
        this.intValue = v;
    }

    public static final Z3_symbol_kind fromInt(int v) {
        for (Z3_symbol_kind k: values()) 
            if (k.intValue == v) return k;
        return values()[0];
    }

    public final int toInt() { return this.intValue; }
}

