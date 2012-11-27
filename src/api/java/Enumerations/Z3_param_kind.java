/**
 *  Automatically generated file
 **/

package com.Microsoft.Z3.Enumerations;

/**
 * Z3_param_kind
 **/
public enum Z3_param_kind {
    Z3_PK_BOOL (1),
    Z3_PK_SYMBOL (3),
    Z3_PK_OTHER (5),
    Z3_PK_INVALID (6),
    Z3_PK_UINT (0),
    Z3_PK_STRING (4),
    Z3_PK_DOUBLE (2);

    private final int intValue;

    Z3_param_kind(int v) {
        this.intValue = v;
    }

    public static final Z3_param_kind fromInt(int v) {
        for (Z3_param_kind k: values()) 
            if (k.intValue == v) return k;
        return values()[0];
    }

    public final int toInt() { return this.intValue; }
}

