/**
 *  Automatically generated file
 **/

package com.Microsoft.Z3;

/**
 * Z3_lbool
 **/
public enum Z3_lbool {
    Z3_L_TRUE (1),
    Z3_L_UNDEF (0),
    Z3_L_FALSE (-1);

    private final int intValue;

    Z3_lbool(int v) {
        this.intValue = v;
    }

    public static final Z3_lbool fromInt(int v) {
        for (Z3_lbool k: values()) 
            if (k.intValue == v) return k;
        return values()[0];
    }

    public final int toInt() { return this.intValue; }
}

