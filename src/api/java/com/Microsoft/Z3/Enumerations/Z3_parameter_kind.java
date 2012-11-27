/**
 *  Automatically generated file
 **/

package com.Microsoft.Z3.Enumerations;

/**
 * Z3_parameter_kind
 **/
public enum Z3_parameter_kind {
    Z3_PARAMETER_FUNC_DECL (6),
    Z3_PARAMETER_DOUBLE (1),
    Z3_PARAMETER_SYMBOL (3),
    Z3_PARAMETER_INT (0),
    Z3_PARAMETER_AST (5),
    Z3_PARAMETER_SORT (4),
    Z3_PARAMETER_RATIONAL (2);

    private final int intValue;

    Z3_parameter_kind(int v) {
        this.intValue = v;
    }

    public static final Z3_parameter_kind fromInt(int v) {
        for (Z3_parameter_kind k: values()) 
            if (k.intValue == v) return k;
        return values()[0];
    }

    public final int toInt() { return this.intValue; }
}

