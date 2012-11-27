/**
 *  Automatically generated file
 **/

package com.Microsoft.Z3.Enumerations;

/**
 * Z3_ast_print_mode
 **/
public enum Z3_ast_print_mode {
    Z3_PRINT_SMTLIB2_COMPLIANT (3),
    Z3_PRINT_SMTLIB_COMPLIANT (2),
    Z3_PRINT_SMTLIB_FULL (0),
    Z3_PRINT_LOW_LEVEL (1);

    private final int intValue;

    Z3_ast_print_mode(int v) {
        this.intValue = v;
    }

    public static final Z3_ast_print_mode fromInt(int v) {
        for (Z3_ast_print_mode k: values()) 
            if (k.intValue == v) return k;
        return values()[0];
    }

    public final int toInt() { return this.intValue; }
}

