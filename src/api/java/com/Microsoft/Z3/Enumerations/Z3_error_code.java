/**
 *  Automatically generated file
 **/

package com.Microsoft.Z3;

/**
 * Z3_error_code
 **/
public enum Z3_error_code {
    Z3_INVALID_PATTERN (6),
    Z3_MEMOUT_FAIL (7),
    Z3_NO_PARSER (5),
    Z3_OK (0),
    Z3_INVALID_ARG (3),
    Z3_EXCEPTION (12),
    Z3_IOB (2),
    Z3_INTERNAL_FATAL (9),
    Z3_INVALID_USAGE (10),
    Z3_FILE_ACCESS_ERROR (8),
    Z3_SORT_ERROR (1),
    Z3_PARSER_ERROR (4),
    Z3_DEC_REF_ERROR (11);

    private final int intValue;

    Z3_error_code(int v) {
        this.intValue = v;
    }

    public static final Z3_error_code fromInt(int v) {
        for (Z3_error_code k: values()) 
            if (k.intValue == v) return k;
        return values()[0];
    }

    public final int toInt() { return this.intValue; }
}

