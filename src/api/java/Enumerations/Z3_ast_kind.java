/**
 *  Automatically generated file
 **/

package com.Microsoft.Z3.Enumerations;

/**
 * Z3_ast_kind
 **/
public enum Z3_ast_kind {
    Z3_VAR_AST (2),
    Z3_SORT_AST (4),
    Z3_QUANTIFIER_AST (3),
    Z3_UNKNOWN_AST (1000),
    Z3_FUNC_DECL_AST (5),
    Z3_NUMERAL_AST (0),
    Z3_APP_AST (1);

    private final int intValue;

    Z3_ast_kind(int v) {
        this.intValue = v;
    }

    public static final Z3_ast_kind fromInt(int v) {
        for (Z3_ast_kind k: values()) 
            if (k.intValue == v) return k;
        return values()[0];
    }

    public final int toInt() { return this.intValue; }
}

