/**
 *  Automatically generated file
 **/

package com.Microsoft.Z3.Enumerations;

/**
 * Z3_goal_prec
 **/
public enum Z3_goal_prec {
    Z3_GOAL_UNDER (1),
    Z3_GOAL_PRECISE (0),
    Z3_GOAL_UNDER_OVER (3),
    Z3_GOAL_OVER (2);

    private final int intValue;

    Z3_goal_prec(int v) {
        this.intValue = v;
    }

    public static final Z3_goal_prec fromInt(int v) {
        for (Z3_goal_prec k: values()) 
            if (k.intValue == v) return k;
        return values()[0];
    }

    public final int toInt() { return this.intValue; }
}

