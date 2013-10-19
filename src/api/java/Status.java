/**
 * This file was automatically generated from Status.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

/**
 * Status values.
 **/
public enum Status
{
    // / Used to signify an unsatisfiable status.
    UNSATISFIABLE(-1),

    // / Used to signify an unknown status.
    UNKNOWN(0),

    // / Used to signify a satisfiable status.
    SATISFIABLE(1);

    private final int intValue;

    Status(int v)
    {
        this.intValue = v;
    }

    public static final Status fromInt(int v)
    {
        for (Status k : values())
            if (k.intValue == v)
                return k;
        return values()[0];
    }

    public final int toInt()
    {
        return this.intValue;
    }
}
