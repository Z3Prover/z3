/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    Status.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
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

    public static Status fromInt(int v)
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
