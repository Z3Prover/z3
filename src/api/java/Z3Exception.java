/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    Z3Exception.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;


/**
 * The exception base class for error reporting from Z3
 **/
@SuppressWarnings("serial")
public class Z3Exception extends Exception
{
    /**
     * Constructor.
     **/
    public Z3Exception()
    {
        super();
    }

    /**
     * Constructor.
     **/
    public Z3Exception(String message)
    {
        super(message);
    }

    /**
     * Constructor.
     **/
    public Z3Exception(String message, Exception inner)
    {
        super(message, inner);
    }
}
