/**
 * This file was automatically generated from Z3Exception.cs 
 * w/ further modifications by:
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.Microsoft.Z3;

import java.lang.Exception;

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
