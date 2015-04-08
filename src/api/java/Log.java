/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    Log.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

/**
 * Interaction logging for Z3.
     * Remarks:  Note that this is a global, static log
 * and if multiple Context objects are created, it logs the interaction with all
 * of them. 
 **/
public final class Log
{
    private static boolean m_is_open = false;

    /**
     * Open an interaction log file. 
     * @param filename the name of the file to open
     * 
     * @return True if opening the log file succeeds, false otherwise.
     **/
    public static boolean open(String filename)
    {
        m_is_open = true;
        return Native.openLog(filename) == 1;
    }

    /**
     * Closes the interaction log.
     **/
    public static void close()
    {
        m_is_open = false;
        Native.closeLog();
    }

    /**
     * Appends the user-provided string {@code s} to the interaction
     * log.
     * @throws Z3Exception 
     **/
    public static void append(String s)
    {
        if (!m_is_open)
            throw new Z3Exception("Log cannot be closed.");
        Native.appendLog(s);
    }

    /**
     * Checks whether the interaction log is opened.
     * 
     * @return True if the interaction log is open, false otherwise.
     **/
    public static boolean isOpen()
    {
        return m_is_open;
    }
}
