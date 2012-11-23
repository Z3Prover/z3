/**
 * This file was automatically generated from Log.cs 
 **/

package com.Microsoft.Z3;

/* using System; */

    /**
     * Interaction logging for Z3.
     * <remarks>
     * Note that this is a global, static log and if multiple Context 
     * objects are created, it logs the interaction with all of them.
     * </remarks>
     **/
    public final class Log
    {
        private  boolean m_is_open = false;

        /**
         * Open an interaction log file.
         * <param name="filename">the name of the file to open</param>
         * @return True if opening the log file succeeds, false otherwise.
         **/
        public  boolean Open(String filename)
        {
            m_is_open = true;
            return Native.openLog(filename) == 1;
        }

        /**
         * Closes the interaction log.
         **/
        public  void Close()
        {
            m_is_open = false;
            Native.closeLog();
        }

        /**
         * Appends the user-provided string <paramref name="s"/> to the interaction log.
         **/
        public  void Append(String s)
        {
            

            if (!m_is_open)
                throw new Z3Exception("Log cannot be closed.");
            Native.appendLog(s);
        }

        /**
         * Checks whether the interaction log is opened.
         * @return True if the interaction log is open, false otherwise.
         **/
        public  boolean isOpen()
        {
            return m_is_open;
        }
    }
