/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    Log.cs

Abstract:

    Z3 Managed API: Log

Author:

    Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
--*/

using System.Diagnostics;
using System;

namespace Microsoft.Z3
{
    /// <summary>
    /// Interaction logging for Z3.
    /// </summary>
    /// <remarks>
    /// Note that this is a global, static log and if multiple Context 
    /// objects are created, it logs the interaction with all of them.
    /// </remarks>
    public static class Log
    {
        private static bool m_is_open = false;

        /// <summary>
        /// Open an interaction log file.
        /// </summary>
        /// <param name="filename">the name of the file to open</param>
        /// <returns>True if opening the log file succeeds, false otherwise.</returns>
        public static bool Open(string filename)
        {
            m_is_open = true;
            return Native.Z3_open_log(filename) == 1;
        }

        /// <summary>
        /// Closes the interaction log.
        /// </summary>
        public static void Close()
        {
            m_is_open = false;
            Native.Z3_close_log();
        }

        /// <summary>
        /// Appends the user-provided string <paramref name="s"/> to the interaction log.
        /// </summary>    
        public static void Append(string s)
        {
            Debug.Assert(isOpen());

            if (!m_is_open)
                throw new Z3Exception("Log cannot be closed.");
            Native.Z3_append_log(s);
        }

        /// <summary>
        /// Checks whether the interaction log is opened.
        /// </summary>
        /// <returns>True if the interaction log is open, false otherwise.</returns>
        public static bool isOpen()
        {
            return m_is_open;
        }
    }
}
