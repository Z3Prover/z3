/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    Global.cs

Abstract:

    Z3 Managed API: Global Functions

Author:

    Christoph Wintersteiger (cwinter) 2013-01-15

Notes:
    
--*/

using System;
using System.Runtime.InteropServices;
using System.Diagnostics.Contracts;

namespace Microsoft.Z3
{
    /// <summary>
    /// Global functions for Z3. 
    /// </summary>
    /// <remarks>
    /// This (static) class contains functions that effect the behaviour of Z3
    /// globally across contexts, etc. 
    /// </remarks>
    public static class Global
    {
        /// <summary>
        /// Set a global (or module) parameter, which is shared by all Z3 contexts.
        /// </summary>
        /// <remarks>
        /// When a Z3 module is initialized it will use the value of these parameters
        /// when Z3_params objects are not provided.
        /// The name of parameter can be composed of characters [a-z][A-Z], digits [0-9], '-' and '_'. 
        /// The character '.' is a delimiter (more later).
        /// The parameter names are case-insensitive. The character '-' should be viewed as an "alias" for '_'.
        /// Thus, the following parameter names are considered equivalent: "pp.decimal-precision"  and "PP.DECIMAL_PRECISION".
        /// This function can be used to set parameters for a specific Z3 module.
        /// This can be done by using [module-name].[parameter-name].
        /// For example:
        /// Z3_global_param_set('pp.decimal', 'true')
        /// will set the parameter "decimal" in the module "pp" to true.
        /// </remarks>
        public static void SetParameter(string id, string value)
        {
            Native.Z3_global_param_set(id, value);
        }

        /// <summary>
        /// Get a global (or module) parameter.
        /// </summary>
        /// <remarks>               
        /// Returns null if the parameter <param name="id"/> does not exist.
        /// The caller must invoke #Z3_global_param_del_value to delete the value returned at \c param_value.
        /// This function cannot be invoked simultaneously from different threads without synchronization.
        /// The result string stored in param_value is stored in a shared location.
        /// </remarks>
        public static string GetParameter(string id)
        {
            IntPtr t;
            if (Native.Z3_global_param_get(id, out t) == 0)
                return null;
            else
                return Marshal.PtrToStringAnsi(t);
        }    


        /// <summary>
        /// Restore the value of all global (and module) parameters.
        /// </summary>
        /// <remarks>
        /// This command will not affect already created objects (such as tactics and solvers)
        /// </remarks>
        /// <seealso cref="SetParameter"/>
        public static void ResetParameters()
        {
            Native.Z3_global_param_reset_all();
        }

        /// <summary>
        /// Enable/disable printing of warning messages to the console.
        /// </summary>
        /// <remarks>Note that this function is static and effects the behaviour of 
        /// all contexts globally.</remarks>
        public static void ToggleWarningMessages(bool enabled)
        {
            Native.Z3_toggle_warning_messages((enabled) ? 1 : 0);
        }

        /// <summary>
        /// Enable tracing messages tagged as `tag' when Z3 is compiled in debug mode.
        /// </summary>
        /// <remarks>
        /// It is a NOOP otherwise. 
        /// </remarks>
        /// <param name="tag">trace tag</param>
        public static void EnableTrace(string tag)
        {
            Native.Z3_enable_trace(tag);
        }

        /// <summary>
        /// Disable tracing messages tagged as `tag' when Z3 is compiled in debug mode.        
        /// </summary>
        /// <remarks>
        /// It is a NOOP otherwise.
        /// </remarks>
        /// <param name="tag">trace tag</param>
        public static void DisableTrace(string tag)
        {
            Native.Z3_disable_trace(tag);
        }
    }
}
