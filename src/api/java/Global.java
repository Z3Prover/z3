/**
Copyright (c) 2012-2014 Microsoft Corporation
   
Module Name:

    Global.java

Abstract:

Author:

    @author Christoph Wintersteiger (cwinter) 2012-03-15

Notes:
    
**/ 

package com.microsoft.z3;

/**
 * Global functions for Z3. 
 * Remarks: 
 * This (static) class contains functions that effect the behaviour of Z3
 * globally across contexts, etc. 
 * 
 **/
public final class Global
{
    /**
     * Set a global (or module) parameter, which is shared by all Z3 contexts.
     * Remarks: 
     * When a Z3 module is initialized it will use the value of these parameters
     * when Z3_params objects are not provided.
     * The name of parameter can be composed of characters [a-z][A-Z], digits [0-9], '-' and '_'. 
     * The character '.' is a delimiter (more later).
     * The parameter names are case-insensitive. The character '-' should be viewed as an "alias" for '_'.
     * Thus, the following parameter names are considered equivalent: "pp.decimal-precision"  and "PP.DECIMAL_PRECISION".
     * This function can be used to set parameters for a specific Z3 module.
     * This can be done by using &lt;module-name&gt;.&lt;parameter-name&gt;.
     * For example:
     * Z3_global_param_set('pp.decimal', 'true')
     * will set the parameter "decimal" in the module "pp" to true.
     * 
     **/
    public static void setParameter(String id, String value)
    {
        Native.globalParamSet(id, value);
    }
    
    /**
     * Get a global (or module) parameter.     
     * Remarks:     
     * This function cannot be invoked simultaneously from different threads without synchronization.
     * The result string stored in param_value is stored in a shared location.
     * @return null if the parameter {@code id} does not exist.
     **/
    public static String getParameter(String id)
    {
        Native.StringPtr res = new Native.StringPtr();
        if (!Native.globalParamGet(id, res))
            return null;
        else
            return res.value;
    }    
    
    /**
     * Restore the value of all global (and module) parameters.
     * Remarks: 
     * This command will not affect already created objects (such as tactics and solvers)
     * @see setParameter
     **/
    public static void resetParameters()
    {
        Native.globalParamResetAll();
    }
    
    /**
     * Enable/disable printing of warning messages to the console.
     * Remarks: Note
     * that this function is static and effects the behaviour of all contexts
     * globally.
     **/
    public static void ToggleWarningMessages(boolean enabled)
            throws Z3Exception
    {
        Native.toggleWarningMessages((enabled) ? true : false);
    }
    
    /** 
     * Enable tracing messages tagged as `tag' when Z3 is compiled in debug mode.        
     * 
     * Remarks: It is a NOOP otherwise.
     **/
    public static void enableTrace(String tag)
    {
        Native.enableTrace(tag);
    }

    /** 
     * Disable tracing messages tagged as `tag' when Z3 is compiled in debug mode.        
     * 
     * Remarks: It is a NOOP otherwise.
     **/
    public static void disableTrace(String tag)
    {
        Native.disableTrace(tag);
    }
}
