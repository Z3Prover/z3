/**
 * Global.java
 * @author Christoph M. Wintersteiger (cwinter)
 **/

package com.microsoft.z3;

/**
 * Global functions for Z3. 
 * <remarks>
 * This (static) class contains functions that effect the behaviour of Z3
 * globally across contexts, etc. 
 * </remarks>
 **/
public final class Global
{
    /**
     * Set a global (or module) parameter, which is shared by all Z3 contexts.
     * <remarks>
     * When a Z3 module is initialized it will use the value of these parameters
     * when Z3_params objects are not provided.
     * The name of parameter can be composed of characters [a-z][A-Z], digits [0-9], '-' and '_'. 
     * The character '.' is a delimiter (more later).
     * The parameter names are case-insensitive. The character '-' should be viewed as an "alias" for '_'.
     * Thus, the following parameter names are considered equivalent: "pp.decimal-precision"  and "PP.DECIMAL_PRECISION".
     * This function can be used to set parameters for a specific Z3 module.
     * This can be done by using <module-name>.<parameter-name>.
     * For example:
     * Z3_global_param_set('pp.decimal', 'true')
     * will set the parameter "decimal" in the module "pp" to true.
     * </remarks>
     **/
    public static void setParameter(String id, String value)
    {
	Native.globalParamSet(id, value);
    }
    
    /**
     * Get a global (or module) parameter.     
     * <remarks>               
     * Returns null if the parameter <param name="id"/> does not exist.
     * The caller must invoke #Z3_global_param_del_value to delete the value returned at \c param_value.
     * This function cannot be invoked simultaneously from different threads without synchronization.
     * The result string stored in param_value is stored in a shared location.
     * </remarks>
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
     * <remarks>
     * This command will not affect already created objects (such as tactics and solvers)
     * </remarks>
     * @seealso SetParameter
     **/
    public static void resetParameters()
    {
	Native.globalParamResetAll();
    }   
}
