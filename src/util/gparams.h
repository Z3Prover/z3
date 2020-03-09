/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    gparams.h

Abstract:

    Global parameter management.

Author:

    Leonardo (leonardo) 2012-11-29

Notes:

--*/
#ifndef GPARAMS_H_
#define GPARAMS_H_

#include "util/params.h"

class gparams {
    struct imp;
    static imp * g_imp; 
public:
    typedef default_exception exception;

    /**
       \brief Reset all global and module parameters.
    */
    static void reset();

    /**
       \brief Set a global parameter \c name with \c value.
       
       The name of parameter can be composed of characters [a-z][A-Z], digits [0-9], '-' and '_'. 
       The character '.' is a delimiter (more later).
       
       The parameter names are case-insensitive. The character '-' should be viewed as an "alias" for '_'.
       Thus, the following parameter names are considered equivalent: "auto-config"  and "AUTO_CONFIG".
       
       This function can be used to set parameters for a specific Z3 module.
       This can be done by using <module-name>.<parameter-name>.
       For example:
       set_global_param('pp.decimal', 'true')
       will set the parameter "decimal" in the module "pp" to true.
       
       An exception is thrown if the parameter name is unknown, or if the value is incorrect.
    */
    static void set(char const * name, char const * value);
    static void set(symbol const & name, char const * value);
    
    /**
       \brief Auxiliary method used to implement get-option in SMT 2.0 front-end.
       
       If the parameter is not set, then it just returns 'default'.

       An exception is thrown if the parameter name is unknown.
    */
    static std::string get_value(char const * name);
    static std::string get_value(symbol const & name);
    
    /**
       \brief Register additional global parameters
       
       This is an auxiliary function used by our automatic code generator.
       Example: the directive REG_PARAMS('collect_param_descrs')
       "tells" the automatic code generator how to register the additional global parameters.
    */
    static void register_global(param_descrs & d);

    /**
       \brief Register parameter descriptions for a Z3 module.
       The parameters of a given Z3 module can only be set using #set_global_param if 
       they are registered in this module using this function.
       
       This is an auxiliary function used by our automatic code generator.
       Each module will contain directives (in comments) such as
       Example: the directive REG_MODULE_PARAMS('nlsat', 'nlsat::solver::collect_param_descrs')
       "tells" the automatic code generator how to register the parameters for the given
       module.
    */

    typedef std::function<param_descrs*(void)> lazy_descrs_t;
    static void register_module(char const* module_name, lazy_descrs_t& get_descrs);

    /**
       \brief Add a (small) description to the given module.
    */
    static void register_module_descr(char const * module_name, char const * descr);

    /**
       \brief Retrieves the parameters associated with the given module.
       
       Example:
       // The following command sets the parameter "decimal" in the module "pp" to true.
       set_global_param("pp.decimal", "true");
       ... 
       // The following command will return  the global parameters that were set for the module "pp".
       // In this example "p" will contain "decimal" -> true after executing this function.
       params_ref const & p = get_module_params("pp")
    */
    static params_ref get_module(char const * module_name);
    /**
       \brief Return the global parameter set (i.e., parameters that are not associated with any particular module).
    */

    static params_ref const& get_ref();

    /**
       \brief Dump information about available parameters in the given output stream.
    */
    static void display(std::ostream & out, unsigned indent = 0, bool smt2_style=false, bool include_descr=true);
    
    // Auxiliary APIs for better command line support
    static void display_modules(std::ostream & out);
    static void display_module(std::ostream & out, char const * module_name);
    static void display_parameter(std::ostream & out, char const * name);

    /**
       \brief Initialize the global parameter management module.
       
       Remark: I set a priority in the initialization, because this module must be initialized
       after the core modules such as symbol.
       ADD_INITIALIZER('gparams::init();', 1)
    */
    static void init();

    /**
       \brief Finalize the global parameter management module.
       
       ADD_FINALIZER('gparams::finalize();');
    */
    static void finalize();
};



#endif
