/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_config_params.cpp

Abstract:
    Configuration parameters

Author:

    Leonardo de Moura (leonardo) 2012-02-29.

Revision History:

--*/
#include"z3.h"
#include"api_context.h"
#include"pp.h"
#include"api_log_macros.h"
#include"api_util.h"
#include"cmd_context.h"
#include"symbol.h"
#include"gparams.h"
#include"env_params.h"
#include"context_params.h"

extern "C" {
    void Z3_API Z3_global_param_set(Z3_string param_id, Z3_string param_value) {
        memory::initialize(UINT_MAX);
        LOG_Z3_global_param_set(param_id, param_value);
        try { 
            gparams::set(param_id, param_value);
            env_params::updt_params();
        }
        catch (z3_exception & ex) {
            // The error handler is only available for contexts
            // Just throw a warning.
            warning_msg("%s", ex.msg());
        }
    }

    void Z3_API Z3_global_param_reset_all(void) {
        memory::initialize(UINT_MAX);
        LOG_Z3_global_param_reset_all();
        gparams::reset();
        env_params::updt_params();
    }

    std::string g_Z3_global_param_get_buffer;
    
    Z3_bool_opt Z3_API Z3_global_param_get(Z3_string param_id, Z3_string_ptr param_value) {
        memory::initialize(UINT_MAX);
        LOG_Z3_global_param_get(param_id, param_value);
        *param_value = 0;
        try {
            g_Z3_global_param_get_buffer = gparams::get_value(param_id);
            *param_value = g_Z3_global_param_get_buffer.c_str();
            return Z3_TRUE;
        }
        catch (z3_exception & ex) {
            // The error handler is only available for contexts
            // Just throw a warning.
            warning_msg("%s", ex.msg());
            return Z3_FALSE;
        }
    }

    Z3_config Z3_API Z3_mk_config(void) {
        memory::initialize(UINT_MAX);
        LOG_Z3_mk_config();
        Z3_config r = reinterpret_cast<Z3_config>(alloc(context_params));
        RETURN_Z3(r);
    }
    
    void Z3_API Z3_del_config(Z3_config c) {
        LOG_Z3_del_config(c);
        dealloc((reinterpret_cast<context_params*>(c)));
    }
    
    void Z3_API Z3_set_param_value(Z3_config c, char const * param_id, char const * param_value) {
        LOG_Z3_set_param_value(c, param_id, param_value);
        try {
            context_params * p = reinterpret_cast<context_params*>(c);
            p->set(param_id, param_value);
        }
        catch (z3_exception & ex) {
            // The error handler is only available for contexts
            // Just throw a warning.
            warning_msg("%s", ex.msg());
        }
    }

    void Z3_API Z3_update_param_value(Z3_context c, Z3_string param_id, Z3_string param_value) {
        Z3_TRY;
        LOG_Z3_update_param_value(c, param_id, param_value);
        RESET_ERROR_CODE();
        mk_c(c)->params().set(param_id, param_value);
        Z3_CATCH;
    }

};
