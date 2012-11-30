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
#include"api_config_params.h"
#include"pp.h"
#include"api_log_macros.h"
#include"api_util.h"
#include"cmd_context.h"
#include"symbol.h"
#include"gparams.h"

namespace api {

    config_params::config_params() {
    }
    
    config_params::config_params(front_end_params const & p):m_params(p) {
    }

};

extern "C" {
    Z3_config Z3_API Z3_mk_config() {
        LOG_Z3_mk_config();
        memory::initialize(0);
        Z3_config r = reinterpret_cast<Z3_config>(alloc(api::config_params));
        RETURN_Z3(r);
    }
    
    void Z3_API Z3_del_config(Z3_config c) {
        LOG_Z3_del_config(c);
        dealloc((reinterpret_cast<api::config_params*>(c)));
    }
    
    void Z3_API Z3_set_param_value(Z3_config c, char const * param_id, char const * param_value) {
        // REMARK: we don't need Z3_config anymore
        try { 
            LOG_Z3_set_param_value(c, param_id, param_value);
            gparams::set(param_id, param_value);
        }
        catch (gparams::exception & ex) {
            // The error handler was not set yet.
            // Just throw a warning.
            std::ostringstream buffer;
            buffer << "Error setting " << param_id << ", " << ex.msg();
            warning_msg(buffer.str().c_str());
        }
    }

    void Z3_API Z3_update_param_value(Z3_context c, Z3_string param_id, Z3_string param_value) {
        Z3_TRY;
        LOG_Z3_update_param_value(c, param_id, param_value);
        RESET_ERROR_CODE();
        gparams::set(param_id, param_value);
        // TODO: set memory limits
        // memory::set_high_watermark(static_cast<size_t>(mk_c(c)->fparams().m_memory_high_watermark)*1024*1024);
        // memory::set_max_size(static_cast<size_t>(mk_c(c)->fparams().m_memory_max_size)*1024*1024);
        Z3_CATCH;
    }

    Z3_bool Z3_API Z3_get_param_value(Z3_context c, Z3_string param_id, Z3_string* param_value) {
        LOG_Z3_get_param_value(c, param_id, param_value);
        // TODO: we don't really have support for that anymore.
        return false;
    }

};
