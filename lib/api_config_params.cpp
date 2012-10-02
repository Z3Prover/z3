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
#include"symbol.h"

namespace api {

    config_params::config_params():
        m_ini(false /* do not abort on errors */) {
        register_verbosity_level(m_ini);
        register_warning(m_ini);
        m_params.register_params(m_ini); 
        register_pp_params(m_ini);
    }
    
    config_params::config_params(front_end_params const & p):m_params(p) {
        register_verbosity_level(m_ini);
        register_warning(m_ini);
        register_pp_params(m_ini);
    }

};

extern std::string smt_keyword2opt_name(symbol const & opt);

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
        try { 
            LOG_Z3_set_param_value(c, param_id, param_value);
            api::config_params* p = reinterpret_cast<api::config_params*>(c);
            if (param_id != 0 && param_id[0] == ':') {
                // Allow SMT2 style paramater names such as  :model, :relevancy, etc
                std::string new_param_id = smt_keyword2opt_name(symbol(param_id));
                p->m_ini.set_param_value(new_param_id.c_str(), param_value);
            }
            else {
                p->m_ini.set_param_value(param_id, param_value);
            }
        }
        catch (set_get_param_exception & ex) {
            // The error handler was not set yet.
            // Just throw a warning.
            std::ostringstream buffer;
            buffer << "Error setting " << param_id << ", " << ex.get_msg();
            warning_msg(buffer.str().c_str());
        }
    }

    void Z3_API Z3_update_param_value(Z3_context c, Z3_string param_id, Z3_string param_value) {
        LOG_Z3_update_param_value(c, param_id, param_value);
        RESET_ERROR_CODE();
        ini_params ini;        
        mk_c(c)->fparams().register_params(ini);
        register_pp_params(ini);
        register_verbosity_level(ini);
        register_warning(ini);
        if (mk_c(c)->has_solver()) {
            ini.freeze();
        }
        if (param_id != 0 && param_id[0] == ':') {
            // Allow SMT2 style paramater names such as  :model, :relevancy, etc
            std::string new_param_id = smt_keyword2opt_name(symbol(param_id));
            ini.set_param_value(new_param_id.c_str(), param_value);
        }
        else {
            ini.set_param_value(param_id, param_value);
        }
        memory::set_high_watermark(static_cast<size_t>(mk_c(c)->fparams().m_memory_high_watermark)*1024*1024);
        memory::set_max_size(static_cast<size_t>(mk_c(c)->fparams().m_memory_max_size)*1024*1024);
    }

    Z3_bool Z3_API Z3_get_param_value(Z3_context c, Z3_string param_id, Z3_string* param_value) {
        LOG_Z3_get_param_value(c, param_id, param_value);
        ini_params ini;        
        mk_c(c)->fparams().register_params(ini);
        register_verbosity_level(ini);
        register_pp_params(ini);
        register_warning(ini);
        std::string param_value_s;
        if (!ini.get_param_value(param_id, param_value_s)) {
            if (param_value) *param_value = 0;
            return false;
        }
        if (param_value) {
            *param_value = mk_c(c)->mk_external_string(param_value_s);
        }
        return true;
    }

};
