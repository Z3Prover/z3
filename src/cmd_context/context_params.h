/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    context_params.h

Abstract:

    Goodies for managing context parameters in the cmd_context and
    api_context

Author:

    Leonardo (leonardo) 2012-12-01

Notes:

--*/
#ifndef _CONTEXT_PARAMS_H_
#define _CONTEXT_PARAMS_H_

#include"params.h"

class context_params {
    void set_bool(bool & opt, char const * param, char const * value);
        
public:
    bool        m_auto_config;
    bool        m_proof;
    bool        m_debug_ref_count;
    bool        m_trace;
    std::string m_trace_file_name;
    bool        m_well_sorted_check;
    bool        m_model;
    bool        m_validate_model;
    bool        m_unsat_core;
    unsigned    m_timeout;
    bool        m_statistics;

    context_params();
    void set(char const * param, char const * value);
    void updt_params();
    void updt_params(params_ref const & p);
    static void collect_param_descrs(param_descrs & d);
    /*
      REG_PARAMS('context_params::collect_param_descrs')
    */
};


#endif
