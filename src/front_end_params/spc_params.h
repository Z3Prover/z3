/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_params.h

Abstract:

    Parameters for the Superposition Calculus Engine

Author:

    Leonardo de Moura (leonardo) 2008-02-08.

Revision History:

--*/
#ifndef _SPC_PARAMS_H_
#define _SPC_PARAMS_H_

#include"order_params.h"

struct spc_params : public order_params {
    unsigned m_min_func_freq_subsumption_index;
    unsigned m_max_subsumption_index_features;
    unsigned m_initial_subsumption_index_opt; 
    double   m_factor_subsumption_index_opt;
    bool     m_backward_subsumption;
    bool     m_equality_subsumption;
    unsigned m_spc_num_iterations;
    bool     m_spc_trace;

    spc_params():
        m_min_func_freq_subsumption_index(100),
        m_max_subsumption_index_features(32),
        m_initial_subsumption_index_opt(1000),
        m_factor_subsumption_index_opt(1.5),
        m_backward_subsumption(true),
        m_equality_subsumption(true),
        m_spc_num_iterations(1000),
        m_spc_trace(false) {
    }
    
    void register_params(ini_params & p);
};

#endif /* _SPC_PARAMS_H_ */

