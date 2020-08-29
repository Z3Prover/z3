/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    pattern_inference_params.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2012-12-02.

Revision History:

--*/
#include "params/pattern_inference_params.h"
#include "params/pattern_inference_params_helper.hpp"

void pattern_inference_params::updt_params(params_ref const & _p) {
    pattern_inference_params_helper p(_p);
    m_pi_max_multi_patterns      = p.max_multi_patterns();
    m_pi_block_loop_patterns     = p.block_loop_patterns();
    m_pi_arith                   = static_cast<arith_pattern_inference_kind>(p.arith());
    m_pi_use_database            = p.use_database();
    m_pi_arith_weight            = p.arith_weight();
    m_pi_non_nested_arith_weight = p.non_nested_arith_weight();
    m_pi_pull_quantifiers        = p.pull_quantifiers();
    m_pi_warnings                = p.warnings();
}

#define DISPLAY_PARAM(X) out << #X"=" << X << std::endl;

void pattern_inference_params::display(std::ostream & out) const {
    DISPLAY_PARAM(m_pi_max_multi_patterns);
    DISPLAY_PARAM(m_pi_block_loop_patterns);
    DISPLAY_PARAM(m_pi_arith);
    DISPLAY_PARAM(m_pi_use_database);
    DISPLAY_PARAM(m_pi_arith_weight);
    DISPLAY_PARAM(m_pi_non_nested_arith_weight);
    DISPLAY_PARAM(m_pi_pull_quantifiers);
    DISPLAY_PARAM(m_pi_nopat_weight);
    DISPLAY_PARAM(m_pi_avoid_skolems);
    DISPLAY_PARAM(m_pi_warnings);
}
