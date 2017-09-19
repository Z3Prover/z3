/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    pattern_inference_params.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-03-24.

Revision History:

--*/
#ifndef PATTERN_INFERENCE_PARAMS_H_
#define PATTERN_INFERENCE_PARAMS_H_

#include "util/params.h"

enum arith_pattern_inference_kind {
    AP_NO,           // do not infer patterns with arithmetic terms
    AP_CONSERVATIVE, // only infer patterns with arithmetic terms if there is no other option
    AP_FULL          // always use patterns with arithmetic terms
};

struct pattern_inference_params {
    unsigned                      m_pi_max_multi_patterns; 
    bool                          m_pi_block_loop_patterns; 
    arith_pattern_inference_kind  m_pi_arith;
    bool                          m_pi_use_database;
    unsigned                      m_pi_arith_weight;
    unsigned                      m_pi_non_nested_arith_weight;
    bool                          m_pi_pull_quantifiers;
    int                           m_pi_nopat_weight;
    bool                          m_pi_avoid_skolems;
    bool                          m_pi_warnings;
    
    pattern_inference_params(params_ref const & p = params_ref()):
        m_pi_nopat_weight(-1),
        m_pi_avoid_skolems(true) {
        updt_params(p);
    }

    void updt_params(params_ref const & _p);

    void display(std::ostream & out) const;
};

#endif /* PATTERN_INFERENCE_PARAMS_H_ */

