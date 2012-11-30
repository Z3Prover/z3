/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    pattern_inference_params.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-03-24.

Revision History:

--*/
#include"pattern_inference_params.h"

void pattern_inference_params::register_params(ini_params & p) {
    p.register_unsigned_param("pi_max_multi_patterns", m_pi_max_multi_patterns, 
                              "when patterns are not provided, the prover uses a heuristic to infer them. This option sets the threshold on the number of extra multi-patterns that can be created. By default, the prover creates at most one multi-pattern when there is no unary pattern");
    p.register_bool_param("pi_block_loop_patterns", m_pi_block_loop_patterns,
                          "block looping patterns during pattern inference");
    p.register_int_param("pi_arith", 0, 2, reinterpret_cast<int&>(m_pi_arith), 
                         "0 - do not infer patterns with arithmetic terms, 1 - use patterns with arithmetic terms if there is no other pattern, 2 - always use patterns with arithmetic terms.");
    p.register_bool_param("pi_use_database", m_pi_use_database);
    p.register_unsigned_param("pi_arith_weight", m_pi_arith_weight, "default weight for quantifiers where the only available pattern has nested arithmetic terms.");
    p.register_unsigned_param("pi_non_nested_arith_weight", m_pi_non_nested_arith_weight, "default weight for quantifiers where the only available pattern has non nested arithmetic terms.");
    p.register_bool_param("pi_pull_quantifiers", m_pi_pull_quantifiers, "pull nested quantifiers, if no pattern was found.");
    p.register_int_param("pi_nopat_weight", m_pi_nopat_weight, "set weight of quantifiers without patterns, if negative the weight is not changed.");
    p.register_bool_param("pi_avoid_skolems", m_pi_avoid_skolems);
    p.register_bool_param("pi_warnings", m_pi_warnings, "enable/disable warning messages in the pattern inference module.");
}


