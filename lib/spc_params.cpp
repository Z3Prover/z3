/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_params.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-08.

Revision History:

--*/
#include"spc_params.h"

void spc_params::register_params(ini_params & p) {
    order_params::register_params(p);
    p.register_unsigned_param("SPC_MIN_FUNC_FREQ_SUBSUMPTION_INDEX",m_min_func_freq_subsumption_index,
                              "minimal number of occurrences (in clauses) for a function symbol to be considered for subsumption indexing.");
    p.register_unsigned_param("SPC_MAX_SUBSUMPTION_INDEX_FEATURES", m_max_subsumption_index_features,
                              "maximum number of features to be used for subsumption index.");
    p.register_unsigned_param("SPC_INITIAL_SUBSUMPTION_INDEX_OPT", m_initial_subsumption_index_opt,
                              "after how many processed clauses the subsumption index is optimized.");
    p.register_double_param("SPC_FACTOR_SUBSUMPTION_INDEX_OPT", m_factor_subsumption_index_opt,
                            "after each optimization the threshold for optimization is increased by this factor. See INITIAL_SUBSUMPTION_INDEX_OPT.");
    p.register_bool_param("SPC_BS", m_backward_subsumption, "Enable/disable backward subsumption in the superposition engine");
    p.register_bool_param("SPC_ES", m_equality_subsumption, "Enable/disable equality resolution in the superposition engine");
    p.register_unsigned_param("SPC_NUM_ITERATIONS", m_spc_num_iterations);
    p.register_bool_param("SPC_TRACE", m_spc_trace);
}


