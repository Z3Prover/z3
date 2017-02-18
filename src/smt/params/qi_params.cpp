/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qi_params.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2012-12-02.

Revision History:

--*/
#include"qi_params.h"
#include"smt_params_helper.hpp"

void qi_params::updt_params(params_ref const & _p) {
    smt_params_helper p(_p);
    m_mbqi = p.mbqi();
    m_mbqi_max_cexs = p.mbqi_max_cexs();
    m_mbqi_max_cexs_incr = p.mbqi_max_cexs_incr();
    m_mbqi_max_iterations = p.mbqi_max_iterations();
    m_mbqi_trace = p.mbqi_trace();
    m_mbqi_force_template = p.mbqi_force_template();
    m_mbqi_id = p.mbqi_id();
    m_qi_profile = p.qi_profile();
    m_qi_profile_freq = p.qi_profile_freq();
    m_qi_max_instances = p.qi_max_instances();
    m_qi_eager_threshold = p.qi_eager_threshold();
    m_qi_lazy_threshold = p.qi_lazy_threshold();
    m_qi_cost = p.qi_cost();
    m_qi_max_eager_multipatterns = p.qi_max_multi_patterns();
}

#define DISPLAY_PARAM(X) out << #X"=" << X << std::endl;

void qi_params::display(std::ostream & out) const {
    DISPLAY_PARAM(m_qi_ematching);
    DISPLAY_PARAM(m_qi_cost);
    DISPLAY_PARAM(m_qi_new_gen);
    DISPLAY_PARAM(m_qi_eager_threshold);
    DISPLAY_PARAM(m_qi_lazy_threshold);
    DISPLAY_PARAM(m_qi_max_eager_multipatterns);
    DISPLAY_PARAM(m_qi_max_lazy_multipattern_matching);
    DISPLAY_PARAM(m_qi_profile);
    DISPLAY_PARAM(m_qi_profile_freq);
    DISPLAY_PARAM(m_qi_quick_checker);
    DISPLAY_PARAM(m_qi_lazy_quick_checker);
    DISPLAY_PARAM(m_qi_promote_unsat);
    DISPLAY_PARAM(m_qi_max_instances);
    DISPLAY_PARAM(m_qi_lazy_instantiation);
    DISPLAY_PARAM(m_qi_conservative_final_check);
    DISPLAY_PARAM(m_mbqi);
    DISPLAY_PARAM(m_mbqi_max_cexs);
    DISPLAY_PARAM(m_mbqi_max_cexs_incr);
    DISPLAY_PARAM(m_mbqi_max_iterations);
    DISPLAY_PARAM(m_mbqi_trace);
    DISPLAY_PARAM(m_mbqi_force_template);
    DISPLAY_PARAM(m_mbqi_id);
}
