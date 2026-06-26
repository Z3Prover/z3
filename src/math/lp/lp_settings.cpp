/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:

    Lev Nachmanson (levnach)

Revision History:


--*/
#include "math/lp/lp_params_helper.hpp"
#include <memory>
#include "util/vector.h"
#include "params/smt_params_helper.hpp"
#include "math/lp/lp_settings_def.h"
template bool lp::vectors_are_equal<lp::mpq>(vector<lp::mpq > const&, vector<lp::mpq> const&);

void lp::lp_settings::updt_params(params_ref const& _p) {
    smt_params_helper p(_p);
    lp_params_helper lp_p(_p);
    m_enable_hnf = p.arith_enable_hnf();
    m_propagate_eqs = p.arith_propagate_eqs();
    print_statistics = p.arith_print_stats();
    m_print_external_var_name = p.arith_print_ext_var_names();
    report_frequency = p.arith_rep_freq();
    m_simplex_strategy = static_cast<lp::simplex_strategy_enum>(p.arith_simplex_strategy());
    m_nlsat_delay = p.arith_nl_delay();
    auto eps = p.arith_epsilon();
    m_epsilon = rational(std::max(1, (int)(100000*eps)), 100000); 
    m_dio = lp_p.dio();
    m_dio_cuts_enable_gomory = lp_p.dio_cuts_enable_gomory();
    m_dio_gomory_enable_period = lp_p.dio_gomory_enable_period();
    m_dio_enable_hnf_cuts = lp_p.dio_cuts_enable_hnf();
    m_dump_bound_lemmas = p.arith_dump_bound_lemmas();
    m_dio_ignore_big_nums = lp_p.dio_ignore_big_nums();
    m_dio_calls_period = lp_p.dio_calls_period();
    m_dio_calls_period_decrease = lp_p.dio_calls_period_decrease();
    m_dio_run_gcd = lp_p.dio_run_gcd();
    m_random_hammers = lp_p.random_hammers();
    m_lcube = lp_p.lcube();
    m_lcube_flips = lp_p.lcube_flips();
    m_gomory_cut_efficacy_filter = lp_p.gomory_cut_efficacy_filter();
    m_gomory_cut_efficacy_threshold = lp_p.gomory_cut_efficacy_threshold();
    m_gomory_efficacy_select = lp_p.gomory_efficacy_select();
    m_gomory_candidate_rows = lp_p.gomory_candidate_rows();
    m_gomory_efficacy_augment = lp_p.gomory_efficacy_augment();
    m_gomory_cut_orthogonality = lp_p.gomory_cut_orthogonality();
    m_gomory_recent_cuts = lp_p.gomory_recent_cuts();
    m_gomory_parallelism_threshold = lp_p.gomory_parallelism_threshold();
    unsigned hammer_period = lp_p.int_hammer_period();
    SASSERT(hammer_period != 0);
    m_int_find_cube_period = hammer_period;
    m_int_gomory_cut_period = hammer_period;
    m_hnf_cut_period = hammer_period;
    m_max_conflicts = p.max_conflicts();
}
