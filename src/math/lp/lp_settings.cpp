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
#include "smt/params/smt_params_helper.hpp"
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
    m_dio = lp_p.dio();
    m_dio_enable_gomory_cuts = lp_p.dio_cuts_enable_gomory();
    m_dio_enable_hnf_cuts = lp_p.dio_cuts_enable_hnf();
    m_dump_bound_lemmas = p.arith_dump_bound_lemmas();
    m_dio_ignore_big_nums = lp_p.dio_ignore_big_nums();
    m_dio_calls_period = lp_p.dio_calls_period();
    m_dio_run_gcd = lp_p.dio_run_gcd();
}
