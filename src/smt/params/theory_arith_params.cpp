/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_arith_params.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-05-06.

Revision History:

--*/
#include"theory_arith_params.h"
#include"smt_params_helper.hpp"

void theory_arith_params::updt_params(params_ref const & _p) {
    smt_params_helper p(_p);
    m_arith_random_initial_value = p.arith_random_initial_value();
    m_arith_random_seed = p.random_seed();
    m_arith_mode = static_cast<arith_solver_id>(p.arith_solver());
    m_nl_arith = p.arith_nl();
    m_nl_arith_gb = p.arith_nl_gb();
    m_nl_arith_branching = p.arith_nl_branching();
    m_nl_arith_rounds = p.arith_nl_rounds();
    m_arith_euclidean_solver = p.arith_euclidean_solver();
    m_arith_propagate_eqs = p.arith_propagate_eqs();
    m_arith_branch_cut_ratio = p.arith_branch_cut_ratio();
    m_arith_int_eq_branching = p.arith_int_eq_branch();
    m_arith_ignore_int = p.arith_ignore_int();
    m_arith_bound_prop = static_cast<bound_prop_mode>(p.arith_propagation_mode());
    m_arith_dump_lemmas = p.arith_dump_lemmas();
}


