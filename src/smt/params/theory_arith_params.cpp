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
#include "smt/params/theory_arith_params.h"
#include "smt/params/smt_params_helper.hpp"
#include "params/arith_rewriter_params.hpp"

void theory_arith_params::updt_params(params_ref const & _p) {
    smt_params_helper p(_p);
    m_arith_random_initial_value = p.arith_random_initial_value();
    m_arith_random_seed = p.random_seed();
    m_arith_mode = static_cast<arith_solver_id>(p.arith_solver());
    m_nl_arith = p.arith_nl();
    m_nl_arith_gb = p.arith_nl_grobner();
    m_nl_arith_branching = p.arith_nl_branching();
    m_nl_arith_rounds = p.arith_nl_rounds();
    m_arith_propagate_eqs = p.arith_propagate_eqs();
    m_arith_branch_cut_ratio = p.arith_branch_cut_ratio();
    m_arith_int_eq_branching = p.arith_int_eq_branch();
    m_arith_ignore_int = p.arith_ignore_int();
    m_arith_bound_prop = static_cast<bound_prop_mode>(p.arith_propagation_mode());
    m_arith_dump_lemmas = p.arith_dump_lemmas();
    m_arith_reflect = p.arith_reflect();
    m_arith_eager_eq_axioms = p.arith_eager_eq_axioms();
    m_arith_auto_config_simplex = p.arith_auto_config_simplex();

    arith_rewriter_params ap(_p);
    m_arith_eq2ineq = ap.eq2ineq();
}


#define DISPLAY_PARAM(X) out << #X"=" << X << std::endl;

void theory_arith_params::display(std::ostream & out) const {
    DISPLAY_PARAM(m_arith_eq2ineq);
    DISPLAY_PARAM(m_arith_process_all_eqs);
    DISPLAY_PARAM((unsigned)m_arith_mode);
    DISPLAY_PARAM(m_arith_auto_config_simplex); //!< force simplex solver in auto_config
    DISPLAY_PARAM(m_arith_blands_rule_threshold);
    DISPLAY_PARAM(m_arith_propagate_eqs);
    DISPLAY_PARAM((unsigned)m_arith_bound_prop);
    DISPLAY_PARAM(m_arith_stronger_lemmas);
    DISPLAY_PARAM(m_arith_skip_rows_with_big_coeffs);
    DISPLAY_PARAM(m_arith_max_lemma_size);
    DISPLAY_PARAM(m_arith_small_lemma_size);
    DISPLAY_PARAM(m_arith_reflect);
    DISPLAY_PARAM(m_arith_ignore_int);
    DISPLAY_PARAM(m_arith_lazy_pivoting_lvl);
    DISPLAY_PARAM(m_arith_random_seed);
    DISPLAY_PARAM(m_arith_random_initial_value);
    DISPLAY_PARAM(m_arith_random_lower);
    DISPLAY_PARAM(m_arith_random_upper);
    DISPLAY_PARAM(m_arith_adaptive);
    DISPLAY_PARAM(m_arith_adaptive_assertion_threshold);
    DISPLAY_PARAM(m_arith_adaptive_propagation_threshold);
    DISPLAY_PARAM(m_arith_dump_lemmas);
    DISPLAY_PARAM(m_arith_eager_eq_axioms);
    DISPLAY_PARAM(m_arith_branch_cut_ratio);
    DISPLAY_PARAM(m_arith_int_eq_branching);
    DISPLAY_PARAM(m_arith_enum_const_mod);
    DISPLAY_PARAM(m_arith_gcd_test);
    DISPLAY_PARAM(m_arith_eager_gcd);
    DISPLAY_PARAM(m_arith_adaptive_gcd);
    DISPLAY_PARAM(m_arith_propagation_threshold);
    DISPLAY_PARAM(m_arith_pivot_strategy);
    DISPLAY_PARAM(m_arith_add_binary_bounds);
    DISPLAY_PARAM((unsigned)m_arith_propagation_strategy);
    DISPLAY_PARAM(m_arith_eq_bounds);
    DISPLAY_PARAM(m_arith_lazy_adapter);
    DISPLAY_PARAM(m_arith_fixnum);
    DISPLAY_PARAM(m_arith_int_only);
    DISPLAY_PARAM(m_nl_arith);
    DISPLAY_PARAM(m_nl_arith_gb);
    DISPLAY_PARAM(m_nl_arith_gb_threshold);
    DISPLAY_PARAM(m_nl_arith_gb_eqs);
    DISPLAY_PARAM(m_nl_arith_gb_perturbate);
    DISPLAY_PARAM(m_nl_arith_max_degree);
    DISPLAY_PARAM(m_nl_arith_branching);
    DISPLAY_PARAM(m_nl_arith_rounds);
}
