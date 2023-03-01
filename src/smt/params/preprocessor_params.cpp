/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    preprocessor_params.h

Abstract:

    Preprocess AST before adding them to the logical context

Author:

    Leonardo de Moura (leonardo) 2012-12-02.

Revision History:

--*/
#include "smt/params/preprocessor_params.h"
#include "smt/params/smt_params_helper.hpp"

void preprocessor_params::updt_local_params(params_ref const & _p) {
    smt_params_helper p(_p);
    m_macro_finder            = p.macro_finder();
    m_quasi_macros            = p.quasi_macros();
    m_restricted_quasi_macros = p.restricted_quasi_macros();
    m_pull_nested_quantifiers = p.pull_nested_quantifiers();
    m_refine_inj_axiom        = p.refine_inj_axioms();
    m_propagate_values        = p.propagate_values();
    m_elim_unconstrained      = p.elim_unconstrained();
    m_solve_eqs               = p.solve_eqs();
    m_ng_lift_ite             = static_cast<lift_ite_kind>(p.q_lift_ite());
    m_bound_simplifier        = p.bound_simplifier();
}

void preprocessor_params::updt_params(params_ref const & p) {
    pattern_inference_params::updt_params(p);
    updt_local_params(p);
}

#define DISPLAY_PARAM(X) out << #X"=" << X << '\n';

void preprocessor_params::display(std::ostream & out) const {
    pattern_inference_params::display(out);
    bit_blaster_params::display(out);

    DISPLAY_PARAM((int)m_lift_ite);
    DISPLAY_PARAM((int)m_ng_lift_ite);
    DISPLAY_PARAM(m_pull_cheap_ite);
    DISPLAY_PARAM(m_pull_nested_quantifiers);
    DISPLAY_PARAM(m_eliminate_term_ite);
    DISPLAY_PARAM(m_macro_finder);
    DISPLAY_PARAM(m_propagate_values);
    DISPLAY_PARAM(m_solve_eqs);
    DISPLAY_PARAM(m_elim_unconstrained);
    DISPLAY_PARAM(m_refine_inj_axiom);
    DISPLAY_PARAM(m_eliminate_bounds);
    DISPLAY_PARAM(m_simplify_bit2int);
    DISPLAY_PARAM(m_nnf_cnf);
    DISPLAY_PARAM(m_distribute_forall);
    DISPLAY_PARAM(m_reduce_args);
    DISPLAY_PARAM(m_quasi_macros);
    DISPLAY_PARAM(m_restricted_quasi_macros);
    DISPLAY_PARAM(m_max_bv_sharing);
    DISPLAY_PARAM(m_pre_simplifier);
    DISPLAY_PARAM(m_nlquant_elim);
    DISPLAY_PARAM(m_bound_simplifier);
}
