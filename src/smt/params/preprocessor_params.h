/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    preprocessor_params.h

Abstract:

    Preprocess AST before adding them to the logical context

Author:

    Leonardo de Moura (leonardo) 2008-01-17.

Revision History:

--*/
#pragma once

#include "params/pattern_inference_params.h"
#include "params/bit_blaster_params.h"

enum class lift_ite_kind {
    LI_NONE,
    LI_CONSERVATIVE,
    LI_FULL
};

struct preprocessor_params : public pattern_inference_params, 
                             public bit_blaster_params {
    lift_ite_kind   m_lift_ite;
    lift_ite_kind   m_ng_lift_ite;  // lift ite for non ground terms
    bool            m_pull_cheap_ite = false;
    bool            m_pull_nested_quantifiers = false;
    bool            m_eliminate_term_ite = false;
    bool            m_macro_finder = false;
    bool            m_propagate_values = true;
    bool            m_elim_unconstrained = true;
    bool            m_solve_eqs = true;
    bool            m_refine_inj_axiom = true;
    bool            m_eliminate_bounds = false;
    bool            m_simplify_bit2int = false;
    bool            m_nnf_cnf = true;
    bool            m_distribute_forall = false;
    bool            m_reduce_args = false;
    bool            m_quasi_macros = false;
    bool            m_restricted_quasi_macros = false;
    bool            m_max_bv_sharing = true;
    bool            m_pre_simplifier = true;
    bool            m_nlquant_elim = false;
    bool            m_bound_simplifier = true;

public:
    preprocessor_params(params_ref const & p = params_ref()):
        m_lift_ite(lift_ite_kind::LI_NONE),
        m_ng_lift_ite(lift_ite_kind::LI_NONE) {
        updt_local_params(p);
    }

    void updt_local_params(params_ref const & p);

    void updt_params(params_ref const & p);

    void display(std::ostream & out) const;
};

