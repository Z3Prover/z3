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
#ifndef PREPROCESSOR_PARAMS_H_
#define PREPROCESSOR_PARAMS_H_

#include "ast/pattern/pattern_inference_params.h"
#include "ast/rewriter/bit_blaster/bit_blaster_params.h"

enum lift_ite_kind {
    LI_NONE,
    LI_CONSERVATIVE,
    LI_FULL
};

struct preprocessor_params : public pattern_inference_params, 
                             public bit_blaster_params {
    lift_ite_kind   m_lift_ite;
    lift_ite_kind   m_ng_lift_ite;  // lift ite for non ground terms
    bool            m_pull_cheap_ite;
    bool            m_pull_nested_quantifiers;
    bool            m_eliminate_term_ite;
    bool            m_macro_finder;
    bool            m_propagate_values;
    bool            m_refine_inj_axiom;
    bool            m_eliminate_bounds;
    bool            m_simplify_bit2int;
    bool            m_nnf_cnf;
    bool            m_distribute_forall;
    bool            m_reduce_args;
    bool            m_quasi_macros;
    bool            m_restricted_quasi_macros;
    bool            m_max_bv_sharing;
    bool            m_pre_simplifier;
    bool            m_nlquant_elim;

public:
    preprocessor_params(params_ref const & p = params_ref()):
        m_lift_ite(LI_NONE),
        m_ng_lift_ite(LI_NONE), 
        m_pull_cheap_ite(false),
        m_pull_nested_quantifiers(false),
        m_eliminate_term_ite(false),
        m_macro_finder(false),
        m_propagate_values(true),
        m_refine_inj_axiom(true),
        m_eliminate_bounds(false),
        m_simplify_bit2int(false),
        m_nnf_cnf(true),
        m_distribute_forall(false),
        m_reduce_args(false),
        m_quasi_macros(false),
        m_restricted_quasi_macros(false),
        m_max_bv_sharing(true),
        m_pre_simplifier(true),
        m_nlquant_elim(false) {
        updt_local_params(p);
    }

    void updt_local_params(params_ref const & p);

    void updt_params(params_ref const & p);

    void display(std::ostream & out) const;
};

#endif /* PREPROCESSOR_PARAMS_H_ */
