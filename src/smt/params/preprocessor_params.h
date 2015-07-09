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

#include"pattern_inference_params.h"
#include"bit_blaster_params.h"
#include"bv_simplifier_params.h"
#include"arith_simplifier_params.h"

enum lift_ite_kind {
    LI_NONE,
    LI_CONSERVATIVE,
    LI_FULL
};

struct preprocessor_params : public pattern_inference_params, 
                             public bit_blaster_params, 
                             public bv_simplifier_params, 
                             public arith_simplifier_params {
    lift_ite_kind   m_lift_ite;
    lift_ite_kind   m_ng_lift_ite;  // lift ite for non ground terms
    bool            m_pull_cheap_ite_trees;
    bool            m_pull_nested_quantifiers;
    bool            m_eliminate_term_ite;
    bool            m_eliminate_and; // represent (and a b) as (not (or (not a) (not b)))
    bool            m_macro_finder;
    bool            m_propagate_values;
    bool            m_propagate_booleans;
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
        m_pull_cheap_ite_trees(false),
        m_pull_nested_quantifiers(false),
        m_eliminate_term_ite(false),
        m_eliminate_and(true),
        m_macro_finder(false),
        m_propagate_values(true),
        m_propagate_booleans(false), // TODO << check peformance
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
};

#endif /* PREPROCESSOR_PARAMS_H_ */
