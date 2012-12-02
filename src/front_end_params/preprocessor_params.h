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
#ifndef _PREPROCESSOR_PARAMS_H_
#define _PREPROCESSOR_PARAMS_H_

#include"pattern_inference_params.h"
#include"bit_blaster_params.h"
#include"bv_simplifier_params.h"

enum lift_ite_kind {
    LI_NONE,
    LI_CONSERVATIVE,
    LI_FULL
};

struct preprocessor_params : public pattern_inference_params, 
                             public bit_blaster_params, public bv_simplifier_params {
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
    preprocessor_params():
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
    }

#if 0
    void register_params(ini_params & p) {
        pattern_inference_params::register_params(p);
        bit_blaster_params::register_params(p);
        bv_simplifier_params::register_params(p);
        p.register_int_param("lift_ite", 0, 2, reinterpret_cast<int&>(m_lift_ite), "ite term lifting: 0 - no lifting, 1 - conservative, 2 - full");
        p.register_int_param("ng_lift_ite", 0, 2, reinterpret_cast<int&>(m_ng_lift_ite), "ite (non-ground) term lifting: 0 - no lifting, 1 - conservative, 2 - full");
        p.register_bool_param("elim_term_ite", m_eliminate_term_ite, "eliminate term if-then-else in the preprocessor");
        p.register_bool_param("elim_and", m_eliminate_and, "represent (and a b) as (not (or (not a) (not b)))");
        p.register_bool_param("macro_finder", m_macro_finder, "try to find universally quantified formulas that can be viewed as macros");
        p.register_bool_param("propagate_values", m_propagate_values, "propagate values during preprocessing step");
        p.register_bool_param("propagate_booleans", m_propagate_booleans, "propagate boolean values during preprocessing step");
        p.register_bool_param("pull_cheap_ite_trees", m_pull_cheap_ite_trees);
        p.register_bool_param("pull_nested_quantifiers", m_pull_nested_quantifiers, "eliminate nested quantifiers by moving nested quantified variables to the outermost quantifier, it is unnecessary if the formula is converted into CNF");
        p.register_bool_param("refine_inj_axiom", m_refine_inj_axiom);
        p.register_bool_param("elim_bounds", m_eliminate_bounds, "cheap Fourier-Motzkin");

        p.register_bool_param("bit2int", m_simplify_bit2int, "hoist bit2int conversions over arithmetical expressions");
        p.register_bool_param("distribute_forall", m_distribute_forall);
        p.register_bool_param("reduce_args", m_reduce_args);
        p.register_bool_param("quasi_macros", m_quasi_macros);
        p.register_bool_param("restricted_quasi_macros", m_restricted_quasi_macros);
        p.register_bool_param("bv_max_sharing", m_max_bv_sharing);
        p.register_bool_param("pre_simplifier", m_pre_simplifier);
    }
#endif

};

#endif /* _PREPROCESSOR_PARAMS_H_ */
