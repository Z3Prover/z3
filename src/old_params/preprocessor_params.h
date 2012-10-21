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

#include"nnf_params.h"
#include"cnf_params.h"
#include"pattern_inference_params.h"
#include"bit_blaster_params.h"
#include"bv_simplifier_params.h"

enum lift_ite_kind {
    LI_NONE,
    LI_CONSERVATIVE,
    LI_FULL
};

enum q_arith_kind {
    QA_NONE,
    QA_COOPER,
    QA_OMEGA,
    QA_ALTERNATE
};

struct preprocessor_params : public nnf_params, public cnf_params, public pattern_inference_params, 
                             public bit_blaster_params, public bv_simplifier_params {
    lift_ite_kind   m_lift_ite;
    lift_ite_kind   m_ng_lift_ite;  // lift ite for non ground terms
    bool            m_pull_cheap_ite_trees;
    bool            m_pull_nested_quantifiers;
    bool            m_eliminate_term_ite;
    bool            m_eliminate_and; // represent (and a b) as (not (or (not a) (not b)))
    bool            m_reverse_implies; // translate (implies a b) into (or b (not a))
    bool            m_macro_finder;
    bool            m_solver;
    bool            m_propagate_values;
    bool            m_propagate_booleans;
    bool            m_context_simplifier;
    bool            m_strong_context_simplifier;
    bool            m_refine_inj_axiom;
    bool            m_eliminate_bounds;
    bool            m_quant_elim;
    bool            m_nlquant_elim;
    bool            m_der;
    bool            m_simplify_bit2int;
    bool            m_nnf_cnf;
    bool            m_distribute_forall;
    bool            m_reduce_args;
    bool            m_pre_demod;
    bool            m_quasi_macros;
    bool            m_restricted_quasi_macros;
    bool            m_max_bv_sharing;
    bool            m_pre_simplifier;

public:
    preprocessor_params():
        m_lift_ite(LI_NONE),
        m_ng_lift_ite(LI_NONE), 
        m_pull_cheap_ite_trees(false),
        m_pull_nested_quantifiers(false),
        m_eliminate_term_ite(false),
        m_eliminate_and(true),
        m_macro_finder(false),
        m_solver(false),
        m_propagate_values(true),
        m_propagate_booleans(false), // TODO << check peformance
        m_context_simplifier(false),
        m_strong_context_simplifier(false),
        m_refine_inj_axiom(true),
        m_eliminate_bounds(false),
        m_quant_elim(false),
        m_nlquant_elim(false),
        m_der(false),
        m_simplify_bit2int(false),
        m_nnf_cnf(true),
        m_distribute_forall(false),
        m_reduce_args(false),
        m_pre_demod(false),
        m_quasi_macros(false),
        m_restricted_quasi_macros(false),
        m_max_bv_sharing(true),
        m_pre_simplifier(true) {
    }

    void register_params(ini_params & p) {
        nnf_params::register_params(p);
        cnf_params::register_params(p);
        pattern_inference_params::register_params(p);
        bit_blaster_params::register_params(p);
        bv_simplifier_params::register_params(p);
        p.register_int_param("LIFT_ITE", 0, 2, reinterpret_cast<int&>(m_lift_ite), "ite term lifting: 0 - no lifting, 1 - conservative, 2 - full");
        p.register_int_param("NG_LIFT_ITE", 0, 2, reinterpret_cast<int&>(m_ng_lift_ite), "ite (non-ground) term lifting: 0 - no lifting, 1 - conservative, 2 - full");
        p.register_bool_param("ELIM_TERM_ITE", m_eliminate_term_ite, "eliminate term if-then-else in the preprocessor");
        p.register_bool_param("ELIM_AND", m_eliminate_and, "represent (and a b) as (not (or (not a) (not b)))");
        p.register_bool_param("MACRO_FINDER", m_macro_finder, "try to find universally quantified formulas that can be viewed as macros");
        p.register_bool_param("SOLVER", m_solver, "enable solver during preprocessing step", true);
        p.register_bool_param("PROPAGATE_VALUES", m_propagate_values, "propagate values during preprocessing step");
        p.register_bool_param("PROPAGATE_BOOLEANS", m_propagate_booleans, "propagate boolean values during preprocessing step");
        p.register_bool_param("PULL_CHEAP_ITE_TREES", m_pull_cheap_ite_trees);
        p.register_bool_param("PULL_NESTED_QUANTIFIERS", m_pull_nested_quantifiers, "eliminate nested quantifiers by moving nested quantified variables to the outermost quantifier, it is unnecessary if the formula is converted into CNF");
        p.register_bool_param("CONTEXT_SIMPLIFIER", m_context_simplifier, 
                              "Simplify Boolean sub-expressions if they already appear in context", true);
        p.register_bool_param("STRONG_CONTEXT_SIMPLIFIER", m_strong_context_simplifier, 
                              "Simplify Boolean sub-expressions by using full satisfiability queries", true);
        p.register_bool_param("REFINE_INJ_AXIOM", m_refine_inj_axiom);
        p.register_bool_param("ELIM_BOUNDS", m_eliminate_bounds, "cheap Fourier-Motzkin");

        p.register_bool_param("ELIM_QUANTIFIERS", m_quant_elim, 
                              "Use quantifier elimination procedures on Boolean, Bit-vector, Arithmetic and Array variables", true);
        p.register_bool_param("ELIM_NLARITH_QUANTIFIERS", m_nlquant_elim, 
                              "Eliminate non-linear quantifiers", true);
        p.register_bool_param("DER", m_der);
        p.register_bool_param("BIT2INT", m_simplify_bit2int, "hoist bit2int conversions over arithmetical expressions");
        p.register_bool_param("DISTRIBUTE_FORALL", m_distribute_forall);
        p.register_bool_param("REDUCE_ARGS", m_reduce_args);
        p.register_bool_param("PRE_DEMODULATOR", m_pre_demod, "apply demodulators during preprocessing step");
        p.register_bool_param("QUASI_MACROS", m_quasi_macros);
        p.register_bool_param("RESTRICTED_QUASI_MACROS", m_restricted_quasi_macros);
        p.register_bool_param("BV_MAX_SHARING", m_max_bv_sharing);
        p.register_bool_param("PRE_SIMPLIFIER", m_pre_simplifier);
    }
};

#endif /* _PREPROCESSOR_PARAMS_H_ */
