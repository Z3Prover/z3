/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    theory_arith_params.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-05-06.

Revision History:

--*/
#ifndef THEORY_ARITH_PARAMS_H_
#define THEORY_ARITH_PARAMS_H_

#include<limits.h>
#include"params.h"

enum arith_solver_id {
    AS_NO_ARITH,
    AS_DIFF_LOGIC,
    AS_ARITH,
    AS_DENSE_DIFF_LOGIC,
    AS_UTVPI,
    AS_OPTINF
};

enum bound_prop_mode {
    BP_NONE,
    BP_SIMPLE, // only used for implying literals   
    BP_REFINE  // refine known bounds
};

enum arith_prop_strategy {
    ARITH_PROP_AGILITY,
    ARITH_PROP_PROPORTIONAL
};

enum arith_pivot_strategy {
    ARITH_PIVOT_SMALLEST,
    ARITH_PIVOT_GREATEST_ERROR,
    ARITH_PIVOT_LEAST_ERROR
};

struct theory_arith_params {
    arith_solver_id         m_arith_mode;
    bool                    m_arith_auto_config_simplex; //!< force simplex solver in auto_config
    unsigned                m_arith_blands_rule_threshold;
    bool                    m_arith_propagate_eqs;
    bound_prop_mode         m_arith_bound_prop; 
    bool                    m_arith_stronger_lemmas;
    bool                    m_arith_skip_rows_with_big_coeffs;
    unsigned                m_arith_max_lemma_size; 
    unsigned                m_arith_small_lemma_size;
    bool                    m_arith_reflect;
    bool                    m_arith_ignore_int;
    unsigned                m_arith_lazy_pivoting_lvl;
    unsigned                m_arith_random_seed;
    bool                    m_arith_random_initial_value;
    int                     m_arith_random_lower;
    int                     m_arith_random_upper;
    bool                    m_arith_adaptive;
    double                  m_arith_adaptive_assertion_threshold;
    double                  m_arith_adaptive_propagation_threshold;
    bool                    m_arith_dump_lemmas;
    bool                    m_arith_eager_eq_axioms;
    unsigned                m_arith_branch_cut_ratio;
    bool                    m_arith_int_eq_branching;
    bool                    m_arith_enum_const_mod;

    bool                    m_arith_gcd_test;
    bool                    m_arith_eager_gcd;
    bool                    m_arith_adaptive_gcd;
    unsigned                m_arith_propagation_threshold;

    arith_pivot_strategy    m_arith_pivot_strategy;

    // used in diff-logic
    bool                    m_arith_add_binary_bounds;
    arith_prop_strategy     m_arith_propagation_strategy;

    // used arith_eq_adapter
    bool                    m_arith_eq_bounds;
    bool                    m_arith_lazy_adapter;

    // performance debugging flags
    bool                    m_arith_fixnum;
    bool                    m_arith_int_only;

    // non linear support
    bool                    m_nl_arith;  
    bool                    m_nl_arith_gb;
    unsigned                m_nl_arith_gb_threshold;
    bool                    m_nl_arith_gb_eqs;
    bool                    m_nl_arith_gb_perturbate;
    unsigned                m_nl_arith_max_degree;
    bool                    m_nl_arith_branching;
    unsigned                m_nl_arith_rounds;

    // euclidean solver for tighting bounds 
    bool                    m_arith_euclidean_solver;


    theory_arith_params(params_ref const & p = params_ref()):
        m_arith_mode(AS_ARITH),
        m_arith_auto_config_simplex(false),
        m_arith_blands_rule_threshold(1000),
        m_arith_propagate_eqs(true),
        m_arith_bound_prop(BP_REFINE),
        m_arith_stronger_lemmas(true),
        m_arith_skip_rows_with_big_coeffs(true),
        m_arith_max_lemma_size(128),
        m_arith_small_lemma_size(16),
        m_arith_reflect(true),
        m_arith_ignore_int(false),
        m_arith_lazy_pivoting_lvl(0),
        m_arith_random_seed(0),
        m_arith_random_initial_value(false),
        m_arith_random_lower(-1000),
        m_arith_random_upper(1000),
        m_arith_adaptive(false),
        m_arith_adaptive_assertion_threshold(0.2),
        m_arith_adaptive_propagation_threshold(0.4),
        m_arith_dump_lemmas(false),
        m_arith_eager_eq_axioms(true),
        m_arith_branch_cut_ratio(2),
        m_arith_int_eq_branching(false),
        m_arith_enum_const_mod(false),
        m_arith_gcd_test(true),
        m_arith_eager_gcd(false),
        m_arith_adaptive_gcd(false),
        m_arith_propagation_threshold(UINT_MAX),
        m_arith_pivot_strategy(ARITH_PIVOT_SMALLEST),
        m_arith_add_binary_bounds(false),
        m_arith_propagation_strategy(ARITH_PROP_PROPORTIONAL),
        m_arith_eq_bounds(false),
        m_arith_lazy_adapter(false),
        m_arith_fixnum(false),
        m_arith_int_only(false),
        m_nl_arith(true),
        m_nl_arith_gb(true),
        m_nl_arith_gb_threshold(512),
        m_nl_arith_gb_eqs(false),
        m_nl_arith_gb_perturbate(true),
        m_nl_arith_max_degree(6),
        m_nl_arith_branching(true),
        m_nl_arith_rounds(1024),
        m_arith_euclidean_solver(false) {
        updt_params(p);
    }

    void updt_params(params_ref const & p);
};

#endif /* THEORY_ARITH_PARAMS_H_ */

