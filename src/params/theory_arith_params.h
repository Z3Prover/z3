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
#pragma once

#include<climits>
#include "util/params.h"

enum class arith_solver_id {
    AS_NO_ARITH,              // 0
    AS_DIFF_LOGIC,            // 1
    AS_OLD_ARITH,             // 2
    AS_DENSE_DIFF_LOGIC,      // 3
    AS_UTVPI,                 // 4
    AS_OPTINF,                // 5
    AS_NEW_ARITH              // 6
};

enum class bound_prop_mode {
    BP_NONE,
    BP_SIMPLE, // only used for implying literals   
    BP_REFINE  // adds new literals, but only refines finite bounds
};

enum class arith_prop_strategy {
    ARITH_PROP_AGILITY,
    ARITH_PROP_PROPORTIONAL
};

enum class arith_pivot_strategy {
    ARITH_PIVOT_SMALLEST,
    ARITH_PIVOT_GREATEST_ERROR,
    ARITH_PIVOT_LEAST_ERROR
};

inline std::ostream& operator<<(std::ostream& out, arith_pivot_strategy st) { return out << (int)st; }

struct theory_arith_params {
    bool                    m_arith_eq2ineq = false;
    bool                    m_arith_process_all_eqs = false;
    arith_solver_id         m_arith_mode = arith_solver_id::AS_NEW_ARITH;
    bool                    m_arith_auto_config_simplex = false; //!< force simplex solver in auto_config
    unsigned                m_arith_blands_rule_threshold = 1000;
    bool                    m_arith_propagate_eqs = true;
    bound_prop_mode         m_arith_bound_prop = bound_prop_mode::BP_REFINE;
    bool                    m_arith_stronger_lemmas = true;
    bool                    m_arith_skip_rows_with_big_coeffs = true;
    unsigned                m_arith_max_lemma_size = 128; 
    unsigned                m_arith_small_lemma_size = 16;
    bool                    m_arith_reflect = true;
    bool                    m_arith_ignore_int = false;
    unsigned                m_arith_lazy_pivoting_lvl = 0;
    unsigned                m_arith_random_seed = 0;
    bool                    m_arith_random_initial_value = false;
    int                     m_arith_random_lower = -1000;
    int                     m_arith_random_upper = 1000;
    bool                    m_arith_adaptive = false;
    double                  m_arith_adaptive_assertion_threshold = 0.2;
    double                  m_arith_adaptive_propagation_threshold = 0.4;
    bool                    m_arith_eager_eq_axioms = true;
    unsigned                m_arith_branch_cut_ratio = 2;
    bool                    m_arith_int_eq_branching = false;
    bool                    m_arith_enum_const_mod = false;

    bool                    m_arith_gcd_test = true;
    bool                    m_arith_eager_gcd = false;
    bool                    m_arith_adaptive_gcd = false;
    unsigned                m_arith_propagation_threshold = UINT_MAX;

    bool                    m_arith_validate = false;
    bool                    m_arith_dump_lemmas = false;
    arith_pivot_strategy    m_arith_pivot_strategy = arith_pivot_strategy::ARITH_PIVOT_SMALLEST;

    // used in diff-logic
    bool                    m_arith_add_binary_bounds = false;
    arith_prop_strategy     m_arith_propagation_strategy = arith_prop_strategy::ARITH_PROP_PROPORTIONAL;

    // used arith_eq_adapter
    bool                    m_arith_eq_bounds = false;
    bool                    m_arith_lazy_adapter = false;

    // performance debugging flags
    bool                    m_arith_fixnum = false;
    bool                    m_arith_int_only = false;

    // non linear support
    bool                    m_nl_arith = true;  
    bool                    m_nl_arith_gb = true;
    unsigned                m_nl_arith_gb_threshold = 512;
    bool                    m_nl_arith_gb_eqs = false;
    bool                    m_nl_arith_gb_perturbate = true;
    unsigned                m_nl_arith_max_degree = 6;
    bool                    m_nl_arith_branching = true;
    unsigned                m_nl_arith_rounds = 1024;
    bool                    m_nl_arith_propagate_linear_monomials = true;
    bool                    m_nl_arith_optimize_bounds = true;
    bool                    m_nl_arith_cross_nested = true;

    theory_arith_params(params_ref const & p = params_ref()) {
        updt_params(p);
    }

    void updt_params(params_ref const & p);

    void display(std::ostream & out) const;
};


