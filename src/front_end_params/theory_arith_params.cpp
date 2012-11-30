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

void theory_arith_params::register_params(ini_params & p) {
#ifdef _EXTERNAL_RELEASE
    p.register_int_param("arith_solver", 0, 3, reinterpret_cast<int&>(m_arith_mode), "select arithmetic solver: 0 - no solver, 1 - bellman-ford based solver (diff. logic only), 2 - simplex based solver, 3 - floyd-warshall based solver (diff. logic only) and no theory combination");
#else
    p.register_int_param("arith_solver", 0, 4, reinterpret_cast<int&>(m_arith_mode), "select arithmetic solver: 0 - no solver, 1 - bellman-ford based solver (diff. logic only), 2 - simplex based solver, 3 - floyd-warshall based solver (diff. logic only) and no theory combination, 4 - model guided arith_solver");
#endif
    p.register_bool_param("arith_force_simplex", m_arith_auto_config_simplex, "force Z3 to use simplex solver.");
    p.register_unsigned_param("arith_blands_rule_threshold", m_arith_blands_rule_threshold);
    p.register_bool_param("arith_propagate_eqs", m_arith_propagate_eqs);
    p.register_int_param("arith_propagation_mode", 0, 2, reinterpret_cast<int&>(m_arith_bound_prop));
    p.register_bool_param("arith_stronger_lemmas", m_arith_stronger_lemmas);
    p.register_bool_param("arith_skip_big_coeffs", m_arith_skip_rows_with_big_coeffs);
    p.register_unsigned_param("arith_max_lemma_size", m_arith_max_lemma_size);
    p.register_unsigned_param("arith_small_lemma_size", m_arith_small_lemma_size);
    p.register_bool_param("arith_reflect", m_arith_reflect);
    p.register_bool_param("arith_ignore_int", m_arith_ignore_int);
    p.register_unsigned_param("arith_lazy_pivoting", m_arith_lazy_pivoting_lvl);
    p.register_unsigned_param("arith_random_seed", m_arith_random_seed);
    p.register_bool_param("arith_random_initial_value", m_arith_random_initial_value);
    p.register_int_param("arith_random_lower", m_arith_random_lower);
    p.register_int_param("arith_random_upper", m_arith_random_upper);
    p.register_bool_param("arith_adaptive", m_arith_adaptive);
    p.register_double_param("arith_adaptive_assertion_threshold", m_arith_adaptive_assertion_threshold, "Delay arithmetic atoms if the num-arith-conflicts/total-conflicts < threshold");
    p.register_double_param("arith_adaptive_propagation_threshold", m_arith_adaptive_propagation_threshold, "Disable arithmetic theory propagation if the num-arith-conflicts/total-conflicts < threshold");
    p.register_bool_param("arith_dump_lemmas", m_arith_dump_lemmas);
    p.register_bool_param("arith_eager_eq_axioms", m_arith_eager_eq_axioms);
    p.register_unsigned_param("arith_branch_cut_ratio", m_arith_branch_cut_ratio);

    p.register_bool_param("arith_add_binary_bounds", m_arith_add_binary_bounds);
    p.register_unsigned_param("arith_prop_strategy", 0, 1, reinterpret_cast<unsigned&>(m_arith_propagation_strategy), "Propagation strategy: 0 - use agility measures based on ration of theory conflicts, 1 - propagate proportional to ratio of theory conflicts (default)");

    p.register_bool_param("arith_eq_bounds", m_arith_eq_bounds);
    p.register_bool_param("arith_lazy_adapter", m_arith_lazy_adapter);
    p.register_bool_param("arith_gcd_test", m_arith_gcd_test);
    p.register_bool_param("arith_eager_gcd", m_arith_eager_gcd);
    p.register_bool_param("arith_adaptive_gcd", m_arith_adaptive_gcd);
    p.register_unsigned_param("arith_propagation_threshold", m_arith_propagation_threshold);

    p.register_bool_param("nl_arith", m_nl_arith, "enable/disable non linear arithmetic support. This option is ignored when ARITH_SOLVER != 2.");
    p.register_bool_param("nl_arith_gb", m_nl_arith_gb, "enable/disable Grobner Basis computation. This option is ignored when NL_ARITH=false");
    p.register_bool_param("nl_arith_gb_eqs", m_nl_arith_gb_eqs, "enable/disable equations in the Grobner Basis to be copied to the Simplex tableau.");
    p.register_bool_param("nl_arith_gb_perturbate", m_nl_arith_gb_perturbate, "enable/disable perturbation of the variable order in GB when searching for new polynomials.");
    p.register_unsigned_param("nl_arith_gb_threshold", m_nl_arith_gb_threshold, "Grobner basis computation can be very expensive. This is a threshold on the number of new equalities that can be generated.");
    p.register_bool_param("nl_arith_branching", m_nl_arith_branching, "enable/disable branching on integer variables in non linear clusters");
    p.register_unsigned_param("nl_arith_rounds", m_nl_arith_rounds, "threshold for number of (nested) final checks for non linear arithmetic.");
    p.register_unsigned_param("nl_arith_max_degree", m_nl_arith_max_degree, "max degree for internalizing new monomials.");
    PRIVATE_PARAMS({
        p.register_bool_param("arith_fixnum", m_arith_fixnum);
        p.register_bool_param("arith_int_only", m_arith_int_only);
        p.register_bool_param("arith_enum_const_mod", m_arith_enum_const_mod, "Create axioms for the finite set of equalities for (mod x k) where k is a positive numeral constant");
        p.register_bool_param("arith_int_eq_branching",  m_arith_int_eq_branching, "Determine branch predicates based on integer equation solving");       
    });
    p.register_bool_param("arith_euclidean_solver", m_arith_euclidean_solver, "");
}

