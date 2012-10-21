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
    p.register_int_param("ARITH_SOLVER", 0, 3, reinterpret_cast<int&>(m_arith_mode), "select arithmetic solver: 0 - no solver, 1 - bellman-ford based solver (diff. logic only), 2 - simplex based solver, 3 - floyd-warshall based solver (diff. logic only) and no theory combination");
#else
    p.register_int_param("ARITH_SOLVER", 0, 4, reinterpret_cast<int&>(m_arith_mode), "select arithmetic solver: 0 - no solver, 1 - bellman-ford based solver (diff. logic only), 2 - simplex based solver, 3 - floyd-warshall based solver (diff. logic only) and no theory combination, 4 - model guided arith_solver");
#endif
    p.register_bool_param("ARITH_FORCE_SIMPLEX", m_arith_auto_config_simplex, "force Z3 to use simplex solver.");
    p.register_unsigned_param("ARITH_BLANDS_RULE_THRESHOLD", m_arith_blands_rule_threshold);
    p.register_bool_param("ARITH_PROPAGATE_EQS", m_arith_propagate_eqs);
    p.register_int_param("ARITH_PROPAGATION_MODE", 0, 2, reinterpret_cast<int&>(m_arith_bound_prop));
    p.register_bool_param("ARITH_STRONGER_LEMMAS", m_arith_stronger_lemmas);
    p.register_bool_param("ARITH_SKIP_BIG_COEFFS", m_arith_skip_rows_with_big_coeffs);
    p.register_unsigned_param("ARITH_MAX_LEMMA_SIZE", m_arith_max_lemma_size);
    p.register_unsigned_param("ARITH_SMALL_LEMMA_SIZE", m_arith_small_lemma_size);
    p.register_bool_param("ARITH_REFLECT", m_arith_reflect);
    p.register_bool_param("ARITH_IGNORE_INT", m_arith_ignore_int);
    p.register_unsigned_param("ARITH_LAZY_PIVOTING", m_arith_lazy_pivoting_lvl);
    p.register_unsigned_param("ARITH_RANDOM_SEED", m_arith_random_seed);
    p.register_bool_param("ARITH_RANDOM_INITIAL_VALUE", m_arith_random_initial_value);
    p.register_int_param("ARITH_RANDOM_LOWER", m_arith_random_lower);
    p.register_int_param("ARITH_RANDOM_UPPER", m_arith_random_upper);
    p.register_bool_param("ARITH_ADAPTIVE", m_arith_adaptive);
    p.register_double_param("ARITH_ADAPTIVE_ASSERTION_THRESHOLD", m_arith_adaptive_assertion_threshold, "Delay arithmetic atoms if the num-arith-conflicts/total-conflicts < threshold");
    p.register_double_param("ARITH_ADAPTIVE_PROPAGATION_THRESHOLD", m_arith_adaptive_propagation_threshold, "Disable arithmetic theory propagation if the num-arith-conflicts/total-conflicts < threshold");
    p.register_bool_param("ARITH_DUMP_LEMMAS", m_arith_dump_lemmas);
    p.register_bool_param("ARITH_EAGER_EQ_AXIOMS", m_arith_eager_eq_axioms);
    p.register_unsigned_param("ARITH_BRANCH_CUT_RATIO", m_arith_branch_cut_ratio);

    p.register_bool_param("ARITH_ADD_BINARY_BOUNDS", m_arith_add_binary_bounds);
    p.register_unsigned_param("ARITH_PROP_STRATEGY", 0, 1, reinterpret_cast<unsigned&>(m_arith_propagation_strategy), "Propagation strategy: 0 - use agility measures based on ration of theory conflicts, 1 - propagate proportional to ratio of theory conflicts (default)");

    p.register_bool_param("ARITH_EQ_BOUNDS", m_arith_eq_bounds);
    p.register_bool_param("ARITH_LAZY_ADAPTER", m_arith_lazy_adapter);
    p.register_bool_param("ARITH_GCD_TEST", m_arith_gcd_test);
    p.register_bool_param("ARITH_EAGER_GCD", m_arith_eager_gcd);
    p.register_bool_param("ARITH_ADAPTIVE_GCD", m_arith_adaptive_gcd);
    p.register_unsigned_param("ARITH_PROPAGATION_THRESHOLD", m_arith_propagation_threshold);

    p.register_bool_param("NL_ARITH", m_nl_arith, "enable/disable non linear arithmetic support. This option is ignored when ARITH_SOLVER != 2.");
    p.register_bool_param("NL_ARITH_GB", m_nl_arith_gb, "enable/disable Grobner Basis computation. This option is ignored when NL_ARITH=false");
    p.register_bool_param("NL_ARITH_GB_EQS", m_nl_arith_gb_eqs, "enable/disable equations in the Grobner Basis to be copied to the Simplex tableau.");
    p.register_bool_param("NL_ARITH_GB_PERTURBATE", m_nl_arith_gb_perturbate, "enable/disable perturbation of the variable order in GB when searching for new polynomials.");
    p.register_unsigned_param("NL_ARITH_GB_THRESHOLD", m_nl_arith_gb_threshold, "Grobner basis computation can be very expensive. This is a threshold on the number of new equalities that can be generated.");
    p.register_bool_param("NL_ARITH_BRANCHING", m_nl_arith_branching, "enable/disable branching on integer variables in non linear clusters");
    p.register_unsigned_param("NL_ARITH_ROUNDS", m_nl_arith_rounds, "threshold for number of (nested) final checks for non linear arithmetic.");
    p.register_unsigned_param("NL_ARITH_MAX_DEGREE", m_nl_arith_max_degree, "max degree for internalizing new monomials.");
    PRIVATE_PARAMS({
        p.register_bool_param("ARITH_FIXNUM", m_arith_fixnum);
        p.register_bool_param("ARITH_INT_ONLY", m_arith_int_only);
        p.register_bool_param("ARITH_ENUM_CONST_MOD", m_arith_enum_const_mod, "Create axioms for the finite set of equalities for (mod x k) where k is a positive numeral constant");
        p.register_bool_param("ARITH_INT_EQ_BRANCHING",  m_arith_int_eq_branching, "Determine branch predicates based on integer equation solving");       
    });
    p.register_bool_param("ARITH_EUCLIDEAN_SOLVER", m_arith_euclidean_solver, "");
}

