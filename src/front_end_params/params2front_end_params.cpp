/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    params2front_end_params.h

Abstract:

    Backward compatibility utilities for parameter setting

Author:

    Leonardo de Moura (leonardo) 2011-05-19.

Revision History:

--*/
#include"front_end_params.h"
#include"params.h"

/**
   Update front_end_params using s.
   Only the most frequently used options are updated.

   This function is mainly used to allow smt::context to be used in
   the new strategy framework.
*/
void params2front_end_params(params_ref const & s, front_end_params & t) {
    t.m_relevancy_lvl = s.get_uint("relevancy", t.m_relevancy_lvl);
    TRACE("qi_cost", s.display(tout); tout << "\n";);
    t.m_qi_cost = s.get_str("qi_cost", t.m_qi_cost.c_str());
    t.m_mbqi = s.get_bool("mbqi", t.m_mbqi);
    t.m_mbqi_max_iterations = s.get_uint("mbqi_max_iterations", t.m_mbqi_max_iterations);
    t.m_random_seed = s.get_uint("random_seed", t.m_random_seed);
    t.m_model = s.get_bool("produce_models", t.m_model);
    if (s.get_bool("produce_proofs", false))
        t.m_proof_mode = PGM_FINE;
    t.m_well_sorted_check = s.get_bool("check_sorts", t.m_well_sorted_check);
    t.m_qi_eager_threshold = s.get_double("qi_eager_threshold", t.m_qi_eager_threshold);
    t.m_qi_lazy_threshold =  s.get_double("qi_lazy_threshold", t.m_qi_lazy_threshold);
    t.m_preprocess = s.get_bool("preprocess", t.m_preprocess);
    t.m_hi_div0 = s.get_bool("hi_div0", t.m_hi_div0);
    t.m_auto_config = s.get_bool("auto_config", t.m_auto_config);
    t.m_array_simplify = s.get_bool("array_old_simplifier", t.m_array_simplify);
    t.m_arith_branch_cut_ratio = s.get_uint("arith_branch_cut_ratio", t.m_arith_branch_cut_ratio);
    t.m_arith_expand_eqs = s.get_bool("arith_expand_eqs", t.m_arith_expand_eqs);

    if (s.get_bool("arith_greatest_error_pivot", false))
        t.m_arith_pivot_strategy = ARITH_PIVOT_GREATEST_ERROR;
    else if (s.get_bool("arith_least_error_pivot", false))
        t.m_arith_pivot_strategy = ARITH_PIVOT_LEAST_ERROR;
}

/**
   \brief Copy parameters (from s) that affect the semantics of Z3 (e.g., HI_DIV0).
   It also copies the model construction parameter. Thus, model construction
   can be enabled at the command line.
*/
void front_end_params2params(front_end_params const & s, params_ref & t) {
    if (s.m_model)
        t.set_bool("produce_models", true);
    if (!s.m_hi_div0)
        t.set_bool("hi_div0", false);
}

/**
   \brief Bridge for using params_ref with smt::context.
*/
void solver_front_end_params_descrs(param_descrs & r) {
    r.insert("hi_div0", CPK_BOOL, "(default: true) if true, then Z3 uses the usual hardware interpretation for division (rem, mod) by zero. Otherwise, these operations are considered uninterpreted");
    r.insert("relevancy", CPK_UINT, "relevancy propagation heuristic: 0 - disabled, 1 - relevancy is tracked by only affects quantifier instantiation, 2 - relevancy is tracked, and an atom is only asserted if it is relevant");
    r.insert("mbqi", CPK_BOOL, "model based quantifier instantiation (MBQI)");
    r.insert("mbqi_max_iterations", CPK_UINT, "maximum number of rounds of MBQI");
    r.insert("random_seed", CPK_UINT, "random seed for smt solver");
    r.insert("qi_eager_threshold", CPK_DOUBLE, "threshold for eager quantifier instantiation");
    r.insert("qi_lazy_threshold", CPK_DOUBLE, "threshold for lazy quantifier instantiation");
    r.insert("auto_config", CPK_BOOL, "use heuristics to automatically configure smt solver");
    r.insert("arith_branch_cut_ratio", CPK_UINT, "branch&bound / gomory cut ratio");
}
