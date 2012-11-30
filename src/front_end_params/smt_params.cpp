/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_params.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-20.

Revision History:

--*/
#include"smt_params.h"
#include"trace.h"

void smt_params::register_params(ini_params & p) {
    dyn_ack_params::register_params(p);
    qi_params::register_params(p);
    theory_arith_params::register_params(p);
    theory_array_params::register_params(p);
    theory_bv_params::register_params(p);
    theory_datatype_params::register_params(p);

    p.register_bool_param("check_proof", m_check_proof);
    p.register_bool_param("display_proof", m_display_proof);
    p.register_bool_param("display_dot_proof", m_display_dot_proof);
    p.register_bool_param("display_unsat_core", m_display_unsat_core);
    p.register_bool_param("internalizer_nnf", m_internalizer_nnf);
    p.register_bool_param("eq_propagation", m_eq_propagation);
    p.register_bool_param("bin_clauses", m_binary_clause_opt);
    p.register_unsigned_param("relevancy", m_relevancy_lvl, "relevancy propagation heuristic: 0 - disabled, 1 - relevancy is tracked by only affects quantifier instantiation, 2 - relevancy is tracked, and an atom is only asserted if it is relevant", true);
    p.register_bool_param("relevancy_lemma", m_relevancy_lemma, "true if lemmas are used to propagate relevancy");
    p.register_unsigned_param("random_seed", m_random_seed, "random seed for Z3");
    p.register_percentage_param("random_case_split_freq", m_random_var_freq, "frequency of random case splits");
    p.register_int_param("phase_selection", 0, 6, reinterpret_cast<int&>(m_phase_selection), "phase selection heuristic: 0 - always false, 1 - always true, 2 - phase caching, 3 - phase caching conservative, 4 - phase caching conservative 2, 5 - random, 6 - number of occurrences");
    p.register_bool_param("minimize_lemmas", m_minimize_lemmas, "enable/disable lemma minimization algorithm");
    p.register_unsigned_param("max_conflicts", m_max_conflicts, "maximum number of conflicts");

    p.register_unsigned_param("recent_lemma_threshold", m_recent_lemmas_size);
    p.register_unsigned_param("tick", m_tick);

    PRIVATE_PARAMS({
            p.register_bool_param("theory_resolve", m_theory_resolve, "Apply theory resolution to produce auxiliary conflict clauses", true);
        });

    p.register_int_param("restart_strategy", 0, 4, reinterpret_cast<int&>(m_restart_strategy), "0 - geometric, 1 - inner-outer-geometric, 2 - luby, 3 - fixed, 4 - arithmetic");
    p.register_unsigned_param("restart_initial", m_restart_initial, 
                              "inital restart frequency in number of conflicts, it is also the unit for the luby sequence");
    p.register_double_param("restart_factor", m_restart_factor, "when using geometric (or inner-outer-geometric) progression of restarts, it specifies the constant used to multiply the currect restart threshold");
    p.register_bool_param("restart_adaptive", m_restart_adaptive, "disable restarts based on the search 'agility'");
    p.register_percentage_param("restart_agility_threshold", m_restart_agility_threshold);

    p.register_int_param("lemma_gc_strategy", 0, 2, reinterpret_cast<int&>(m_lemma_gc_strategy), "0 - fixed, 1 - geometric, 2 - at every restart");
    p.register_bool_param("lemma_gc_half", m_lemma_gc_half, "true for simple gc algorithm (delete approx. half of the clauses)");
    p.register_unsigned_param("lemma_gc_initial", m_lemma_gc_initial, "lemma initial gc frequency (in number of conflicts), used by fixed or geometric strategies");
    p.register_double_param("lemma_gc_factor", m_lemma_gc_factor, "used by geometric strategy");
    p.register_unsigned_param("lemma_gc_new_old_ratio", m_new_old_ratio);
    p.register_unsigned_param("lemma_gc_new_clause_activity", m_new_clause_activity);
    p.register_unsigned_param("lemma_gc_old_clause_activity", m_old_clause_activity);
    p.register_unsigned_param("lemma_gc_new_clause_relevancy", m_new_clause_relevancy);
    p.register_unsigned_param("lemma_gc_old_clause_relevancy", m_old_clause_activity);
    
    p.register_bool_param("simplify_clauses", m_simplify_clauses);
    
    p.register_int_param("random_initial_activity", 0, 2, reinterpret_cast<int&>(m_random_initial_activity));

    PRIVATE_PARAMS({

        p.register_double_param("inv_decay", m_inv_decay);
        p.register_unsigned_param("phase_caching_on_duration", m_phase_caching_on);
        p.register_unsigned_param("phase_caching_off_duration", m_phase_caching_off);
    });

    p.register_bool_param("smtlib_dump_lemmas", m_smtlib_dump_lemmas);
    p.register_string_param("smtlib_logic", m_smtlib_logic, "Name used for the :logic field when generating SMT-LIB benchmarks");
    p.register_bool_param("display_features", m_display_features);

    p.register_bool_param("new_core2th_eq", m_new_core2th_eq);
    p.register_bool_param("ematching", m_ematching, "E-Matching based quantifier instantiation");

    p.register_bool_param("profile_res_sub", m_profile_res_sub);
#ifndef _EXTERNAL_RELEASE 
    p.register_bool_param("display_bool_var2expr", m_display_bool_var2expr);
    p.register_bool_param("display_ll_bool_var2expr", m_display_ll_bool_var2expr);
    p.register_bool_param("abort_after_preproc", m_abort_after_preproc, "abort after preprocessing step, this flag is only useful for debugging purposes");
    p.register_bool_param("display_installed_theories", m_display_installed_theories, "display theories installed at smt::context", true);
#endif
    p.register_int_param("case_split", 0, 5, reinterpret_cast<int&>(m_case_split_strategy), "0 - case split based on variable activity, 1 - similar to 0, but delay case splits created during the search, 2 - similar to 0, but cache the relevancy, 3 - case split based on relevancy (structural splitting), 4 - case split on relevancy and activity, 5 - case split on relevancy and current goal");
    p.register_unsigned_param("rel_case_split_order", 0, 2, m_rel_case_split_order, "structural (relevancy) splitting order: 0 - left-to-right (default), 1 - random, 2 - right-to-left");
    p.register_bool_param("lookahead_diseq", m_lookahead_diseq);

    p.register_bool_param("delay_units", m_delay_units);
    p.register_unsigned_param("delay_units_threshold", m_delay_units_threshold);

    p.register_bool_param("model", m_model, "enable/disable model construction", true);
    p.register_bool_param("model_validate", m_model_validate, "validate the model", true);
    p.register_bool_param("model_on_timeout", m_model_on_timeout, "after hitting soft-timeout or memory high watermark, generate a candidate model", true);
    p.register_bool_param("model_on_final_check", m_model_on_final_check, "display candidate model (in the standard output) whenever Z3 hits a final check", true);
    
    p.register_unsigned_param("progress_sampling_freq", m_progress_sampling_freq, "frequency for progress output in miliseconds");
}

