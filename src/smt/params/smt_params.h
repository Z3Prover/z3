/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_params.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-20.

Revision History:

--*/
#ifndef SMT_PARAMS_H_
#define SMT_PARAMS_H_

#include"ast.h"
#include"dyn_ack_params.h"
#include"qi_params.h"
#include"theory_arith_params.h"
#include"theory_array_params.h"
#include"theory_bv_params.h"
#include"theory_pb_params.h"
#include"theory_datatype_params.h"
#include"preprocessor_params.h"
#include"context_params.h"

enum phase_selection { 
    PS_ALWAYS_FALSE,
    PS_ALWAYS_TRUE,
    PS_CACHING,
    PS_CACHING_CONSERVATIVE,
    PS_CACHING_CONSERVATIVE2, // similar to the previous one, but alternated default config from time to time.
    PS_RANDOM,
    PS_OCCURRENCE
};

enum restart_strategy {
    RS_GEOMETRIC,
    RS_IN_OUT_GEOMETRIC,
    RS_LUBY,
    RS_FIXED,
    RS_ARITHMETIC
};

enum lemma_gc_strategy {
    LGC_FIXED,
    LGC_GEOMETRIC,
    LGC_AT_RESTART
};

enum initial_activity {
    IA_ZERO,                    // initialized with 0
    IA_RANDOM_WHEN_SEARCHING,   // random when searching
    IA_RANDOM                   // always random
};

enum case_split_strategy {
    CS_ACTIVITY, // case split based on activity
    CS_ACTIVITY_DELAY_NEW, // case split based on activity but delay new case splits created during the search
    CS_ACTIVITY_WITH_CACHE, // case split based on activity and cache the activity
    CS_RELEVANCY, // case split based on relevancy
    CS_RELEVANCY_ACTIVITY, // case split based on relevancy and activity
    CS_RELEVANCY_GOAL // based on relevancy and the current goal
};

struct smt_params : public preprocessor_params, 
                    public dyn_ack_params, 
                    public qi_params, 
                    public theory_arith_params, 
                    public theory_array_params, 
                    public theory_bv_params,
                    public theory_pb_params,
                    public theory_datatype_params {
    bool             m_display_proof;
    bool             m_display_dot_proof;
    bool             m_display_unsat_core;
    bool             m_check_proof;
    bool             m_eq_propagation;
    bool             m_binary_clause_opt;
    unsigned         m_relevancy_lvl;
    bool             m_relevancy_lemma;
    unsigned         m_random_seed;
    double           m_random_var_freq;
    double           m_inv_decay;
    unsigned         m_clause_decay;
    initial_activity m_random_initial_activity;
    phase_selection  m_phase_selection;
    unsigned         m_phase_caching_on;
    unsigned         m_phase_caching_off;
    bool             m_minimize_lemmas;
    unsigned         m_max_conflicts;
    bool             m_simplify_clauses;
    unsigned         m_tick;
    bool             m_display_features;
    bool             m_new_core2th_eq;
    bool             m_ematching;

    // -----------------------------------
    //
    // Case split strategy
    //
    // -----------------------------------
    case_split_strategy m_case_split_strategy;
    unsigned            m_rel_case_split_order;
    bool                m_lookahead_diseq;

    // -----------------------------------
    //
    // Delay units...
    //
    // -----------------------------------
    bool             m_delay_units;
    unsigned         m_delay_units_threshold;

    // -----------------------------------
    //
    // Conflict resolution
    //
    // -----------------------------------
    bool             m_theory_resolve;

    // -----------------------------------
    //
    // Restart
    //
    // -----------------------------------
    restart_strategy m_restart_strategy;
    unsigned         m_restart_initial;
    double           m_restart_factor;
    bool             m_restart_adaptive;
    double           m_agility_factor;
    double           m_restart_agility_threshold;

    // -----------------------------------
    //
    // Lemma garbage collection
    //
    // -----------------------------------
    lemma_gc_strategy m_lemma_gc_strategy;
    bool              m_lemma_gc_half;
    unsigned          m_recent_lemmas_size;
    unsigned          m_lemma_gc_initial;
    double            m_lemma_gc_factor;
    unsigned          m_new_old_ratio;     //!< the ratio of new and old clauses.
    unsigned          m_new_clause_activity;  
    unsigned          m_old_clause_activity;
    unsigned          m_new_clause_relevancy; //!< Max. number of unassigned literals to be considered relevant.
    unsigned          m_old_clause_relevancy; //!< Max. number of unassigned literals to be considered relevant.
    double            m_inv_clause_decay;     //!< clause activity decay
    
    // -----------------------------------
    //
    // SMT-LIB (debug) pretty printer
    //
    // -----------------------------------
    bool              m_smtlib_dump_lemmas;
    std::string       m_smtlib_logic;
    
    // -----------------------------------
    //
    // Statistics for Profiling
    //
    // -----------------------------------
    bool              m_profile_res_sub;
    bool              m_display_bool_var2expr;
    bool              m_display_ll_bool_var2expr;
    bool              m_abort_after_preproc;

    // -----------------------------------
    //
    // Model generation 
    //
    // -----------------------------------
    bool             m_model; 
    bool             m_model_compact;
    bool             m_model_on_timeout;
    bool             m_model_on_final_check;

    // -----------------------------------
    //
    // Progress sampling
    //
    // -----------------------------------
    unsigned         m_progress_sampling_freq;

    // -----------------------------------
    //
    // Debugging goodies
    //
    // -----------------------------------
    bool             m_display_installed_theories;
    bool             m_core_validate;

    // -----------------------------------
    //
    // From front_end_params
    //
    // -----------------------------------
    bool                m_preprocess;  // temporary hack for disabling all preprocessing..
    bool                m_user_theory_preprocess_axioms;
    bool                m_user_theory_persist_axioms;
    unsigned            m_timeout;
    unsigned            m_rlimit;
    bool                m_at_labels_cex; // only use labels which contains the @ symbol when building multiple counterexamples.
    bool                m_check_at_labels; // check that @ labels are inserted to generate unique counter-examples.    
    bool                m_dump_goal_as_smt;
    bool                m_auto_config;

    smt_params(params_ref const & p = params_ref()):
        m_display_proof(false),
        m_display_dot_proof(false),
        m_display_unsat_core(false),
        m_check_proof(false), 
        m_eq_propagation(true),
        m_binary_clause_opt(true),
        m_relevancy_lvl(2),
        m_relevancy_lemma(false),
        m_random_seed(0),
        m_random_var_freq(0.01),
        m_inv_decay(1.052),
        m_clause_decay(1),
        m_random_initial_activity(IA_RANDOM_WHEN_SEARCHING),
        m_phase_selection(PS_CACHING_CONSERVATIVE),
        m_phase_caching_on(400),
        m_phase_caching_off(100),
        m_minimize_lemmas(true),
        m_max_conflicts(UINT_MAX),
        m_simplify_clauses(true),
        m_tick(1000),
        m_display_features(false),
        m_new_core2th_eq(true),
        m_ematching(true),
        m_case_split_strategy(CS_ACTIVITY_DELAY_NEW),
        m_rel_case_split_order(0),
        m_lookahead_diseq(false),
        m_delay_units(false),
        m_delay_units_threshold(32),
        m_theory_resolve(false),
        m_restart_strategy(RS_IN_OUT_GEOMETRIC),
        m_restart_initial(100),
        m_restart_factor(1.1),
        m_restart_adaptive(true),
        m_agility_factor(0.9999),
        m_restart_agility_threshold(0.18),
        m_lemma_gc_strategy(LGC_FIXED),
        m_lemma_gc_half(false),
        m_recent_lemmas_size(100),
        m_lemma_gc_initial(5000),
        m_lemma_gc_factor(1.1),
        m_new_old_ratio(16),
        m_new_clause_activity(10),
        m_old_clause_activity(500),
        m_new_clause_relevancy(45), 
        m_old_clause_relevancy(6),
        m_inv_clause_decay(1),
        m_smtlib_dump_lemmas(false),
        m_smtlib_logic("AUFLIA"),
        m_profile_res_sub(false),
        m_display_bool_var2expr(false),
        m_display_ll_bool_var2expr(false),
        m_abort_after_preproc(false),
        m_model(true),
        m_model_compact(false),
        m_model_on_timeout(false),
        m_model_on_final_check(false),
        m_progress_sampling_freq(0),
        m_display_installed_theories(false),
        m_core_validate(false),
        m_preprocess(true), // temporary hack for disabling all preprocessing..
        m_user_theory_preprocess_axioms(false),
        m_user_theory_persist_axioms(false),
        m_timeout(0),
        m_rlimit(0),
        m_at_labels_cex(false),
        m_check_at_labels(false),
        m_dump_goal_as_smt(false),
        m_auto_config(true) {
        updt_local_params(p);
    }

    void updt_local_params(params_ref const & p);

    void updt_params(params_ref const & p);

    void updt_params(context_params const & p);
};

#endif /* SMT_PARAMS_H_ */

