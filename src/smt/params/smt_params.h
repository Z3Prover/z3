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
#pragma once

#include "ast/static_features.h"
#include "smt/params/dyn_ack_params.h"
#include "smt/params/qi_params.h"
#include "smt/params/theory_arith_params.h"
#include "smt/params/theory_array_params.h"
#include "smt/params/theory_bv_params.h"
#include "smt/params/theory_str_params.h"
#include "smt/params/theory_seq_params.h"
#include "smt/params/theory_pb_params.h"
#include "smt/params/theory_datatype_params.h"
#include "smt/params/preprocessor_params.h"
#include "params/context_params.h"

enum phase_selection {
    PS_ALWAYS_FALSE,
    PS_ALWAYS_TRUE,
    PS_CACHING,
    PS_CACHING_CONSERVATIVE,
    PS_CACHING_CONSERVATIVE2, // similar to the previous one, but alternated default config from time to time.
    PS_RANDOM,
    PS_OCCURRENCE,
    PS_THEORY
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
    LGC_AT_RESTART,
    LGC_NONE
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
    CS_RELEVANCY_GOAL, // based on relevancy and the current goal
    CS_ACTIVITY_THEORY_AWARE_BRANCHING // activity-based case split, but theory solvers can manipulate activity
};

struct smt_params : public preprocessor_params,
                    public dyn_ack_params,
                    public qi_params,
                    public theory_arith_params,
                    public theory_array_params,
                    public theory_bv_params,
                    public theory_str_params,
                    public theory_seq_params,
                    public theory_pb_params,
                    public theory_datatype_params {
    bool             m_display_proof = false;
    bool             m_display_dot_proof = false;
    bool             m_display_unsat_core = false;
    bool             m_check_proof = false;
    bool             m_eq_propagation = true;
    bool             m_binary_clause_opt = true;
    unsigned         m_relevancy_lvl = 2;
    bool             m_relevancy_lemma = false;
    unsigned         m_random_seed = 0;
    double           m_random_var_freq = 0.01;
    double           m_inv_decay = 1.052;
    unsigned         m_clause_decay = 1;
    initial_activity m_random_initial_activity = initial_activity::IA_RANDOM_WHEN_SEARCHING;
    phase_selection  m_phase_selection = phase_selection::PS_CACHING_CONSERVATIVE;
    unsigned         m_phase_caching_on = 700;
    unsigned         m_phase_caching_off = 100;
    bool             m_minimize_lemmas = true;
    unsigned         m_max_conflicts = UINT_MAX;
    unsigned         m_restart_max;
    unsigned         m_cube_depth = 1;
    unsigned         m_threads = 1;
    unsigned         m_threads_max_conflicts = UINT_MAX;
    unsigned         m_threads_cube_frequency = 2;
    bool             m_simplify_clauses = true;
    unsigned         m_tick = 1000;
    bool             m_display_features = false;
    bool             m_new_core2th_eq = true;
    bool             m_ematching = true;
    bool             m_induction = false;
    bool             m_clause_proof = false;
    symbol           m_proof_log;
    bool             m_sls_enable = false;
    bool             m_sls_parallel = true;

    // -----------------------------------
    //
    // Case split strategy
    //
    // -----------------------------------
    case_split_strategy m_case_split_strategy = case_split_strategy::CS_ACTIVITY_DELAY_NEW;
    unsigned            m_rel_case_split_order = 0;
    bool                m_lookahead_diseq = false;
    bool                m_theory_case_split = false;
    bool                m_theory_aware_branching = false;

    // -----------------------------------
    //
    // Delay units...
    //
    // -----------------------------------
    bool             m_delay_units = false;
    unsigned         m_delay_units_threshold = 32;

    // -----------------------------------
    //
    // Conflict resolution
    //
    // -----------------------------------
    bool             m_theory_resolve = false;

    // -----------------------------------
    //
    // Restart
    //
    // -----------------------------------
    restart_strategy m_restart_strategy = restart_strategy::RS_IN_OUT_GEOMETRIC;
    unsigned         m_restart_initial = 100;
    double           m_restart_factor = 1.1;
    bool             m_restart_adaptive = true;
    double           m_agility_factor = 0.9999;
    double           m_restart_agility_threshold = 0.18;

    // -----------------------------------
    //
    // Lemma garbage collection
    //
    // -----------------------------------
    lemma_gc_strategy m_lemma_gc_strategy = lemma_gc_strategy::LGC_FIXED;
    bool              m_lemma_gc_half = false;
    unsigned          m_recent_lemmas_size = 100;
    unsigned          m_lemma_gc_initial = 5000;
    double            m_lemma_gc_factor = 1.1;
    unsigned          m_new_old_ratio = 16;     //!< the ratio of new and old clauses.
    unsigned          m_new_clause_activity = 10;
    unsigned          m_old_clause_activity = 500;
    unsigned          m_new_clause_relevancy = 45; //!< Max. number of unassigned literals to be considered relevant.
    unsigned          m_old_clause_relevancy = 6; //!< Max. number of unassigned literals to be considered relevant.
    double            m_inv_clause_decay = 1;     //!< clause activity decay

    // -----------------------------------
    //
    // User propagator configuration
    //
    // -----------------------------------

    bool             m_up_persist_clauses = false;

    // -----------------------------------
    //
    // SMT-LIB (debug) pretty printer
    //
    // -----------------------------------
    bool              m_axioms2files = false;
    bool              m_lemmas2console = false;
    bool              m_instantiations2console = false;
    symbol            m_logic = symbol::null;

    // -----------------------------------
    //
    // Statistics for Profiling
    //
    // -----------------------------------
    bool              m_profile_res_sub = false;
    bool              m_display_bool_var2expr = false;
    bool              m_display_ll_bool_var2expr = false;

    // -----------------------------------
    //
    // Model generation
    //
    // -----------------------------------
    bool             m_model = true;
    bool             m_model_on_timeout = false;
    bool             m_model_on_final_check = false;

    // -----------------------------------
    //
    // Progress sampling
    //
    // -----------------------------------
    unsigned         m_progress_sampling_freq = 0;

    // -----------------------------------
    //
    // Debugging goodies
    //
    // -----------------------------------
    bool             m_core_validate = false;

    // -----------------------------------
    //
    // From front_end_params
    //
    // -----------------------------------
    bool                m_preprocess = true;  // temporary hack for disabling all preprocessing..
    bool                m_user_theory_preprocess_axioms = false;
    bool                m_user_theory_persist_axioms = false;
    bool                m_at_labels_cex = false; // only use labels which contains the @ symbol when building multiple counterexamples.
    bool                m_check_at_labels = false; // check that @ labels are inserted to generate unique counter-examples.
    bool                m_dump_goal_as_smt = false;
    bool                m_auto_config = true;

    // -----------------------------------
    //
    // Spacer hacking
    //
    // -----------------------------------
    bool                m_dump_benchmarks;
    double              m_dump_min_time;
    bool                m_dump_recheck;

    // -----------------------------------
    //
    // Solver selection
    //
    // -----------------------------------
    symbol m_string_solver;

    smt_params(params_ref const & p = params_ref()):
        m_string_solver(symbol("auto")){
        updt_local_params(p);
    }

    void updt_local_params(params_ref const & p);

    void updt_params(params_ref const & p);

    void updt_params(context_params const & p);

    void display(std::ostream & out) const;

    void validate_string_solver(symbol const& s) const;

    void setup_QF_UF();

    void setup_QF_RDL();

    void setup_QF_RDL(static_features & st);

    void setup_QF_IDL();

    void setup_QF_IDL(static_features & st);

    void setup_QF_LRA();

    void setup_QF_LRA(static_features const& st);

    void setup_QF_LIA();

    void setup_QF_LIA(static_features const& st);

    void setup_QF_UFIDL();

    void setup_QF_UFLIA();

    void setup_QF_UFLRA();

    void setup_QF_BV();

    void setup_QF_AUFBV();

    void setup_QF_AX();

    void setup_QF_AX(static_features const& st);

    void setup_QF_AUFLIA();

    void setup_QF_AUFLIA(static_features const& st);

    void setup_AUFLIA(bool simple_array);

    void setup_AUFLIA(static_features const & st);

    void setup_AUFLIRA(bool simple_array);

    void setup_LRA();
            
};


