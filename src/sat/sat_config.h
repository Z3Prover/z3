/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_config.h

Abstract:

    SAT main configuration options.
    Sub-components have their own options.

Author:

    Leonardo de Moura (leonardo) 2011-05-21.

Revision History:

--*/
#ifndef SAT_CONFIG_H_
#define SAT_CONFIG_H_

#include "util/params.h"

namespace sat {

    enum phase_selection {
        PS_ALWAYS_TRUE,
        PS_ALWAYS_FALSE,
        PS_CACHING,
        PS_RANDOM
    };

    enum restart_strategy {
        RS_GEOMETRIC,
        RS_LUBY,
        RS_EMA,
        RS_STATIC
    };

    enum gc_strategy {
        GC_DYN_PSM,
        GC_PSM,
        GC_GLUE,
        GC_GLUE_PSM,
        GC_PSM_GLUE
    };

    enum branching_heuristic {
        BH_VSIDS,
        BH_CHB,
        BH_LRB
    };

    enum pb_solver {
        PB_SOLVER,
        PB_CIRCUIT,
        PB_SORTING,
        PB_TOTALIZER,
        PB_SEGMENTED
    };

    enum reward_t {
        ternary_reward,
        unit_literal_reward,
        heule_schur_reward,
        heule_unit_reward,
        march_cu_reward
    };

    enum cutoff_t {
        depth_cutoff,
        freevars_cutoff,
        psat_cutoff,
        adaptive_freevars_cutoff,
        adaptive_psat_cutoff
    };

    enum local_search_mode {
        gsat,
        wsat
    };

    struct config {
        unsigned long long m_max_memory;
        phase_selection    m_phase;
        unsigned           m_phase_caching_on;
        unsigned           m_phase_caching_off;
        bool               m_phase_sticky;
        bool               m_propagate_prefetch;
        restart_strategy   m_restart;
        bool               m_restart_fast;
        unsigned           m_restart_initial;
        double             m_restart_factor; // for geometric case
        double             m_restart_margin; // for ema
        unsigned           m_restart_max;
        double             m_fast_glue_avg;
        double             m_slow_glue_avg;
        unsigned           m_inprocess_max;
        double             m_random_freq;
        unsigned           m_random_seed;
        unsigned           m_burst_search;
        unsigned           m_max_conflicts;
        unsigned           m_num_threads;
        unsigned           m_local_search_threads;
        bool               m_local_search;
        local_search_mode  m_local_search_mode;
        unsigned           m_unit_walk_threads;
        bool               m_unit_walk;
        bool               m_lookahead_simplify;
        bool               m_lookahead_simplify_bca;
        cutoff_t           m_lookahead_cube_cutoff;
        double             m_lookahead_cube_fraction;
        unsigned           m_lookahead_cube_depth;
        double             m_lookahead_cube_freevars;
        double             m_lookahead_cube_psat_var_exp;
        double             m_lookahead_cube_psat_clause_base;
        double             m_lookahead_cube_psat_trigger;
        reward_t           m_lookahead_reward;
        bool               m_lookahead_global_autarky;
        bool               m_lookahead_use_learned;

        bool               m_incremental;
        unsigned           m_next_simplify1;
        double             m_simplify_mult2;
        unsigned           m_simplify_max;
        unsigned           m_simplify_delay;

        unsigned           m_variable_decay;

        gc_strategy        m_gc_strategy;
        unsigned           m_gc_initial;
        unsigned           m_gc_increment;
        unsigned           m_gc_small_lbd;
        unsigned           m_gc_k;
        bool               m_gc_burst;
        bool               m_gc_defrag;

        bool               m_force_cleanup;


        bool               m_minimize_lemmas;
        bool               m_dyn_sub_res;
        bool               m_core_minimize;
        bool               m_core_minimize_partial;
        bool               m_drat;
        symbol             m_drat_file;
        bool               m_drat_check_unsat;
        bool               m_drat_check_sat;
        
        pb_solver          m_pb_solver;
        bool               m_card_solver;
        
        // branching heuristic settings.
        branching_heuristic m_branching_heuristic;
        bool               m_anti_exploration;
        double             m_step_size_init;
        double             m_step_size_dec;
        double             m_step_size_min;
        double             m_reward_multiplier;
        double             m_reward_offset;

        // simplifier configurations used outside of sat_simplifier
        bool               m_elim_vars;

        config(params_ref const & p);
        void updt_params(params_ref const & p);
        static void collect_param_descrs(param_descrs & d);
    };
};

#endif
