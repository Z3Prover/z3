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
#pragma once

#include "util/params.h"

namespace sat {

    enum phase_selection {
        PS_ALWAYS_TRUE,
        PS_ALWAYS_FALSE,
        PS_BASIC_CACHING,
        PS_SAT_CACHING,
        PS_LOCAL_SEARCH,
        PS_FROZEN,
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
        BH_CHB
    };

    enum pb_resolve {
        PB_CARDINALITY,
        PB_ROUNDING
    };

    enum pb_lemma_format {
        PB_LEMMA_CARDINALITY,
        PB_LEMMA_PB
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
        // Memory layout optimized: fields grouped by size for minimal padding
        // 8-byte aligned fields first (doubles, unsigned long long)
        unsigned long long m_max_memory;
        double             m_reorder_itau;
        double             m_restart_factor; // for geometric case
        double             m_restart_margin; // for ema
        double             m_fast_glue_avg;
        double             m_slow_glue_avg;
        double             m_random_freq;
        double             m_lookahead_cube_fraction;
        double             m_lookahead_cube_freevars;
        double             m_lookahead_cube_psat_var_exp;
        double             m_lookahead_cube_psat_clause_base;
        double             m_lookahead_cube_psat_trigger;
        double             m_lookahead_delta_fraction;
        double             m_simplify_mult2;
        double             m_step_size_init;
        double             m_step_size_dec;
        double             m_step_size_min;
        double             m_reward_multiplier;
        double             m_reward_offset;

        // Symbol fields (8 bytes each on 64-bit platforms)
        symbol             m_inprocess_out;
        symbol             m_drat_file;

        // 4-byte fields: unsigned integers
        unsigned           m_search_sat_conflicts;
        unsigned           m_search_unsat_conflicts;
        unsigned           m_rephase_base;
        unsigned           m_reorder_base;
        unsigned           m_reorder_activity_scale;
        unsigned           m_restart_initial;
        unsigned           m_restart_max;
        unsigned           m_activity_scale;
        unsigned           m_inprocess_max;
        unsigned           m_random_seed;
        unsigned           m_burst_search;
        unsigned           m_max_conflicts;
        unsigned           m_num_threads;
        unsigned           m_ddfw_threads;
        unsigned           m_local_search_threads;
        unsigned           m_anf_delay;
        unsigned           m_lookahead_cube_depth;
        unsigned           m_next_simplify1;
        unsigned           m_simplify_max;
        unsigned           m_simplify_delay;
        unsigned           m_variable_decay;
        unsigned           m_gc_initial;
        unsigned           m_gc_increment;
        unsigned           m_gc_small_lbd;
        unsigned           m_gc_k;
        unsigned           m_backtrack_scopes;  // backtracking
        unsigned           m_backtrack_init_conflicts;

        // 4-byte fields: enums
        phase_selection    m_phase;
        restart_strategy   m_restart;
        local_search_mode  m_local_search_mode;
        cutoff_t           m_lookahead_cube_cutoff;
        reward_t           m_lookahead_reward;
        gc_strategy        m_gc_strategy;
        pb_resolve         m_pb_resolve;
        pb_lemma_format    m_pb_lemma_format;
        branching_heuristic m_branching_heuristic;

        // These bool fields are accessed by reference (via flet), so cannot be bitfields
        bool               m_core_minimize;
        bool               m_drat;  // drat proofs

        // Bitfields for 32 boolean flags (typically packed into 4 bytes on most platforms)
        // Note: m_core_minimize and m_drat are kept as regular bools above
        // because they are passed by reference (flet usage)
        unsigned           m_phase_sticky : 1;
        unsigned           m_propagate_prefetch : 1;
        unsigned           m_restart_fast : 1;
        unsigned           m_enable_pre_simplify : 1;
        unsigned           m_ddfw_search : 1;
        unsigned           m_prob_search : 1;
        unsigned           m_local_search : 1;
        unsigned           m_local_search_dbg_flips : 1;
        unsigned           m_anf_simplify : 1;
        unsigned           m_anf_exlin : 1;
        unsigned           m_lookahead_simplify : 1;
        unsigned           m_lookahead_simplify_bca : 1;
        unsigned           m_lookahead_double : 1;
        unsigned           m_lookahead_global_autarky : 1;
        unsigned           m_lookahead_use_learned : 1;
        unsigned           m_incremental : 1;
        unsigned           m_gc_burst : 1;
        unsigned           m_gc_defrag : 1;
        unsigned           m_force_cleanup : 1;
        unsigned           m_minimize_lemmas : 1;
        unsigned           m_dyn_sub_res : 1;
        unsigned           m_core_minimize_partial : 1;
        unsigned           m_drat_disable : 1;
        unsigned           m_drat_binary : 1;
        unsigned           m_smt_proof_check : 1;
        unsigned           m_drat_check_unsat : 1;
        unsigned           m_drat_check_sat : 1;
        unsigned           m_drat_activity : 1;
        unsigned           m_card_solver : 1;
        unsigned           m_xor_solver : 1;
        unsigned           m_anti_exploration : 1;
        unsigned           m_elim_vars : 1;  // simplifier configurations used outside of sat_simplifier

        config(params_ref const & p);
        void updt_params(params_ref const & p);
        static void collect_param_descrs(param_descrs & d);

    };

    // Verify struct packing optimization
    // Previous size was 408 bytes, optimized to 320 bytes (88 bytes / 21.6% reduction)
    // The assertion checks for a reasonable range to detect both regressions and unexpected reductions
    static_assert(sizeof(config) >= 300 && sizeof(config) <= 320, 
                  "sat::config size changed unexpectedly - expected 320 bytes, check field ordering and alignment");
};

