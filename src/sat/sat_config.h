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

#include"params.h"

namespace sat {

    enum phase_selection {
        PS_ALWAYS_TRUE,
        PS_ALWAYS_FALSE,
        PS_CACHING,
        PS_RANDOM
    };

    enum restart_strategy {
        RS_GEOMETRIC,
        RS_LUBY
    };

    enum gc_strategy {
        GC_DYN_PSM,
        GC_PSM,
        GC_GLUE,
        GC_GLUE_PSM,
        GC_PSM_GLUE
    };

    struct config {
        unsigned long long m_max_memory;
        phase_selection    m_phase;
        unsigned           m_phase_caching_on;
        unsigned           m_phase_caching_off;
        restart_strategy   m_restart;
        unsigned           m_restart_initial;
        double             m_restart_factor; // for geometric case
        double             m_random_freq;
        unsigned           m_random_seed;
        unsigned           m_burst_search;
        unsigned           m_max_conflicts;

        unsigned           m_simplify_mult1;
        double             m_simplify_mult2;
        unsigned           m_simplify_max;

        gc_strategy        m_gc_strategy;
        unsigned           m_gc_initial;
        unsigned           m_gc_increment;
        unsigned           m_gc_small_lbd;
        unsigned           m_gc_k;

        bool               m_minimize_lemmas;
        bool               m_dyn_sub_res;
        bool               m_core_minimize;
        bool               m_core_minimize_partial;
        bool               m_optimize_model;
        bool               m_bcd;


        symbol             m_always_true;
        symbol             m_always_false;
        symbol             m_caching;
        symbol             m_random;
        symbol             m_geometric;
        symbol             m_luby;
        
        symbol             m_dyn_psm;
        symbol             m_psm;        
        symbol             m_glue;        
        symbol             m_glue_psm;        
        symbol             m_psm_glue;        
        
        config(params_ref const & p);
        void updt_params(params_ref const & p);
        static void collect_param_descrs(param_descrs & d);
    };
};

#endif
