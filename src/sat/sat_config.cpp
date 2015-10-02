/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_config.cpp

Abstract:

    SAT configuration options

Author:

    Leonardo de Moura (leonardo) 2011-05-21.

Revision History:

--*/
#include"sat_config.h"
#include"sat_types.h"
#include"sat_params.hpp"

namespace sat {

    config::config(params_ref const & p):
        m_always_true("always_true"),
        m_always_false("always_false"),
        m_caching("caching"),
        m_random("random"),
        m_geometric("geometric"),
        m_luby("luby"),
        m_dyn_psm("dyn_psm"),
        m_psm("psm"),
        m_glue("glue"),
        m_glue_psm("glue_psm"),
        m_psm_glue("psm_glue") {
        updt_params(p); 
    }

    void config::updt_params(params_ref const & _p) {
        sat_params p(_p);
        m_max_memory  = megabytes_to_bytes(p.max_memory());

        symbol s = p.restart();
        if (s == m_luby)
            m_restart = RS_LUBY;
        else if (s == m_geometric)
            m_restart = RS_GEOMETRIC;
        else
            throw sat_param_exception("invalid restart strategy");

        s = p.phase();
        if (s == m_always_false) 
            m_phase = PS_ALWAYS_FALSE;
        else if (s == m_always_true)
            m_phase = PS_ALWAYS_TRUE;
        else if (s == m_caching)
            m_phase = PS_CACHING;
        else if (s == m_random)
            m_phase = PS_RANDOM;
        else
            throw sat_param_exception("invalid phase selection strategy");

        m_phase_caching_on  = p.phase_caching_on();
        m_phase_caching_off = p.phase_caching_off();

        m_restart_initial = p.restart_initial();
        m_restart_factor  = p.restart_factor();
        
        m_random_freq     = p.random_freq();
        m_random_seed     = p.random_seed();
        if (m_random_seed == 0) 
            m_random_seed = _p.get_uint("random_seed", 0);
        
        m_burst_search    = p.burst_search();
        
        m_max_conflicts   = p.max_conflicts();
        
        // These parameters are not exposed
        m_simplify_mult1  = _p.get_uint("simplify_mult1", 300);
        m_simplify_mult2  = _p.get_double("simplify_mult2", 1.5);
        m_simplify_max    = _p.get_uint("simplify_max", 500000);
        // --------------------------------

        s = p.gc();
        if (s == m_dyn_psm) {
            m_gc_strategy     = GC_DYN_PSM;
            m_gc_initial      = p.gc_initial();
            m_gc_increment    = p.gc_increment();
            m_gc_small_lbd    = p.gc_small_lbd();
            m_gc_k            = p.gc_k();
            if (m_gc_k > 255)
                m_gc_k = 255;
        }
        else {
            if (s == m_glue_psm)
                m_gc_strategy = GC_GLUE_PSM;
            else if (s == m_glue)
                m_gc_strategy = GC_GLUE;
            else if (s == m_psm)
                m_gc_strategy = GC_PSM;
            else if (s == m_psm_glue)
                m_gc_strategy = GC_PSM_GLUE;
            else 
                throw sat_param_exception("invalid gc strategy");
            m_gc_initial      = p.gc_initial();
            m_gc_increment    = p.gc_increment();
        }
        m_minimize_lemmas = p.minimize_lemmas();
        m_minimize_core   = p.minimize_core();
        m_minimize_core_partial   = p.minimize_core_partial();
        m_optimize_model  = p.optimize_model();
        m_bcd             = p.bcd();
        m_dyn_sub_res     = p.dyn_sub_res();
    }

    void config::collect_param_descrs(param_descrs & r) {
        sat_params::collect_param_descrs(r);
    }

};
