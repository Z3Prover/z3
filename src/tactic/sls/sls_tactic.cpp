/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    sls_tactic.h

Abstract:

    A Stochastic Local Search (SLS) tactic

Author:

    Christoph (cwinter) 2012-02-29

Notes:

--*/
#include "ast/normal_forms/nnf.h"
#include "tactic/core/solve_eqs_tactic.h"
#include "tactic/bv/bv_size_reduction_tactic.h"
#include "tactic/bv/max_bv_sharing_tactic.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/core/propagate_values_tactic.h"
#include "tactic/core/ctx_simplify_tactic.h"
#include "tactic/core/elim_uncnstr_tactic.h"
#include "tactic/core/nnf_tactic.h"
#include "util/stopwatch.h"
#include "tactic/sls/sls_tactic.h"
#include "tactic/sls/sls_params.hpp"
#include "tactic/sls/sls_engine.h"

class sls_tactic : public tactic {    
    ast_manager    & m;
    params_ref       m_params;
    sls_engine     * m_engine;

public:
    sls_tactic(ast_manager & _m, params_ref const & p):
        m(_m),
        m_params(p) {
        m_engine = alloc(sls_engine, m, p);
    }

    tactic * translate(ast_manager & m) override {
        return alloc(sls_tactic, m, m_params);
    }

    ~sls_tactic() override {
        dealloc(m_engine);
    }

    void updt_params(params_ref const & p) override {
        m_params = p;
        m_engine->updt_params(p);
    }

    void collect_param_descrs(param_descrs & r) override {
        sls_params::collect_param_descrs(r);
    }
    
    void operator()(goal_ref const & g, 
                    goal_ref_buffer & result) override {
        result.reset();
        
        TRACE("sls", g->display(tout););
        tactic_report report("sls", *g);
        
        model_converter_ref mc;
        m_engine->operator()(g, mc);
        g->add(mc.get());
        g->inc_depth();
        result.push_back(g.get());
    }

    void cleanup() override {
        sls_engine * d = alloc(sls_engine, m, m_params);
        std::swap(d, m_engine);            
        dealloc(d);
    }
    
    void collect_statistics(statistics & st) const override {
        m_engine->collect_statistics(st);
    }

    void reset_statistics() override {
        m_engine->reset_statistics();
    }

};

static tactic * mk_sls_tactic(ast_manager & m, params_ref const & p) {
    return and_then(fail_if_not(mk_is_qfbv_probe()), // Currently only QF_BV is supported.
                    clean(alloc(sls_tactic, m, p)));
}


static tactic * mk_preamble(ast_manager & m, params_ref const & p) {
    params_ref main_p;
    main_p.set_bool("elim_and", true);
    // main_p.set_bool("pull_cheap_ite", true);
    main_p.set_bool("push_ite_bv", true);
    main_p.set_bool("blast_distinct", true);
    main_p.set_bool("hi_div0", true);

    params_ref simp2_p = p;
    simp2_p.set_bool("som", true);
    simp2_p.set_bool("pull_cheap_ite", true);
    simp2_p.set_bool("push_ite_bv", false);
    simp2_p.set_bool("local_ctx", true);
    simp2_p.set_uint("local_ctx_limit", 10000000);

    params_ref hoist_p;
    hoist_p.set_bool("hoist_mul", true);
    hoist_p.set_bool("som", false);

    params_ref gaussian_p;
    // conservative gaussian elimination. 
    gaussian_p.set_uint("gaussian_max_occs", 2); 

    params_ref ctx_p;
    ctx_p.set_uint("max_depth", 32);
    ctx_p.set_uint("max_steps", 5000000);
    return and_then(and_then(mk_simplify_tactic(m),                             
                             mk_propagate_values_tactic(m),
                             using_params(mk_solve_eqs_tactic(m), gaussian_p),
                             mk_elim_uncnstr_tactic(m),
                             mk_bv_size_reduction_tactic(m),
                             using_params(mk_simplify_tactic(m), simp2_p)),
                        using_params(mk_simplify_tactic(m), hoist_p),
                        mk_max_bv_sharing_tactic(m),
                        mk_nnf_tactic(m, p));
}

tactic * mk_qfbv_sls_tactic(ast_manager & m, params_ref const & p) {
    tactic * t = and_then(mk_preamble(m, p), mk_sls_tactic(m, p));
    t->updt_params(p);
    return t;
}
