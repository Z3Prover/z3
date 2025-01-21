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
#include "params/sls_params.hpp"
#include "ast/sls/sls_bv_engine.h"
#include "ast/sls/sls_smt_solver.h"

class sls_smt_tactic : public tactic {
    ast_manager& m;
    params_ref   m_params;
    sls::smt_solver*     m_sls;
    statistics   m_st;

public:
    sls_smt_tactic(ast_manager& _m, params_ref const& p) :
        m(_m),
        m_params(p) {
        m_sls = alloc(sls::smt_solver, m, p);
    }

    tactic* translate(ast_manager& m) override {
        return alloc(sls_smt_tactic, m, m_params);
    }

    ~sls_smt_tactic() override {
        dealloc(m_sls);
    }

    char const* name() const override { return "sls-smt"; }

    void updt_params(params_ref const& p) override {
        m_params.append(p);
        m_sls->updt_params(m_params);
    }

    void collect_param_descrs(param_descrs& r) override {
        sls_params::collect_param_descrs(r);
    }

    void run(goal_ref const& g, model_converter_ref& mc) {
        if (g->inconsistent()) {
            mc = nullptr;
            return;
        }

        for (unsigned i = 0; i < g->size(); i++)
            m_sls->assert_expr(g->form(i));


        m_st.reset();
        lbool res = l_undef;
        try {
            res = m_sls->check();
        }
        catch (z3_exception& ex) {
            IF_VERBOSE(1, verbose_stream() << "SLS threw an exception: " << ex.what() << "\n");
            m_sls->collect_statistics(m_st);
            throw;
        }
        m_sls->collect_statistics(m_st);

//        report_tactic_progress("Number of flips:", m_sls->get_num_moves());
        IF_VERBOSE(10, verbose_stream() << res << "\n");
        IF_VERBOSE(10, m_sls->display(verbose_stream()));

        if (res == l_true) {            
            if (g->models_enabled()) {
                model_ref mdl = m_sls->get_model();
                mc = model2model_converter(mdl.get());
                TRACE("sls_model", mc->display(tout););
            }
            g->reset();
        }
        else
            mc = nullptr;
    }

    void operator()(goal_ref const& g,
        goal_ref_buffer& result) override {
        result.reset();

        TRACE("sls", g->display(tout););
        tactic_report report("sls", *g);

        model_converter_ref mc;
        run(g, mc);
        g->add(mc.get());
        g->inc_depth();
        result.push_back(g.get());
    }

    void cleanup() override {
        auto* d = alloc(sls::smt_solver, m, m_params);
        std::swap(d, m_sls);
        dealloc(d);
    }

    void collect_statistics(statistics& st) const override {
        st.copy(m_st);
    }

    void reset_statistics() override {
        m_sls->reset_statistics();
        m_st.reset();
    }
};


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

    char const* name() const override { return "sls"; }

    void updt_params(params_ref const & p) override {
        m_params.append(p);
        m_engine->updt_params(m_params);
    }

    void collect_param_descrs(param_descrs & r) override {
        sls_params::collect_param_descrs(r);
    }

    void run(goal_ref const& g, model_converter_ref& mc) {
        if (g->inconsistent()) {
            mc = nullptr;
            return;
        }        
        
        for (unsigned i = 0; i < g->size(); i++)
            m_engine->assert_expr(g->form(i));    
        
        lbool res = m_engine->operator()();
        auto const& stats = m_engine->get_stats();
        if (res == l_true) {
            report_tactic_progress("Number of flips:", stats.m_moves);
            
            for (unsigned i = 0; i < g->size(); i++)
                if (!m_engine->get_mpz_manager().is_one(m_engine->get_value(g->form(i)))) {
                    verbose_stream() << "Terminated before all assertions were SAT!" << std::endl;
                    NOT_IMPLEMENTED_YET();
                }

            if (g->models_enabled()) {
                model_ref mdl = m_engine->get_model();
                mc = model2model_converter(mdl.get());
                TRACE("sls_model", mc->display(tout););
            }
            g->reset();
        }
        else
            mc = nullptr;
        
    }
    
    void operator()(goal_ref const & g, 
                    goal_ref_buffer & result) override {
        result.reset();
        
        TRACE("sls", g->display(tout););
        tactic_report report("sls", *g);
        
        model_converter_ref mc;
        run(g, mc);
        g->add(mc.get());
        g->inc_depth();
        result.push_back(g.get());
    }

    void cleanup() override {
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

static tactic * mk_preamble(ast_manager & m, params_ref const & p, bool add_nnf) {

    params_ref simp2_p = p;
    simp2_p.set_bool("som", true);
    simp2_p.set_bool("pull_cheap_ite", true);
    simp2_p.set_bool("push_ite_bv", false);
    simp2_p.set_bool("local_ctx", true);
    simp2_p.set_uint("local_ctx_limit", 10000000);

    params_ref hoist_p = p;
    hoist_p.set_bool("hoist_mul", true);
    hoist_p.set_bool("som", false);

    params_ref gaussian_p = p;
    // conservative gaussian elimination. 
    gaussian_p.set_uint("gaussian_max_occs", 2); 

    return and_then(
        and_then(mk_simplify_tactic(m, p),
            mk_propagate_values_tactic(m),
            using_params(mk_solve_eqs_tactic(m), gaussian_p),
            mk_elim_uncnstr_tactic(m),
            mk_bv_size_reduction_tactic(m),
            using_params(mk_simplify_tactic(m), simp2_p)),
        using_params(mk_simplify_tactic(m), hoist_p),
        mk_max_bv_sharing_tactic(m),
        add_nnf ? mk_nnf_tactic(m, p) : mk_skip_tactic()
    );
}

tactic * mk_qfbv_sls_tactic(ast_manager & m, params_ref const & p) {
    tactic * t = and_then(mk_preamble(m, p, true), mk_sls_tactic(m, p));
    t->updt_params(p);
    return t;
}


tactic* mk_sls_smt_tactic(ast_manager& m, params_ref const& p) {
    tactic* t = and_then(mk_preamble(m, p, false), alloc(sls_smt_tactic, m, p));
    t->updt_params(p);
    return t;
}
