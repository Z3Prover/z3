/*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  bv_bound_chk_tactic.cpp

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
--*/
#include"bv_bound_chk_tactic.h"
#include"ast.h"
#include"rewriter.h"
#include"rewriter_def.h"
#include"bv_bounds.h"
#include"rewriter_params.hpp"
#include"bool_rewriter.h"
#include"cooperate.h"

struct bv_bound_chk_stats {
    unsigned            m_unsats;
    unsigned            m_singletons;
    unsigned            m_reduces;
    bv_bound_chk_stats() : m_unsats(0), m_singletons(0), m_reduces(0) {};
};

struct bv_bound_chk_rewriter_cfg : public default_rewriter_cfg {
    ast_manager &       m_m;
    unsigned                 m_bv_ineq_consistency_test_max;
    bool_rewriter       m_b_rw;
    unsigned long long  m_max_steps;
    unsigned long long  m_max_memory; // in bytes
    bv_bound_chk_stats& m_stats;
    

    bv_bound_chk_rewriter_cfg(ast_manager & m, bv_bound_chk_stats& stats)
        : m_m(m), m_b_rw(m), m_stats(stats) {}

    ~bv_bound_chk_rewriter_cfg() {}

    void updt_params(params_ref const & _p) {
        rewriter_params p(_p);
        m_bv_ineq_consistency_test_max = p.bv_ineq_consistency_test_max();        
        m_max_memory = p.max_memory();
        m_max_steps = p.max_steps();

    }

    ast_manager & m() const { return m_m; }

    bool rewrite_patterns() const { return false; }

    bool flat_assoc(func_decl * f) const { return true; }

    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
        const br_status st = reduce_app_core(f, num, args, result, result_pr);
        CTRACE("bv_bound_chk_step", st != BR_FAILED,
            tout << f->get_name() << "\n";
        for (unsigned i = 0; i < num; i++) tout << mk_ismt2_pp(args[i], m()) << "\n";
        tout << "---------->\n" << mk_ismt2_pp(result, m()) << "\n";);
        return st;
    }

    br_status reduce_app_core(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
        result_pr = 0;
        const family_id fid = f->get_family_id();
        if (fid != m_b_rw.get_fid()) return BR_FAILED;
        bv_bounds bvb(m());
        const br_status rv = bvb.rewrite(m_bv_ineq_consistency_test_max, f, num, args, result);
        if (rv != BR_FAILED && (m_m.is_false(result) || m_m.is_true(result))) m_stats.m_unsats++;
        else if (rv != BR_FAILED && bvb.singletons().size()) m_stats.m_singletons++;
        else if (rv != BR_FAILED && is_app(result) && to_app(result)->get_num_args() < num) m_stats.m_reduces++;
        return rv;
    }

    bool max_steps_exceeded(unsigned long long num_steps) const {
        cooperate("bv-bound-chk");
        if (num_steps > m_max_steps)
            return true;
        if (memory::get_allocation_size() > m_max_memory)
            throw tactic_exception(TACTIC_MAX_MEMORY_MSG);
        return false;
    }

    void reset_statistics() {
        m_stats.m_unsats = 0;
        m_stats.m_singletons = 0;
        m_stats.m_reduces = 0;
    }

    void collect_statistics(statistics & st) const {
        st.update("unsat bv bounds", m_stats.m_unsats);
        st.update("bv singletons", m_stats.m_singletons);
        st.update("bv reduces", m_stats.m_reduces);
    }
};

struct bv_bound_chk_rewriter : public rewriter_tpl<bv_bound_chk_rewriter_cfg> {
    bv_bound_chk_rewriter_cfg m_cfg;

    bv_bound_chk_rewriter(ast_manager & m, params_ref const & p, bv_bound_chk_stats& stats)
        : rewriter_tpl<bv_bound_chk_rewriter_cfg>(m, false, m_cfg)
        , m_cfg(m, stats)
    {
        updt_params(p);
    }

    virtual ~bv_bound_chk_rewriter() {}

    void updt_params(params_ref const & _p) {
        m_cfg.updt_params(_p);
    }

    void collect_statistics(statistics & st) const {
        m_cfg.collect_statistics(st);
    }


    void reset_statistics() {
        m_cfg.reset_statistics();
    }

};

class bv_bound_chk_tactic : public tactic {
    class imp;
    imp *                       m_imp;
    params_ref                  m_params;
    bv_bound_chk_stats          m_stats;
public:
    bv_bound_chk_tactic(ast_manager & m, params_ref const & p);
    virtual ~bv_bound_chk_tactic();
    void operator()(goal_ref const & g,
        goal_ref_buffer & result,
        model_converter_ref & mc,
        proof_converter_ref & pc,
        expr_dependency_ref & core);
    virtual tactic * translate(ast_manager & m);
    virtual void updt_params(params_ref const & p);
    void cleanup();
    void collect_statistics(statistics & st) const;
    void reset_statistics();
};

class bv_bound_chk_tactic::imp {
    bv_bound_chk_rewriter      m_rw;
public:
    imp(ast_manager & m, params_ref const & p, bv_bound_chk_stats& stats)
        : m_rw(m, p, stats) {    }

    virtual ~imp() {    }

    ast_manager& m() { return m_rw.m(); }

    void operator()(goal_ref const & g) {
        SASSERT(g->is_well_sorted());
        tactic_report report("bv-bound-chk", *g);
        ast_manager& m(g->m());
        expr_ref   new_curr(m);
        const unsigned size = g->size();
        for (unsigned idx = 0; idx < size; idx++) {
            if (g->inconsistent()) break;
            expr * curr = g->form(idx);
            m_rw(curr, new_curr);
            g->update(idx, new_curr);
        }
        m_rw.m_cfg.cleanup();
    }

    virtual void updt_params(params_ref const & p) {
        m_rw.updt_params(p);
    }

    void collect_statistics(statistics & st) const {
        m_rw.collect_statistics(st);
    }

    void reset_statistics() {
        m_rw.reset_statistics();
    }
};

bv_bound_chk_tactic::bv_bound_chk_tactic(ast_manager & m, params_ref const & p)
: m_params(p)
{
    m_imp = alloc(imp, m, p, m_stats);
}


bv_bound_chk_tactic::~bv_bound_chk_tactic() {
    dealloc(m_imp);
}

void bv_bound_chk_tactic::operator()(goal_ref const & g,
        goal_ref_buffer & result,
        model_converter_ref & mc,
        proof_converter_ref & pc,
        expr_dependency_ref & core) {
    SASSERT(g->is_well_sorted());
    fail_if_proof_generation("bv-bound-chk", g);
    fail_if_unsat_core_generation("bv-bound-chk", g);
    TRACE("bv-bound-chk", g->display(tout << "before:"); tout << std::endl;);
    mc = 0; pc = 0; core = 0; result.reset();
    m_imp->operator()(g);
    g->inc_depth();
    result.push_back(g.get());
    TRACE("bv-bound-chk", g->display(tout << "after:"););
    SASSERT(g->is_well_sorted());
}

tactic * bv_bound_chk_tactic::translate(ast_manager & m) {
    return alloc(bv_bound_chk_tactic, m, m_params);
}


void bv_bound_chk_tactic::updt_params(params_ref const & p) {
    m_params = p;
    m_imp->updt_params(p);
}

void bv_bound_chk_tactic::cleanup() {
    imp * d = alloc(imp, m_imp->m(), m_params, m_stats);
    std::swap(d, m_imp);
    dealloc(d);
}

void bv_bound_chk_tactic::collect_statistics(statistics & st) const {
    m_imp->collect_statistics(st);
}

void bv_bound_chk_tactic::reset_statistics() {
    m_imp->reset_statistics();
}


tactic* mk_bv_bound_chk_tactic(ast_manager & m, params_ref const & p) {
    return alloc(bv_bound_chk_tactic, m, p);
}
