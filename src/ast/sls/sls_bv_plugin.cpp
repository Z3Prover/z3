/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sls_bv_plugin.cpp

Abstract:

    Theory plugin for bit-vector local search

Author:

    Nikolaj Bjorner (nbjorner) 2024-07-06

--*/
#include "ast/sls/sls_bv_plugin.h"
#include "ast/ast_ll_pp.h"

namespace sls {

    bv_plugin::bv_plugin(context& ctx): 
        plugin(ctx),
        bv(m),
        m_terms(ctx),
        m_eval(m_terms, ctx)
    {}

    void bv_plugin::register_term(expr* e) {
        m_terms.register_term(e);
    }
    
    expr_ref bv_plugin::get_value(expr* e) {
        return expr_ref(m);
    }
    
    lbool bv_plugin::check() {

        if (!m_initialized) {
            auto eval = [&](expr* e, unsigned idx) { return false; };
            m_eval.init_eval(eval);
            m_initialized = true;
        }

        auto& axioms = m_terms.axioms();
        if (!axioms.empty()) {
            for (auto* e : axioms)
                ctx.add_constraint(e);
            axioms.reset();
            return l_undef;
        }

        // repair each root literal
        for (sat::literal lit : ctx.root_literals())
            repair_literal(lit);

        repair_defs_and_updates();

        // update literal assignment based on current model
        for (unsigned v = 0; v < ctx.num_bool_vars(); ++v)
            init_bool_var_assignment(v);

        return ctx.unsat().empty() ? l_true : l_undef;
    }

    void bv_plugin::repair_literal(sat::literal lit) {
        if (!ctx.is_true(lit))
            return;
        auto a = ctx.atom(lit.var());
        if (!a || !is_app(a))
            return;
        if (to_app(a)->get_family_id() != bv.get_family_id())
            return;
        if (!m_eval.eval_is_correct(to_app(a)))
            m_repair_roots.insert(a->get_id());
    }

    void bv_plugin::repair_defs_and_updates() {
        if (!m_repair_roots.empty() || 
            !m_repair_up.empty() || 
            m_repair_down != UINT_MAX) {

            while (m_repair_down != UINT_MAX) {
                auto e = ctx.term(m_repair_down);                
                try_repair_down(to_app(e));
            }
            
            while (!m_repair_up.empty()) {
                auto id = m_repair_up.elem_at(rand() % m_repair_up.size());
                auto e = ctx.term(id);
                m_repair_up.remove(id);
                try_repair_up(to_app(e));
            }

            if (!m_repair_roots.empty()) {
                auto id = m_repair_roots.elem_at(rand() % m_repair_roots.size());
                m_repair_roots.remove(id);
                m_repair_down = id;
            }            
        }
    }

    void bv_plugin::init_bool_var_assignment(sat::bool_var v) {
        auto a = ctx.atom(v);
        if (!a || !is_app(a))
            return;
        if (to_app(a)->get_family_id() != bv.get_family_id())
            return;
        bool is_true = m_eval.bval1(to_app(a));

        if (is_true != ctx.is_true(sat::literal(v, false)))
            ctx.flip(v);        
    }

    bool bv_plugin::is_sat() {
        return false;
    }
    
    std::ostream& bv_plugin::display(std::ostream& out) const {
        // m_eval.display(out);
        return out;
    }
    
    void bv_plugin::set_shared(expr* e) {
    }
    
    void bv_plugin::set_value(expr* e, expr* v) {
    }

    void bv_plugin::try_repair_down(app* e) {

        unsigned n = e->get_num_args();
        if (n == 0 || m_eval.eval_is_correct(e)) {
            m_eval.commit_eval(e);
            if (!m.is_bool(e))
                for (auto p : ctx.parents(e))
                    m_repair_up.insert(p->get_id());
            return;
        }

        if (m.is_bool(e)) {
            NOT_IMPLEMENTED_YET();
            return;
        }

        if (n == 2) {
            auto d1 = get_depth(e->get_arg(0));
            auto d2 = get_depth(e->get_arg(1));
            unsigned s = ctx.rand(d1 + d2 + 2);
            if (s <= d1 && m_eval.try_repair(e, 0)) {
                set_repair_down(e->get_arg(0));
                return;
            }
            if (m_eval.try_repair(e, 1)) {
                set_repair_down(e->get_arg(1));
                return;
            }
            if (m_eval.try_repair(e, 0)) {
                set_repair_down(e->get_arg(0));
                return;
            }
        }
        else {
            unsigned s = ctx.rand(n);
            for (unsigned i = 0; i < n; ++i) {
                auto j = (i + s) % n;
                if (m_eval.try_repair(e, j)) {
                    set_repair_down(e->get_arg(j));
                    return;
                }
            }
        }
        IF_VERBOSE(3, verbose_stream() << "init-repair " << mk_bounded_pp(e, m) << "\n");
        // repair was not successful, so reset the state to find a different way to repair
        m_repair_down = UINT_MAX;
    }

    void bv_plugin::try_repair_up(app* e) {
        if (m.is_bool(e))
            ;
        else if (m_eval.repair_up(e)) {
            if (!m_eval.eval_is_correct(e)) {
                verbose_stream() << "incorrect eval #" << e->get_id() << " " << mk_bounded_pp(e, m) << "\n";
            }
            SASSERT(m_eval.eval_is_correct(e));
            for (auto p : ctx.parents(e))
                m_repair_up.insert(p->get_id());
        }
        else if (ctx.rand(10) != 0) {
            IF_VERBOSE(2, verbose_stream() << "repair-up "; trace_repair(true, e));             
            m_eval.set_random(e);
            m_repair_roots.insert(e->get_id());            
        }
    }

    std::ostream& bv_plugin::trace_repair(bool down, expr* e) {
        verbose_stream() << (down ? "d #" : "u #")
            << e->get_id() << ": "
            << mk_bounded_pp(e, m, 1) << " ";
        return m_eval.display_value(verbose_stream(), e) << "\n";
    }

    void bv_plugin::trace() {
        IF_VERBOSE(2, verbose_stream()
            << "(bvsls :restarts " << m_stats.m_restarts
            << " :repair-up " << m_repair_up.size()
            << " :repair-roots " << m_repair_roots.size() << ")\n");
    }

}
