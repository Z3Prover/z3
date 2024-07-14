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
        m_eval(m_terms, ctx) {
        m_fid = bv.get_family_id();
    }

    void bv_plugin::register_term(expr* e) {
        m_terms.register_term(e);
    }
    
    expr_ref bv_plugin::get_value(expr* e) {
        SASSERT(bv.is_bv(e));
        auto const & val = m_eval.wval(e);
        return expr_ref(bv.mk_numeral(val.get_value(), e->get_sort()), m);
    }

    void bv_plugin::propagate_literal(sat::literal lit) {       
        SASSERT(ctx.is_true(lit));
        auto a = ctx.atom(lit.var());
        if (!a || !is_app(a))
            return;
        if (!m_eval.eval_is_correct(to_app(a)))
            ctx.new_value_eh(a);
    }

    bool bv_plugin::propagate() {
        auto& axioms = m_terms.axioms();
        if (!axioms.empty()) {
            for (auto* e : axioms)
                ctx.add_constraint(e);
            axioms.reset();
            return true;
        }
        return false;
    }

    void bv_plugin::initialize() {
        if (!m_initialized) {
            // compute fixed ranges
            m_initialized = true;
        }
    }

    void bv_plugin::init_bool_var_assignment(sat::bool_var v) {
        auto a = ctx.atom(v);
        if (!a || !is_app(a))
            return;
        if (to_app(a)->get_family_id() != bv.get_family_id())
            return;
        bool is_true = m_eval.bval1(to_app(a));

        if (is_true != ctx.is_true(v))
            ctx.flip(v);        
    }

    bool bv_plugin::is_sat() {
        for (auto t : ctx.subterms())
            if (is_app(t) && bv.is_bv(t) && !m_eval.eval_is_correct(to_app(t)))
                return false;
        return true;
    }
    
    std::ostream& bv_plugin::display(std::ostream& out) const {
        return m_eval.display(out);
    }
    
    void bv_plugin::set_value(expr* e, expr* v) {
        if (!bv.is_bv(e))
            return;
        rational val;
        VERIFY(bv.is_numeral(v, val));
        NOT_IMPLEMENTED_YET();
        // set value of e to val,
    }

    void bv_plugin::repair_down(app* e) {

        unsigned n = e->get_num_args();
        if (n == 0 || m_eval.eval_is_correct(e)) {
            m_eval.commit_eval(e);
            return;
        }

        if (n == 2) {
            auto d1 = get_depth(e->get_arg(0));
            auto d2 = get_depth(e->get_arg(1));
            unsigned s = ctx.rand(d1 + d2 + 2);
            if (s <= d1 && m_eval.try_repair(e, 0)) {
                ctx.new_value_eh(e->get_arg(0));
                return;
            }
            if (m_eval.try_repair(e, 1)) {
                ctx.new_value_eh(e->get_arg(1));
                return;
            }
            if (m_eval.try_repair(e, 0)) {
                ctx.new_value_eh(e->get_arg(0));
                return;
            }
        }
        else {
            unsigned s = ctx.rand(n);
            for (unsigned i = 0; i < n; ++i) {
                auto j = (i + s) % n;
                if (m_eval.try_repair(e, j)) {
                    ctx.new_value_eh(e->get_arg(j));
                    return;
                }
            }
        }
        IF_VERBOSE(3, verbose_stream() << "init-repair " << mk_bounded_pp(e, m) << "\n");
    }

    void bv_plugin::repair_up(app* e) {
        if (!bv.is_bv(e))
            ;
        else if (m_eval.repair_up(e)) {
            if (!m_eval.eval_is_correct(e)) {
                verbose_stream() << "incorrect eval #" << e->get_id() << " " << mk_bounded_pp(e, m) << "\n";
            }
            SASSERT(m_eval.eval_is_correct(e));
            for (auto p : ctx.parents(e))
                ctx.new_value_eh(p);
        }
        else if (ctx.rand(10) != 0) {
            IF_VERBOSE(2, verbose_stream() << "repair-up "; trace_repair(true, e));             
            m_eval.set_random(e);
            ctx.new_value_eh(e);
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
            << "(bvsls :restarts " << m_stats.m_restarts << ")\n");
    }

}
