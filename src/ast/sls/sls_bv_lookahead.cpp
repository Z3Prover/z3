/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sls_bv_lookahead.h

Abstract:

    Lookahead solver for BV, modeled after sls_engine/sls_tracker/sls_evaluator.

Author:

    Nikolaj Bjorner (nbjorner) 2024-12-26

--*/

#include "ast/sls/sls_bv_lookahead.h"
#include "ast/sls/sls_bv_eval.h"
#include "ast/sls/sls_bv_terms.h"
#include "ast/ast_pp.h"

namespace sls {

    bv_lookahead::bv_lookahead(bv_eval& ev) : 
        bv(ev.m), 
        m_ev(ev), 
        ctx(ev.ctx), 
        m(ev.m) {}

    bool bv_lookahead::try_repair_down(app* e) {
        if (!m.is_bool(e))
            return false;
        if (m_ev.bval1(e) == m_ev.bval0(e))
            return true;
        auto const& uninterp = m_ev.terms.uninterp_occurs(e);
        if (uninterp.empty())
            return false;
        reset_updates();

        IF_VERBOSE(4,
            verbose_stream() << mk_bounded_pp(e, m) << "\n";
            for (auto e : uninterp)
                verbose_stream() << mk_bounded_pp(e, m) << " ";
            verbose_stream() << "\n");

        for (auto e : uninterp) 
            add_updates(e);

#if 0
        for (unsigned i = 0; i < m_num_updates; ++i) {
            auto const& [e, score, new_value] = m_updates[i];
            verbose_stream() << mk_bounded_pp(e, m) << " " << new_value << " score: " << score << "\n";
        }
#endif
        
        return apply_update();
    }

    double bv_lookahead::lookahead(expr* e, bvect const& new_value) {
        SASSERT(bv.is_bv(e));
        SASSERT(is_uninterp(e));
        SASSERT(m_restore.empty());

        bool has_tabu = false;
        double break_count = 0, make_count = 0;

        wval(e).eval = new_value;
        if (!insert_update(e)) {
            restore_lookahead();
            return -1000000;
        }
        insert_update_stack(e);
        unsigned max_depth = get_depth(e);
        for (unsigned depth = max_depth; depth <= max_depth; ++depth) {
            for (unsigned i = 0; !has_tabu && i < m_update_stack[depth].size(); ++i) {
                auto e = m_update_stack[depth][i];
                if (bv.is_bv(e)) {
                    auto& v = m_ev.eval(to_app(e));
                    if (insert_update(e)) {
                        for (auto p : ctx.parents(e)) {
                            insert_update_stack(p);
                            max_depth = std::max(max_depth, get_depth(p));
                        }
                    }
                    else
                        has_tabu = true;
                }
                else if (m.is_bool(e) && m_ev.can_eval1(to_app(e))) {
                    if (!ctx.is_relevant(e))
                        continue;
                    bool is_true = ctx.is_true(e);
                    bool is_true_new = m_ev.bval1(to_app(e));
                    bool is_true_old = m_ev.bval1_tmp(to_app(e));
                    if (is_true_new == is_true_old)
                        continue;
                    if (is_true == is_true_new)
                        ++make_count;
                    if (is_true == is_true_old)
                        ++break_count;
                }
                else {
                    IF_VERBOSE(1, verbose_stream() << "skipping " << mk_bounded_pp(e, m) << "\n");
                    has_tabu = true;
                }
            }
            m_update_stack[depth].reset();
        }
        restore_lookahead();
        // verbose_stream() << has_tabu << " " << new_value << " " << make_count << " " << break_count << "\n";

        if (has_tabu)
            return -10000;
        return make_count - break_count;
    }

    void bv_lookahead::try_set(expr* e, bvect const& new_value) {
        if (!wval(e).can_set(new_value))
            return;
        auto d = lookahead(e, new_value);
        if (d > 0)
            add_update(d, e, new_value);
    }

    void bv_lookahead::add_updates(expr* e) {
        SASSERT(bv.is_bv(e));
        auto& v = wval(e);
        double d = 0;
        while (m_v_saved.size() < v.bits().size()) {
            m_v_saved.push_back(0);
            m_v_updated.push_back(0);
        }
        m_v_saved.set_bw(v.bw);
        m_v_updated.set_bw(v.bw);
        v.bits().copy_to(v.nw, m_v_saved);
        m_v_saved.copy_to(v.nw, m_v_updated);

        // flip a single bit
        for (unsigned i = 0; i < v.bw; ++i) {
            m_v_updated.set(i, !m_v_updated.get(i));
            try_set(e, m_v_updated);
            //verbose_stream() << "flip " << d << " " << m_v_updated << "\n";
            m_v_updated.set(i, !m_v_updated.get(i));
        }
        if (v.bw <= 1)
            return;

        // invert
        for (unsigned i = 0; i < v.nw; ++i)
            m_v_updated[i] = ~m_v_updated[i];
        v.clear_overflow_bits(m_v_updated);
        try_set(e, m_v_updated);

        // increment
        m_v_saved.copy_to(v.nw, m_v_updated);
        v.add1(m_v_updated);
        try_set(e, m_v_updated);       

        // decrement
        m_v_saved.copy_to(v.nw, m_v_updated);
        v.sub1(m_v_updated);
        try_set(e, m_v_updated);

        // random
        v.get_variant(m_v_updated, m_ev.m_rand);
        try_set(e, m_v_updated);
    }

    bool bv_lookahead::apply_update() {
        double sum_score = 0;
        for (unsigned i = 0; i < m_num_updates; ++i) 
            sum_score += m_updates[i].score;        
        double pos = (sum_score * m_ev.m_rand()) / (double)m_ev.m_rand.max_value();
        for (unsigned i = 0; i < m_num_updates; ++i) {
            auto const& [e, score, new_value] = m_updates[i];
            pos -= score;
            if (pos <= 0) {
                //verbose_stream() << "apply " << mk_bounded_pp(e, m) << " new value " << new_value << " " << score << "\n";
                apply_update(e, new_value);
                return true;
            }
        }
        return false;
    }

    void bv_lookahead::apply_update(expr* e, bvect const& new_value) {
        SASSERT(bv.is_bv(e));
        SASSERT(is_uninterp(e));
        SASSERT(m_restore.empty());
        wval(e).eval = new_value;
        VERIFY(wval(e).commit_eval());
        insert_update_stack(e);
        unsigned max_depth = get_depth(e);
        for (unsigned depth = max_depth; depth <= max_depth; ++depth) {
            for (unsigned i = 0; i < m_update_stack[depth].size(); ++i) {
                auto e = m_update_stack[depth][i];
                if (bv.is_bv(e)) {
                    m_ev.eval(to_app(e)); // updates wval(e).eval
                    VERIFY(wval(e).commit_eval());
                    for (auto p : ctx.parents(e)) {
                        insert_update_stack(p);
                        max_depth = std::max(max_depth, get_depth(p));
                    }                    
                }
                else if (m.is_bool(e) && m_ev.can_eval1(to_app(e))) {
                    VERIFY(m_ev.repair_up(e));
                }
                else {
                    UNREACHABLE();                    
                }
            }
            m_update_stack[depth].reset();
        }
        m_in_update_stack.reset();        
    }

    bool bv_lookahead::insert_update(expr* e) {
        m_restore.push_back(e);
        m_on_restore.mark(e);
        auto& v = wval(e);
        v.save_value();
        return v.commit_eval();
    }

    void bv_lookahead::insert_update_stack(expr* e) {
        unsigned depth = get_depth(e);
        m_update_stack.reserve(depth + 1);
        if (!m_in_update_stack.is_marked(e)) {
            m_in_update_stack.mark(e);
            m_update_stack[depth].push_back(e);
        }    
    }

    void bv_lookahead::restore_lookahead() {
        for (auto e : m_restore)
            wval(e).restore_value();
        m_restore.reset();
        m_on_restore.reset();
        m_in_update_stack.reset();
    }

    sls::bv_valuation& bv_lookahead::wval(expr* e) const {
        return m_ev.wval(e);
    }

    bool bv_lookahead::on_restore(expr* e) const {
        return m_on_restore.is_marked(e);
    }
}