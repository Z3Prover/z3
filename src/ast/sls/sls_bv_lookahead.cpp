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
#include <cmath>

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

        if (false && ctx.rand(10) == 0 && apply_random_update(uninterp))
            return true;

        reset_updates();

        TRACE("sls", tout << mk_bounded_pp(e, m) << " contains ";
        for (auto e : uninterp)
            tout << mk_bounded_pp(e, m) << " ";
        tout << "\n";);

        for (auto e : uninterp)
            add_updates(e);

        m_stats.m_num_lookahead += 1;
        m_stats.m_num_updates += m_num_updates;

        TRACE("sls", display_updates(tout));

        if (apply_update())
            return true;

        return apply_random_update(uninterp);
    }

    void bv_lookahead::display_updates(std::ostream& out) {
        for (unsigned i = 0; i < m_num_updates; ++i) {
            auto const& [e, score, new_value] = m_updates[i];
            out << mk_bounded_pp(e, m) << " " << new_value << " score: " << score << "\n";
        }
    }

    bool bv_lookahead::apply_random_update(ptr_vector<expr> const& vars) {
        while (true) {
            expr* e = vars[ctx.rand(vars.size())];
            auto& v = wval(e);
            m_v_updated.set_bw(v.bw);
            v.get_variant(m_v_updated, m_ev.m_rand);
            v.eval = m_v_updated;
            if (!v.commit_eval()) 
                continue;            
            apply_update(e, m_v_updated);
            break;
        }
        return true;
    }

    double bv_lookahead::lookahead(expr* e, bvect const& new_value) {
        SASSERT(bv.is_bv(e));
        SASSERT(is_uninterp(e));
        SASSERT(m_restore.empty());

        bool has_tabu = false;
        int result = 0;
        int breaks = 0;

        wval(e).eval = new_value;
        if (!insert_update(e)) {
            restore_lookahead();
            m_in_update_stack.reset();
            return -1000000;
        }
        insert_update_stack(e);
        unsigned max_depth = get_depth(e);
        for (unsigned depth = max_depth; depth <= max_depth; ++depth) {
            for (unsigned i = 0; !has_tabu && i < m_update_stack[depth].size(); ++i) {
                auto a = m_update_stack[depth][i];
                if (bv.is_bv(a)) {
                    if (a == e || (m_ev.eval(a), insert_update(a))) { // do not insert e twice
                        for (auto p : ctx.parents(a)) {
                            insert_update_stack(p);
                            max_depth = std::max(max_depth, get_depth(p));
                        }
                    }
                    else
                        has_tabu = true;
                }
                else if (m.is_bool(a) && m_ev.can_eval1(a)) {
                    if (!ctx.is_relevant(a))
                        continue;
                    bool is_true = ctx.is_true(a);
                    bool is_true_new = m_ev.bval1(a);
                    bool is_true_old = m_ev.bval1_tmp(a);
                    TRACE("sls_verbose", tout << mk_bounded_pp(a, m) << " " << is_true << " " << is_true_new << " " << is_true_old << "\n");
                    if (is_true_new == is_true_old)
                        continue;
                    if (is_true == is_true_new)
                        ++result;
                    if (is_true == is_true_old) {
                        --result;
                        ++breaks;
                    }
                }
                else {
                    IF_VERBOSE(1, verbose_stream() << "skipping " << mk_bounded_pp(a, m) << "\n");
                    has_tabu = true;
                }
            }
            m_update_stack[depth].reset();
        }
        m_in_update_stack.reset();
        restore_lookahead();

        TRACE("sls_verbose", tout << mk_bounded_pp(e, m) << " " << new_value << " " << result << " " << breaks << "\n");

        if (has_tabu)
            return -10000;
        if (result < 0)
            return 0.0000001;
        else if (result == 0)
            return 0.000002;
        for (int i = m_prob_break.size(); i <= breaks; ++i)
            m_prob_break.push_back(std::pow(m_config.cb, -i));
         return m_prob_break[breaks];
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

        // random, deffered to failure path
        // v.get_variant(m_v_updated, m_ev.m_rand);
        // try_set(e, m_v_updated);
    }

    bool bv_lookahead::apply_update() {
        double sum_score = 0;
        for (unsigned i = 0; i < m_num_updates; ++i) 
            sum_score += m_updates[i].score;        
        double pos = (sum_score * m_ev.m_rand()) / (double)m_ev.m_rand.max_value();
        for (unsigned i = 0; i < m_num_updates; ++i) {
            auto const& [e, score, new_value] = m_updates[i];
            pos -= score;
            if (pos <= 0.00000000001) {
                TRACE("sls", tout << "apply " << mk_bounded_pp(e, m) << " new value " << new_value << " " << score << "\n");
                apply_update(e, new_value);
                return true;
            }
        }
        TRACE("sls", tout << "no update " << m_num_updates << "\n");
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
                    m_ev.eval(e); // updates wval(e).eval
                    if (!wval(e).commit_eval()) {
                        TRACE("sls", tout << "failed to commit " << mk_bounded_pp(e, m) << " " << wval(e) << "\n");
                        // bv_plugin::is_sat picks up discrepancies
                        continue;
                    }
                    for (auto p : ctx.parents(e)) {
                        insert_update_stack(p);
                        max_depth = std::max(max_depth, get_depth(p));
                    }                    
                }
                else if (m.is_bool(e) && m_ev.can_eval1(e)) {
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
        auto& v = wval(e);
        m_restore.push_back(e);
        m_on_restore.mark(e);
        TRACE("sls_verbose", tout << "insert update " << mk_bounded_pp(e, m) << " " << v << "\n");
        v.save_value();
        return v.commit_eval();
    }

    void bv_lookahead::insert_update_stack(expr* e) {
        unsigned depth = get_depth(e);
        m_update_stack.reserve(depth + 1);
        if (!m_in_update_stack.is_marked(e) && is_app(e)) {
            m_in_update_stack.mark(e);
            m_update_stack[depth].push_back(to_app(e));
        }    
    }

    void bv_lookahead::restore_lookahead() {
        for (auto e : m_restore) {
            wval(e).restore_value();
            TRACE("sls_verbose", tout << "restore value " << mk_bounded_pp(e, m) << " " << wval(e) << "\n");
        }
        m_restore.reset();
        m_on_restore.reset();
    }

    sls::bv_valuation& bv_lookahead::wval(expr* e) const {
        return m_ev.wval(e);
    }

    bool bv_lookahead::on_restore(expr* e) const {
        return m_on_restore.is_marked(e);
    }

    void bv_lookahead::collect_statistics(statistics& st) const {
        st.update("sls-bv-lookahead", m_stats.m_num_lookahead);
        st.update("sls-bv-updates", m_stats.m_num_updates);
    }
}