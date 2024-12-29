/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sls_bv_lookahead

Abstract:

    Lookahead solver for BV, modeled after 
    sls_bv_engine/sls_bv_tracker/sls_bv_evaluator
    by Froelich and Wintersteiger.

Author:

    Nikolaj Bjorner (nbjorner) 2024-12-26

--*/

#include "ast/sls/sls_bv_lookahead.h"
#include "ast/sls/sls_bv_eval.h"
#include "ast/sls/sls_bv_terms.h"
#include "params/sls_params.hpp"
#include "ast/ast_pp.h"
#include <cmath>

namespace sls {

    bv_lookahead::bv_lookahead(bv_eval& ev) :
        bv(ev.m),
        m_ev(ev),
        ctx(ev.ctx),
        m(ev.m) {
    }

    void bv_lookahead::init_updates() {
        m_best_expr = nullptr;
    }

    lbool bv_lookahead::search() {
        updt_params(ctx.get_params());
        rescore();
        m_config.max_moves = m_stats.m_moves + m_config.max_moves_base;

        while (m.inc() && m_stats.m_moves < m_config.max_moves) {
            m_stats.m_moves++;
            check_restart();

            // get candidate variables
            auto& vars = get_candidate_uninterp();

            if (vars.empty())
                return l_true;

            // random walk with probability 1000/wp 
            if (ctx.rand(10) < m_config.wp && apply_random_update(vars))
                continue;

            if (apply_guided_update(vars))
                continue;

            apply_random_update(vars);
            recalibrate_weights();
        }
        m_config.max_moves_base += 100;
        return l_undef;
    }

    bool bv_lookahead::apply_guided_update(ptr_vector<expr> const& vars) {
        init_updates();
        double old_top_score = m_top_score;
        for (auto u : vars)
            add_updates(u);
        m_top_score = old_top_score;
        return apply_update();
    }

    ptr_vector<expr> const& bv_lookahead::get_candidate_uninterp() {
        auto const& lits = ctx.root_literals();
        unsigned start = ctx.rand(lits.size());
        for (unsigned i = 0; i < lits.size(); ++i) {
            auto lit = lits[(i + start) % lits.size()];
            auto e = ctx.atom(lit.var());
            if (!e || !is_app(e))
                continue;
            app* a = to_app(e);
            if (!m_ev.can_eval1(a))
                continue;
            if (m_ev.bval0(a) == m_ev.bval1(a))
                continue;
            auto const& vars = m_ev.terms.uninterp_occurs(a);
            VERIFY(!vars.empty());
            TRACE("bv", tout << "candidates " << mk_bounded_pp(e, m) << ": ";
            for (auto e : vars)
                tout << mk_bounded_pp(e, m) << " ";
            tout << "\n";);
            return vars;
        }
        return m_vars;
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

    void bv_lookahead::check_restart() {

        if (m_stats.m_moves % m_config.restart_base == 0)
            // ucb_forget();
            rescore();

        if (m_stats.m_moves < m_config.restart_next)
            return;

        if (m_stats.m_restarts & 1)
            m_config.restart_next += m_config.restart_base;
        else
            m_config.restart_next += (2 << (m_stats.m_restarts >> 1)) * m_config.restart_base;

        m_stats.m_restarts++;

        // TODO: reset values of uninterpreted to 0        
    }

    void bv_lookahead::updt_params(params_ref const& _p) {
        sls_params p(_p);
        //m_config.max_restarts = p.max_restarts();
        m_config.walksat = p.walksat();
        m_config.walksat_repick = p.walksat_repick();
        m_config.paws_sp = p.paws_sp();
        m_config.paws = m_config.paws_sp < 1024;
        m_config.wp = p.wp();
        m_config.restart_base = p.restart_base();
        m_config.restart_next = m_config.restart_base;
        m_config.restart_init = p.restart_init();
        m_config.early_prune = p.early_prune();
    }

    double bv_lookahead::new_score(app* a) {
        bool is_true = ctx.is_true(a);
        bool is_true_new = m_ev.bval1(a);
        if (!ctx.is_relevant(a))
            return 0;
        if (is_true == is_true_new)
            return 1;
        expr* x, * y;
        if (is_true && m.is_eq(a, x, y) && bv.is_bv(x)) {
            auto const& vx = wval(x);
            auto const& vy = wval(y);
            // hamming distance between vx.bits() and vy.bits():
            double delta = 0;
            for (unsigned i = 0; i < vx.bw; ++i)
                if (vx.bits().get(i) != vy.bits().get(i))
                    ++delta;
            return 1 - (delta / vx.bw);
        }
        else if (bv.is_ule(a, x, y)) {
            auto const& vx = wval(x);
            auto const& vy = wval(y);

            if (is_true)
                // x > y as unsigned.
                // x - y > 0
                // score = (x - y) / 2^bw
                vx.set_sub(m_ev.m_tmp, vx.bits(), vy.bits());
            else {
                // x <= y as unsigned.
                // y - x >= 0
                // score = (y - x + 1) / 2^bw
                vx.set_sub(m_ev.m_tmp, vy.bits(), vx.bits());
                vx.add1(m_ev.m_tmp);
            }
            rational n = m_ev.m_tmp.get_value(vx.nw);
            n /= rational(rational::power_of_two(vx.bw));
            double dbl = n.get_double();
            return (dbl > 1.0) ? 0.0 : (dbl < 0.0) ? 1.0 : 1.0 - dbl;
        }
        else if (bv.is_sle(a, x, y)) {
            auto const& vx = wval(x);
            auto const& vy = wval(y);
            // x += 2^bw-1
            // y += 2^bw-1
            vy.bits().copy_to(vy.nw, m_ev.m_tmp);
            vx.bits().copy_to(vx.nw, m_ev.m_tmp2);
            m_ev.m_tmp.set(vy.bw - 1, !m_ev.m_tmp.get(vy.bw - 1));
            m_ev.m_tmp2.set(vx.bw - 1, !m_ev.m_tmp2.get(vx.bw - 1));

            if (is_true) {
                // x >s y
                // x' - y' > 0
                vx.set_sub(m_ev.m_tmp3, m_ev.m_tmp2, m_ev.m_tmp);
            }
            else {
                // x <=s y
                // y' - x' >= 0
                vx.set_sub(m_ev.m_tmp3, m_ev.m_tmp, m_ev.m_tmp2);
                vx.add1(m_ev.m_tmp3);
            }
            rational n = m_ev.m_tmp3.get_value(vx.nw);
            n /= rational(rational::power_of_two(vx.bw));
            double dbl = n.get_double();
            return (dbl > 1.0) ? 0.0 : (dbl < 0.0) ? 1.0 : 1.0 - dbl;
        }
        else if (is_true && m.is_distinct(a) && bv.is_bv(a->get_arg(0))) {
            double np = 0, nd = 0;
            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                auto const& vi = wval(a->get_arg(i));
                for (unsigned j = i + 1; j < a->get_num_args(); ++j) {
                    ++np;
                    auto const& vj = wval(a->get_arg(j));
                    if (vi.bits() != vj.bits())
                        nd++;
                }
            }
            return nd / np;
        }

        return 0;
    }

    double bv_lookahead::lookahead(expr* e, bvect const& new_value) {
        SASSERT(bv.is_bv(e));
        SASSERT(is_uninterp(e));
        SASSERT(m_restore.empty());

        bool has_tabu = false;

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

                    rescore(a);
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

        TRACE("sls_verbose", tout << mk_bounded_pp(e, m) << " := " << new_value << " score: " << m_top_score << "\n");

        if (has_tabu)
            return -10000;
        if (m_top_score <= 0.000001)
            return -10000;
        return m_top_score;
    }

    void bv_lookahead::try_set(expr* u, bvect const& new_value) {
        if (!wval(u).can_set(new_value))
            return;
        auto score = lookahead(u, new_value);
        ++m_stats.m_num_updates;
        verbose_stream() << mk_bounded_pp(u, m) << " " << new_value << " score: " << score << "\n";
        if (score > m_best_score) {
            m_best_score = score;
            m_best_expr = u;
            m_best_value.set_bw(new_value.bw);
            new_value.copy_to(new_value.nw, m_best_value);
        }
    }

    void bv_lookahead::add_updates(expr* u) {
        SASSERT(bv.is_bv(u));
        auto& v = wval(u);
        while (m_v_saved.size() < v.bits().size()) {
            m_v_saved.push_back(0);
            m_v_updated.push_back(0);
            m_best_value.push_back(0);
        }

        m_v_saved.set_bw(v.bw);
        m_v_updated.set_bw(v.bw);
        v.bits().copy_to(v.nw, m_v_saved);
        m_v_saved.copy_to(v.nw, m_v_updated);

        // flip a single bit
        for (unsigned i = 0; i < v.bw && i <= 32; ++i) {
            m_v_updated.set(i, !m_v_updated.get(i));
            try_set(u, m_v_updated);
            m_v_updated.set(i, !m_v_updated.get(i));
        }
        if (v.bw > 32) {
            unsigned j = ctx.rand(v.bw - 32) + 32;
            m_v_updated.set(j, !m_v_updated.get(j));
            try_set(u, m_v_updated);
            m_v_updated.set(j, !m_v_updated.get(j));
        }
        if (v.bw <= 1)
            return;

        // invert
        for (unsigned i = 0; i < v.nw; ++i)
            m_v_updated[i] = ~m_v_updated[i];
        v.clear_overflow_bits(m_v_updated);
        try_set(u, m_v_updated);

        // increment
        m_v_saved.copy_to(v.nw, m_v_updated);
        v.add1(m_v_updated);
        try_set(u, m_v_updated);

        // decrement
        m_v_saved.copy_to(v.nw, m_v_updated);
        v.sub1(m_v_updated);
        try_set(u, m_v_updated);

        // reset to original value
        try_set(u, m_v_saved);
    }

    bool bv_lookahead::apply_update() {
        CTRACE("bv", !m_best_expr, tout << "no update\n");
        if (!m_best_expr)
            return false;
        apply_update(m_best_expr, m_best_value);
        return true;       
    }

    void bv_lookahead::apply_update(expr* e, bvect const& new_value) {
        TRACE("bv", tout << "apply " << mk_bounded_pp(e, m) << " new value " << new_value << "\n");
        SASSERT(bv.is_bv(e));
        SASSERT(is_uninterp(e));
        SASSERT(m_restore.empty());
        wval(e).eval = new_value;

        //verbose_stream() << mk_bounded_pp(e, m) << " := " << new_value << "\n";

        VERIFY(wval(e).commit_eval());
        insert_update_stack(e);
        unsigned max_depth = get_depth(e);
        for (unsigned depth = max_depth; depth <= max_depth; ++depth) {
            for (unsigned i = 0; i < m_update_stack[depth].size(); ++i) {
                auto e = m_update_stack[depth][i];
                if (bv.is_bv(e)) {
                    m_ev.eval(e); // updates wval(e).eval
                    if (!wval(e).commit_eval()) {
                        TRACE("bv", tout << "failed to commit " << mk_bounded_pp(e, m) << " " << wval(e) << "\n");
                        // bv_plugin::is_sat picks up discrepancies
                        continue;
                    }
                    for (auto p : ctx.parents(e)) {
                        insert_update_stack(p);
                        max_depth = std::max(max_depth, get_depth(p));
                    }
                }
                else if (m.is_bool(e) && m_ev.can_eval1(e)) {
                    rescore(e);
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

    unsigned bv_lookahead::get_weight(expr* e) {
        return m_bool_info.insert_if_not_there(e, { m_config.paws_init, 0 }).weight;
    }

    void bv_lookahead::inc_weight(expr* e) {
        m_bool_info.insert_if_not_there(e, { m_config.paws_init, 0 }).weight += 1;
    }

    void bv_lookahead::dec_weight(expr* e) {
        auto& w = m_bool_info.insert_if_not_there(e, { m_config.paws_init, 0 }).weight;
        w = w > m_config.paws_init ? w - 1 : m_config.paws_init;
    }

    void bv_lookahead::set_score(app* a, double d) {
        m_bool_info.insert_if_not_there(a, { m_config.paws_init, 0 }).score = d;
    }

    double bv_lookahead::old_score(app* a) {
        return m_bool_info.insert_if_not_there(a, { m_config.paws_init, 0 }).score;
    }

    void bv_lookahead::rescore() {
        m_top_score = 0;
        m_rescore = false;
        for (auto lit : ctx.root_literals()) {
            auto e = ctx.atom(lit.var());
            if (!e || !is_app(e))
                continue;
            app* a = to_app(e);
            if (!m_ev.can_eval1(a))
                continue;

            double score = new_score(a);
            set_score(a, score);
            m_top_score += score;
        }
        verbose_stream() << "top score " << m_top_score << "\n";

    }

    void bv_lookahead::rescore(app* e) {
        double score = new_score(e);
        m_top_score += get_weight(e) * (score - old_score(e));
        set_score(e, score);
    }

    void bv_lookahead::recalibrate_weights() {
        for (auto lit : ctx.root_literals()) {
            auto e = ctx.atom(lit.var());
            if (!e || !is_app(e))
                continue;
            app* a = to_app(e);
            if (!m_ev.can_eval1(a))
                continue;
            bool is_true = ctx.is_true(lit);
            bool is_true_a = m_ev.bval1(a);
            if (ctx.rand(10) < m_config.paws_sp) {
                if (is_true == is_true_a)
                    dec_weight(a);
            }
            else if (is_true != is_true_a)
                inc_weight(a);
        }
        m_best_score = 0;
    }

    void bv_lookahead::collect_statistics(statistics& st) const {
        st.update("sls-bv-lookahead", m_stats.m_num_lookahead);
        st.update("sls-bv-updates", m_stats.m_num_updates);
        st.update("sls-bv-moves", m_stats.m_moves);
    }
}