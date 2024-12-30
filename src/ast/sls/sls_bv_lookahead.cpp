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

    /**
    * Main entry point. The lookahead solver is invoked periodically
    * before any other propagation with the main BV solver. 
    */
    void bv_lookahead::start_propagation() {
        if (m_stats.m_num_propagations++ % m_config.propagation_base == 0) 
            search();        
    }

    /**
    * Main search loop. 
    * - Selects candidate variables
    * - Applies random moves with a small probability
    * - Applies guided moves to reduce cost of false literals
    * - Applies random updates if no progress is made
    */

    void bv_lookahead::search() {
        updt_params(ctx.get_params());
        rescore();
        m_config.max_moves = m_stats.m_moves + m_config.max_moves_base;

        while (m.inc() && m_stats.m_moves < m_config.max_moves) {
            m_stats.m_moves++;
            check_restart();

            // get candidate variables
            auto& vars = get_candidate_uninterp();

            if (vars.empty())
                return;

            // random walk  
            if (ctx.rand(2047) < m_config.wp && apply_random_move(vars))
                continue;

            // guided moves, greedily reducing cost of false literals
            if (apply_guided_move(vars))
                continue;

            // bail out if no progress, and try random update
            if (apply_random_update(get_candidate_uninterp()))
                recalibrate_weights();
        }
        m_config.max_moves_base += 100;
    }

    /**
    * guided move: apply lookahead search for the selected variables
    * and possible moves
    */
    bool bv_lookahead::apply_guided_move(ptr_vector<expr> const& vars) {
        m_best_expr = nullptr;
        m_best_score = m_top_score;
        unsigned sz = vars.size();
        unsigned start = ctx.rand();
        for (unsigned i = 0; i < sz; ++i)
            add_updates(vars[(start + i) % sz]);
        CTRACE("bv", !m_best_expr, tout << "no guided move\n";);
        return apply_update(m_best_expr, m_best_value, "increasing move");
    }

    /**
    * random update: select a variable at random and set bits to random values
    */
    bool bv_lookahead::apply_random_update(ptr_vector<expr> const& vars) {  
        expr* e = vars[ctx.rand(vars.size())];
        auto& v = wval(e);
        m_v_updated.set_bw(v.bw);
        v.get_variant(m_v_updated, m_ev.m_rand);
        return apply_update(e, m_v_updated, "random update");
    }

    /**
    * random move: select a variable at random and use one of the moves: flip, add1, sub1
    */
    bool bv_lookahead::apply_random_move(ptr_vector<expr> const& vars) {
        expr* e = vars[ctx.rand(vars.size())];
        auto& v = wval(e);
        m_v_updated.set_bw(v.bw);
        v.bits().copy_to(v.nw, m_v_updated);
        switch (ctx.rand(3)) {
        case 0: {
            // flip a random bit
            auto bit = ctx.rand(v.bw);
            m_v_updated.set(bit, !m_v_updated.get(bit));
            break;
        }
        case 1:
            v.add1(m_v_updated);
            break;
        default:
            v.sub1(m_v_updated);
            break;
        }
        return apply_update(e, m_v_updated, "random move");
    }

    /**
    * Retrieve a candidate top-level predicate that is false, give preference to
    * those with high score, but back off if they are frequently chosen.
    */
    ptr_vector<expr> const& bv_lookahead::get_candidate_uninterp() {
        auto const& lits = ctx.root_literals();
        app* e = nullptr;
        if (m_config.ucb) {
            double max = -1.0;
            for (auto lit : ctx.root_literals()) {
                if (!is_false_bv_literal(lit))
                    continue;
                auto a = to_app(ctx.atom(lit.var()));
                auto score = old_score(a);
                auto q = score
                    + m_config.ucb_constant * sqrt(log((double)m_touched) / get_touched(a))
                    + m_config.ucb_noise * ctx.rand(512);
                if (q > max)
                    max = q, e = a;
            }
            if (e) {
                m_touched++;
                inc_touched(e);
            }
        }
        else {
            unsigned n = 0;
            for (auto lit : ctx.root_literals())
                if (is_false_bv_literal(lit) && ctx.rand() % ++n == 0)
                    e = to_app(ctx.atom(lit.var()));
        }
        if (!e)
            return m_empty_vars;

        auto const& vars = m_ev.terms.uninterp_occurs(e);
        VERIFY(!vars.empty());
        TRACE("bv", tout << "candidates " << mk_bounded_pp(e, m) << ": ";
        for (auto e : vars) tout << mk_bounded_pp(e, m) << " ";
        tout << "\n";);
        return vars;
    }

    void bv_lookahead::check_restart() {
        
        if (m_stats.m_moves % m_config.restart_base == 0) {
            ucb_forget();
            rescore();
        }

        if (m_stats.m_moves < m_config.restart_next)
            return;

        ++m_stats.m_restarts;

        if (0x1 == (m_stats.m_restarts & 0x1))
            m_config.restart_next += m_config.restart_base;
        else
            m_config.restart_next += (2 << (m_stats.m_restarts >> 1)) * m_config.restart_base;

        reset_uninterp_in_false_literals(); 
        rescore();
    }

    /**
    * Reset variables that occur in false literals.
    */
    void bv_lookahead::reset_uninterp_in_false_literals() {
        auto const& lits = ctx.root_literals();
        expr_mark marked;
        for (auto lit : ctx.root_literals()) {
            if (!is_false_bv_literal(lit))
                continue;
            app* a = to_app(ctx.atom(lit.var()));
            auto const& occs = m_ev.terms.uninterp_occurs(a);
            for (auto e : occs) {
                if (marked.is_marked(e))
                    continue;
                marked.mark(e);
                auto& v = wval(e);
                m_v_updated.set_bw(v.bw);
                m_v_updated.set_zero();
                apply_update(e, m_v_updated, "reset");                
            }
        }
    }

    bool bv_lookahead::is_bv_literal(sat::literal lit) {
        if (!ctx.is_true(lit))
            return false;
        auto e = ctx.atom(lit.var());
        if (!e || !is_app(e))
            return false;
        app* a = to_app(e);
        return m_ev.can_eval1(a);
    }

    bool bv_lookahead::is_false_bv_literal(sat::literal lit) {
        if (!is_bv_literal(lit))
            return false;
        app* a = to_app(ctx.atom(lit.var()));
        return (m_ev.bval0(a) != m_ev.bval1(a));
    }

   
    void bv_lookahead::updt_params(params_ref const& _p) {
        sls_params p(_p);
        m_config.walksat = p.walksat();
        m_config.walksat_repick = p.walksat_repick();
        m_config.paws_sp = p.paws_sp();
        m_config.paws = m_config.paws_sp < 1024;
        m_config.wp = p.wp();
        m_config.restart_base = p.restart_base();
        m_config.restart_next = m_config.restart_base;
        m_config.restart_init = p.restart_init();
        m_config.early_prune = p.early_prune();
        m_config.ucb = p.walksat_ucb();
        m_config.ucb_constant = p.walksat_ucb_constant();
        m_config.ucb_forget = p.walksat_ucb_forget();
        m_config.ucb_init = p.walksat_ucb_init();
        m_config.ucb_noise = p.walksat_ucb_noise();
    }

    /**
    * Score of a predicate based on how close the current
    * solution is to satisfying it. The proximity measure is
    * based on hamming distance for equalities, and differences
    * for inequalities.
    */
    double bv_lookahead::new_score(app* a) {
        bool is_true = ctx.is_true(a);
        bool is_true_new = m_ev.bval1(a);
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
            auto d = 1.0 - (delta / (double)vx.bw);
            //verbose_stream() << "hamming distance " << mk_bounded_pp(a, m) << " " << d << "\n";
            return d;
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

    /**
    * Rehearse an update. The update is revered while a score is computed and returned.
    * Walk all parents, until hitting predicates where their scores are computed.
    */
    double bv_lookahead::lookahead_update(expr* e, bvect const& new_value) {
        SASSERT(bv.is_bv(e));
        SASSERT(is_uninterp(e));
        SASSERT(m_restore.empty());

        bool has_tabu = false;
        double score = m_top_score;

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
                    else {
                        IF_VERBOSE(1, verbose_stream() << "tabu " << mk_bounded_pp(a, m) << "\n");
                        has_tabu = true;
                    }
                }
                else if (is_root(a)) {
                     score += get_weight(a) * (new_score(a) - old_score(a));
                }
                else if (m.is_bool(a))
                    continue;
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
        return score;
    }

    void bv_lookahead::try_set(expr* u, bvect const& new_value) {
        if (!wval(u).can_set(new_value))
            return;
        auto score = lookahead_update(u, new_value);
        ++m_stats.m_num_updates;
        //verbose_stream() << mk_bounded_pp(u, m) << " := " << new_value << " score: " << score << "\n";
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

        // increment
        m_v_saved.copy_to(v.nw, m_v_updated);
        v.add1(m_v_updated);
        try_set(u, m_v_updated);

        // decrement
        m_v_saved.copy_to(v.nw, m_v_updated);
        v.sub1(m_v_updated);
        try_set(u, m_v_updated);

        // invert
        m_v_saved.copy_to(v.nw, m_v_updated);
        for (unsigned i = 0; i < v.nw; ++i)
            m_v_updated[i] = ~m_v_updated[i];
        v.clear_overflow_bits(m_v_updated);
        try_set(u, m_v_updated);
    }

    /**
    * Apply an update to a variable.
    * The update is committed.
    */

    bool bv_lookahead::apply_update(expr* e, bvect const& new_value, char const* reason) {
        SASSERT(bv.is_bv(e));
        SASSERT(is_uninterp(e));
        SASSERT(m_restore.empty());
        if (!e || !wval(e).can_set(new_value))
            return false;
        wval(e).eval = new_value;
        double old_top_score = m_top_score;

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
                        IF_VERBOSE(2, verbose_stream() << "failed to commit " << mk_bounded_pp(e, m) << " " << wval(e) << "\n");
                        // bv_plugin::is_sat picks up discrepancies
                        continue;
                    }
                    for (auto p : ctx.parents(e)) {
                        insert_update_stack(p);
                        max_depth = std::max(max_depth, get_depth(p));
                    }
                }
                else if (is_root(e)) {
                    double score = new_score(e);
                    m_top_score += get_weight(e) * (score - old_score(e));
                    set_score(e, score);
                }
                else if (m.is_bool(e))
                    continue;
                else {
                    UNREACHABLE();
                }
            }
            m_update_stack[depth].reset();
        }
        m_in_update_stack.reset();
        TRACE("bv", tout << reason << " " << mk_bounded_pp(m_best_expr, m)
            << " := " << new_value
            << " score " << m_top_score << "\n";);
        return true;
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

    bv_lookahead::bool_info& bv_lookahead::get_bool_info(expr* e) {
        return m_bool_info.insert_if_not_there(e, { m_config.paws_init, 0, 1});
    }

    void bv_lookahead::dec_weight(expr* e) {
        auto& w = get_bool_info(e).weight;
        w = w > m_config.paws_init ? w - 1 : m_config.paws_init;
    }

    void bv_lookahead::rescore() {
        m_top_score = 0;
        m_is_root.reset();
        for (auto lit : ctx.root_literals()) {
            if (!is_bv_literal(lit))
                continue;
            auto a = to_app(ctx.atom(lit.var()));
            double score = new_score(a);
            set_score(a, score);
            m_top_score += score;
            m_is_root.mark(a);
        }
    }

    void bv_lookahead::recalibrate_weights() {
        for (auto lit : ctx.root_literals()) {
            if (!is_bv_literal(lit))
                continue;
            auto a = to_app(ctx.atom(lit.var()));
            bool is_true0 = m_ev.bval0(a);
            bool is_true1 = m_ev.bval1(a);
            if (ctx.rand(2047) < m_config.paws_sp) {
                if (is_true0 == is_true1)
                    dec_weight(a);
            }
            else if (is_true0 != is_true1)
                inc_weight(a);
        }

        IF_VERBOSE(20, display_weights(verbose_stream()));       
    }

    std::ostream& bv_lookahead::display_weights(std::ostream& out) {

        for (auto lit : ctx.root_literals()) {
            if (!is_bv_literal(lit))
                continue;
            auto a = to_app(ctx.atom(lit.var()));
            out
                << get_weight(a) << " "
                << mk_bounded_pp(a, m) << " "
                << old_score(a) << "\n";
        }
        return out;
    }

    void bv_lookahead::ucb_forget() {
        if (m_config.ucb_forget >= 1.0)
            return;
        for (auto lit : ctx.root_literals()) {
            if (!is_bv_literal(lit))
                continue;
            auto a = to_app(ctx.atom(lit.var()));
            auto touched_old = get_touched(a);
            auto touched_new = static_cast<unsigned>((touched_old - 1) * m_config.ucb_forget + 1);
            set_touched(a, touched_new);
            m_touched += touched_new - touched_old;
        }
    }

    void bv_lookahead::collect_statistics(statistics& st) const {
        st.update("sls-bv-lookahead", m_stats.m_num_lookahead);
        st.update("sls-bv-updates", m_stats.m_num_updates);
        st.update("sls-bv-moves", m_stats.m_moves);
        st.update("sls-bv-restarts", m_stats.m_restarts);
    }
}