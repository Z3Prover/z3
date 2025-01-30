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
        if (m_stats.m_propagations++ % m_config.propagation_base == 0) 
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
        if (!m_config.use_lookahead_bv)
            return;
        flet<bool> _set_use_tmp(m_ev.m_use_tmp_bool_value, true);
        initialize_bool_values();
        rescore();
        m_config.max_moves = m_stats.m_moves + m_config.max_moves_base;
        TRACE("bv", tout << "search " << m_stats.m_moves << " " << m_config.max_moves << "\n";);
        IF_VERBOSE(1, verbose_stream() << "lookahead-search moves:" << m_stats.m_moves << " max-moves:" << m_config.max_moves << "\n");

        while (ctx.rlimit().inc() && m_stats.m_moves < m_config.max_moves) {
            m_stats.m_moves++;
            check_restart();

            // get candidate variables
            auto& vars = get_candidate_uninterp();

            if (vars.empty()) {
                finalize_bool_values();
                return;
            }

            // random walk  
            if (ctx.rand(2047) < m_config.wp && apply_random_move(vars))
                continue;

            // guided moves, greedily reducing cost of false literals
            if (apply_guided_move(vars))
                continue;

            // bail out if no progress, and try random update
            if (apply_random_update(m_config.walksat_repick?get_candidate_uninterp():vars))
                recalibrate_weights();
        }
        m_config.max_moves_base += 100;
    }

    void bv_lookahead::initialize_bool_values() {
        m_ev.restore_bool_values(0);
        for (auto t : ctx.subterms()) {
            if (bv.is_bv(t)) {
                auto& v = m_ev.eval(to_app(t));
                v.commit_eval_ignore_tabu();
            }
            else if (m.is_bool(t)) {
                auto b = m_ev.bval1(t);
                m_ev.set_bool_value_no_log(t, b);

            }
        }
        m_ev.commit_bool_values();
    }
    

    /**
    * Flip truth values of root literals if they are updated.
    */
    void bv_lookahead::finalize_bool_values() {
        for (unsigned v = ctx.num_bool_vars(); v-- > 0; ) {
            auto a = ctx.atom(v);
            if (!a)
                continue;
            if (m_ev.get_bool_value(a) != ctx.is_true(v))
                ctx.flip(v);
        }
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
        return apply_update(m_last_atom, m_best_expr, m_best_value, move_type::guided_t);
    }

    /**
    * random update: select a variable at random and set bits to random values
    */
    bool bv_lookahead::apply_random_update(ptr_vector<expr> const& vars) {  
        if (vars.empty())
            return false;
        expr* e = vars[ctx.rand(vars.size())];
        if (m.is_bool(e)) {
            if (is_root(e))
                return false;
        }
        else {
            SASSERT(bv.is_bv(e));
            auto& v = wval(e);
            m_v_updated.set_bw(v.bw);
            v.get_variant(m_v_updated, m_ev.m_rand);
        }
        ++m_stats.m_random_flips;
        return apply_update(m_last_atom, e, m_v_updated, move_type::random_t);
    }


    /**
    * random move: select a variable at random and use one of the moves: flip, add1, sub1
    */
    bool bv_lookahead::apply_random_move(ptr_vector<expr> const& vars) {
        if (vars.empty())
            return false;
        expr* e = vars[ctx.rand(vars.size())];
        TRACE("bv", tout << "random move " << mk_bounded_pp(e, m) << "\n";);
        if (m.is_bool(e)) {
            if (is_root(e))
                return false;
        }
        else {
            SASSERT(bv.is_bv(e));
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
        }
        return apply_update(m_last_atom, e, m_v_updated, move_type::move_t);
    }

    /**
    * Retrieve a candidate top-level predicate that is false, give preference to
    * those with high score, but back off if they are frequently chosen.
    */
    ptr_vector<expr> const& bv_lookahead::get_candidate_uninterp() {
        expr* e = nullptr;
        if (m_config.ucb) {
            double max = -1.0;
            TRACE("bv", tout << "select\n");
            for (auto a : get_root_assertions()) {
                auto const& vars = m_ev.terms.uninterp_occurs(a);
                //verbose_stream() << mk_bounded_pp(a, m) << " " << assertion_is_true(a) << " num vars " << vars.size() << "\n";
                if (assertion_is_true(a))
                    continue;

                if (vars.empty())
                    continue;
                auto score = old_score(a);
                TRACE("bv", tout << "score " << score << "  " << mk_bounded_pp(a, m) << "\n");
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
            for (auto a : get_root_assertions())
                if (!assertion_is_true(a) && !m_ev.terms.uninterp_occurs(e).empty() && ctx.rand() % ++n == 0)
                    e = a;
        }
        CTRACE("bv", !e, ; display_weights(ctx.display(tout << "no candidate\n")););

        m_last_atom = e;

        if (!e)
            return m_empty_vars;

        auto const& vars = m_ev.terms.uninterp_occurs(e);

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
        m_config.restart_next = std::max(m_config.restart_next, m_stats.m_moves);

        if (0x1 == (m_stats.m_restarts & 0x1))
            m_config.restart_next += m_config.restart_base;
        else
            m_config.restart_next += (2 * (m_stats.m_restarts >> 1)) * m_config.restart_base;

        reset_uninterp_in_false_literals(); 
        rescore();
    }

    /**
    * Reset variables that occur in false literals.
    */
    void bv_lookahead::reset_uninterp_in_false_literals() {
        expr_mark marked;
        for (auto a : get_root_assertions()) {
            if (assertion_is_true(a))
                continue;
            auto const& occs = m_ev.terms.uninterp_occurs(a);
            for (auto e : occs) {
                if (!bv.is_bv(e))
                    continue;
                if (marked.is_marked(e))
                    continue;
                marked.mark(e);
                auto& v = wval(e);
                m_v_updated.set_bw(v.bw);
                m_v_updated.set_zero();
                apply_update(nullptr, e, m_v_updated, move_type::reset_t);                
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

    bool bv_lookahead::assertion_is_true(expr* a) {
        if (m_config.use_top_level_assertions)
            return m_ev.get_bool_value(a);
        return !m_ev.can_eval1(a) || m_ev.bval0(a) == m_ev.bval1(a);
    }
   
    void bv_lookahead::updt_params(params_ref const& _p) {
        sls_params p(_p);
        if (m_config.config_initialized)
            return;
        m_config.config_initialized = true;
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
        m_config.use_top_level_assertions = p.bv_use_top_level_assertions();
        m_config.use_lookahead_bv = p.bv_use_lookahead();
        m_config.allow_rotation = p.bv_allow_rotation();
    }

    /**
    * Score of a predicate based on how close the current
    * solution is to satisfying it. The proximity measure is
    * based on hamming distance for equalities, and differences
    * for inequalities.
    */
    double bv_lookahead::new_score(expr* a) {
        if (m_config.use_top_level_assertions)
            return new_score(a, true);
        else
            return new_score(a, m_ev.bval0(a));
    }

    double bv_lookahead::new_score(expr* a, bool is_true) {
        bool is_true_new = m_ev.get_bool_value(a);
        
        //verbose_stream() << "compute score " << mk_bounded_pp(a, m) << " is-true " << is_true << " is-true-new " << is_true_new << "\n";
        if (is_true == is_true_new)
            return 1;
        if (is_uninterp(a))
            return 0;
        if (m.is_true(a))
            return is_true ? 1 : 0;
        if (m.is_false(a))
            return is_true ? 0 : 1;
        expr* x, * y, * z;
        if (m.is_not(a, x))
            return new_score(x, !is_true);
        if ((m.is_and(a) && is_true) || (m.is_or(a) && !is_true)) {
            double score = 1;
            for (auto arg : *to_app(a))
                score = std::min(score, new_score(arg, is_true));
            return score;
        }
        if ((m.is_and(a) && !is_true) || (m.is_or(a) && is_true)) {
            double score = 0;
            for (auto arg : *to_app(a))
                score = std::max(score, new_score(arg, is_true));
            return score;
        }
        if (m.is_iff(a, x, y)) {
            auto v0 = m_ev.get_bool_value(x);
            auto v1 = m_ev.get_bool_value(y);
            return (is_true == (v0 == v1)) ? 1 : 0;
        }
        if (m.is_ite(a, x, y, z)) 
            return m_ev.get_bool_value(x) ? new_score(y, is_true) : new_score(z, is_true);        
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
        if (!is_true && m.is_eq(a, x, y) && bv.is_bv(x)) 
            return 0;        
        if (bv.is_ule(a, x, y)) {
            auto const& vx = wval(x);
            auto const& vy = wval(y);
            m_ev.m_tmp.set_bw(vx.bw);
            m_ev.m_tmp2.set_bw(vx.bw);
            if (is_true) {
                if (vx.bits() <= vy.bits())
                    return 1.0;
                // x > y as unsigned.
                // x - y > 0
                // score = (x - y) / 2^bw
                vx.set_sub(m_ev.m_tmp, vx.bits(), vy.bits());
            }
            else {
                if (!(vx.bits() <= vy.bits()))
                    return 1.0;
                // x <= y as unsigned.
                // y - x >= 0
                // score = (y - x + 1) / 2^bw
                vx.set_sub(m_ev.m_tmp, vy.bits(), vx.bits());
                vx.add1(m_ev.m_tmp);
            }

            double delta = 0;
            for (unsigned i = 0; i < vx.bw; ++i)
                if (m_ev.m_tmp.get(i))
                    ++delta;
            return 1.0 - (delta / (double)vx.bw);
        }
        if (bv.is_sle(a, x, y)) {
            auto const& vx = wval(x);
            auto const& vy = wval(y);
            // x += 2^bw-1
            // y += 2^bw-1
            m_ev.m_tmp.set_bw(vx.bw);
            m_ev.m_tmp2.set_bw(vx.bw);
            vy.bits().copy_to(vy.nw, m_ev.m_tmp);
            vx.bits().copy_to(vx.nw, m_ev.m_tmp2);
            m_ev.m_tmp.set(vy.bw - 1, !m_ev.m_tmp.get(vy.bw - 1));
            m_ev.m_tmp2.set(vx.bw - 1, !m_ev.m_tmp2.get(vx.bw - 1));

            if (is_true) {
                if (m_ev.m_tmp2 <= m_ev.m_tmp)
                    return 1.0;
                // otherwise x' > y'                
                vx.set_sub(m_ev.m_tmp3, m_ev.m_tmp2, m_ev.m_tmp);
            }
            else {
                if (!(m_ev.m_tmp2 <= m_ev.m_tmp))
                    return 1.0;
                // x' <= y'
                vx.set_sub(m_ev.m_tmp3, m_ev.m_tmp, m_ev.m_tmp2);
                vx.add1(m_ev.m_tmp3);
            }
            double delta = 0;
            for (unsigned i = 0; i < vx.bw; ++i)
                if (m_ev.m_tmp3.get(i))
                    ++delta;
            return 1.0 - (delta / (double)vx.bw);
        }
        if (is_true && m.is_distinct(a) && bv.is_bv(to_app(a)->get_arg(0))) {
            double np = 0, nd = 0;
            for (unsigned i = 0; i < to_app(a)->get_num_args(); ++i) {
                auto const& vi = wval(to_app(a)->get_arg(i));
                for (unsigned j = i + 1; j < to_app(a)->get_num_args(); ++j) {
                    ++np;
                    auto const& vj = wval(to_app(a)->get_arg(j));
                    if (vi.bits() != vj.bits())
                        nd++;
                }
            }
            return nd / np;
        }

        return 0;
    }

    double bv_lookahead::lookahead_flip(sat::bool_var v) {
        if (ctx.is_unit(v))
            return -100;
        auto a = ctx.atom(v);
        return lookahead_update(a, m_v_updated);
    }

    /**
    * Rehearse an update. The update is revered while a score is computed and returned.
    * Walk all parents, until hitting predicates where their scores are computed.
    */
    double bv_lookahead::lookahead_update(expr* t, bvect const& new_value) {
        SASSERT(bv.is_bv(t) || m.is_bool(t));
        SASSERT(is_uninterp(t));
        double score = m_top_score;

        unsigned restore_point = m_ev.bool_value_restore_point();

        //verbose_stream() << "lookahead update " << mk_bounded_pp(t, m) << " := " << new_value << "\n";

        if (bv.is_bv(t)) {
            if (!wval(t).can_set(new_value))
                return -1000000;
            wval(t).eval = new_value;
            insert_update(t, true);
        }
        else if (m.is_bool(t)) 
            m_ev.set_bool_value_no_log(t, !m_ev.get_bool_value(t));        

        // TRACE("bv_verbose", tout << "lookahead update " << mk_bounded_pp(t, m) << " := " << new_value << "\n";);

        for (unsigned depth = m_min_depth; depth <= m_max_depth; ++depth) {
            for (unsigned i = 0; i < m_update_stack[depth].size(); ++i) {
                auto const& [a, is_bv] = m_update_stack[depth][i];
                TRACE("bv_verbose", tout << "update " << mk_bounded_pp(a, m) << " depth: " << depth  << "\n";);

                if (t != a) {
                    if (is_bv)
                        m_ev.eval(a);
                    insert_update(a, is_bv);
                }

                if (is_root(a)) 
                    score += get_weight(a) * (new_score(a) - old_score(a));                
            }
        }
        m_ev.restore_bool_values(restore_point);

        TRACE("bv_verbose", tout << "lookahead update " << mk_bounded_pp(t, m) << " := " << new_value << " score: " << score << " " << m_best_score << "\n");

        return score;
    }

    void bv_lookahead::populate_update_stack(expr* t) {
        SASSERT(m_bv_restore.empty());
        if (!insert_update_stack(t))
            return;
        m_min_depth = m_max_depth = get_depth(t);
        for (unsigned depth = m_max_depth; depth <= m_max_depth; ++depth) {
            for (unsigned i = 0; i < m_update_stack[depth].size(); ++i) {
                auto [a, is_bv] = m_update_stack[depth][i];
                for (auto p : ctx.parents(a)) {
                    if (insert_update_stack(p))
                        m_max_depth = std::max(m_max_depth, get_depth(p));
                }
                if (is_bv) {
                    wval(a).save_value();
                    SASSERT(!m_bv_restore.contains(a));
                    m_bv_restore.push_back(a);
                }
                else  
                    m_bool_restore.push_back({ a, m_ev.get_bool_value(a) });                
            }
        }
    }

    void bv_lookahead::clear_update_stack() {
        for (unsigned i = m_min_depth; i <= m_max_depth; ++i)
            m_update_stack[i].reset();
        m_in_update_stack.reset();
        for (auto e : m_bv_restore) {
            wval(e).restore_value();
            TRACE("sls_verbose", tout << "restore value " << mk_bounded_pp(e, m) << " " << wval(e) << "\n");
        }
        for (auto const& [e, b]: m_bool_restore)
            m_ev.set_bool_value_no_log(e, b);
        m_bv_restore.reset();
        m_bool_restore.reset();
    }

    void bv_lookahead::try_set(expr* u, bvect const& new_value) {
        if (!wval(u).can_set(new_value))
            return;
        auto score = lookahead_update(u, new_value);
        ++m_stats.m_lookaheads;
        if (score > m_best_score) {
            m_best_score = score;
            m_best_expr = u;
            m_best_value.set_bw(new_value.bw);
            new_value.copy_to(new_value.nw, m_best_value);
        }
    }

    void bv_lookahead::try_flip(expr* u) {
        auto v = ctx.atom2bool_var(u);
        if (v == sat::null_bool_var)
            return;
        auto score = lookahead_flip(v);
        ++m_stats.m_lookaheads;
        if (score > m_best_score) {
            m_best_score = score;
            m_best_expr = u;
        }
    }

    void bv_lookahead::add_updates(expr* u) {
        if (m.is_bool(u)) {
            populate_update_stack(u);
            try_flip(u);
            clear_update_stack();
            return;
        }       
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

        populate_update_stack(u);
        // flip a single bit
        for (unsigned i = 0; i < v.bw && i < 32 ; ++i) {
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
        if (v.bw > 1) {

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
        clear_update_stack();
    }

    /**
    * Apply an update to a variable.
    * The update is committed.
    */

    std::ostream& operator<<(std::ostream& out, bv_lookahead::move_type t) {
        switch (t) {
        case bv_lookahead::move_type::guided_t: return out << "guided";
        case bv_lookahead::move_type::random_t: return out << "random";
        case bv_lookahead::move_type::move_t:   return out << "move";
        case bv_lookahead::move_type::reset_t:  return out << "reset";
        default:
            return out;
        }
    }

    bool bv_lookahead::apply_update(expr* p, expr* t, bvect const& new_value, move_type mt) {
        if (!t)
            return false;
        if (!m.is_bool(t) && !bv.is_bv(t))
            return false;
        if (bv.is_bv(t) && !wval(t).can_set(new_value))
            return false;

        SASSERT(is_uninterp(t));

        if (bv.is_bv(t)) {
            wval(t).eval = new_value;
            VERIFY(wval(t).commit_eval_check_tabu());
        }
        else {
            m_ev.set_bool_value_log(t, !m_ev.get_bool_value(t));
            if (!m_config.use_top_level_assertions) {
                auto v = ctx.atom2bool_var(t);
                if (v != sat::null_bool_var)
                    ctx.flip(v);
            }
        }

        VERIFY(insert_update_stack(t));
        unsigned max_depth = get_depth(t);
        unsigned restore_point = m_ev.bool_value_restore_point();
        for (unsigned depth = max_depth; depth <= max_depth; ++depth) {
            for (unsigned i = 0; i < m_update_stack[depth].size(); ++i) {
                auto [e, is_bv] = m_update_stack[depth][i];
                TRACE("bv_verbose", tout << "update " << mk_bounded_pp(e, m) << "\n";);
                if (t == e)
                    ;
                else if (is_bv) {
                    m_ev.eval(e); // updates wval(e).eval
                    wval(e).commit_eval_ignore_tabu();
                }
                else {
                    SASSERT(m.is_bool(e));    
                    auto v1 = m_ev.bval1(e);

                    CTRACE("bv_verbose", m_ev.get_bool_value(e) != v1, tout << "updated truth value " << mk_bounded_pp(e, m) << " := " << v1 << "\n";);


                    if (m_config.use_top_level_assertions) {
                        if (m_ev.get_bool_value(e) == v1)
                            continue;
                    }
                    else {
                        if (e == p)
                            continue;

                        auto v = ctx.atom2bool_var(e);
                        
                        if (v != sat::null_bool_var) {

                            if (ctx.is_unit(v) || ctx.is_true(e) == v1)
                                ;
                            else if (allow_costly_flips(mt))
                                ctx.flip(v);
                            else if (m_config.allow_rotation) {
                                m_rotated.reset();
                                unsigned budget = 100;
                                bool rot = ctx.try_rotate(v, m_rotated, budget);
                                if (rot)
                                    ++m_stats.m_rotations;
                                CTRACE("bv", rot, tout << "rotated: " << m_rotated << "\n";);
                            }
                        }
                    }
                    m_ev.set_bool_value_log(e, v1);
                }

                for (auto p : ctx.parents(e)) {
                    if (insert_update_stack(p))
                        max_depth = std::max(max_depth, get_depth(p));
                }
        
                if (is_root(e)) {
                    double score = new_score(e);
                    m_top_score += get_weight(e) * (score - old_score(e));
                    set_score(e, score);
                }
            }
            m_update_stack[depth].reset();
        }
        m_in_update_stack.reset();
        if (m_config.use_top_level_assertions)
            m_ev.commit_bool_values();
        else
            m_ev.restore_bool_values(restore_point);
        TRACE("bv", tout << mt << " " << mk_bounded_pp(t, m);
        if (bv.is_bv(t)) tout << " := " << new_value; else tout << " " << m_ev.get_bool_value(t);
            tout << " score " << m_top_score << "\n";);
        return true;
    }

    bool bv_lookahead::allow_costly_flips(move_type mt) {
        if (mt == move_type::reset_t)
            return true;
        if (mt != move_type::random_t)
            return false;
        return m_stats.m_random_flips % 100 == 0;
    }

    void bv_lookahead::insert_update(expr* e, bool is_bv) {
        TRACE("sls_verbose", tout << "insert update " << mk_bounded_pp(e, m) << "\n");
        if (is_bv) {
            SASSERT(bv.is_bv(e));
            auto& v = wval(e);
            v.commit_eval_ignore_tabu();
        }
        else  {
            SASSERT(m.is_bool(e));
            auto v1 = m_ev.bval1(to_app(e));
            m_ev.set_bool_value_no_log(to_app(e), v1);
        }
    }

    bool bv_lookahead::insert_update_stack(expr* e) {
        if (!bv.is_bv(e) && !m.is_bool(e))
            return false;
        unsigned depth = get_depth(e);
        m_update_stack.reserve(depth + 1);
        if (!m_in_update_stack.is_marked(e) && is_app(e)) {
            m_in_update_stack.mark(e);
            m_update_stack[depth].push_back({ to_app(e), bv.is_bv(e) });
        }
        return true;
    }

    sls::bv_valuation& bv_lookahead::wval(expr* e) const {
        return m_ev.wval(e);
    }

    bv_lookahead::bool_info& bv_lookahead::get_bool_info(expr* e) {
        m_bool_info.reserve(e->get_id() + 1, { m_config.paws_init, 0, 1 });
        return m_bool_info[e->get_id()];
    }

    void bv_lookahead::dec_weight(expr* e) {
        auto& w = get_bool_info(e).weight;
        w = w > m_config.paws_init ? w - 1 : m_config.paws_init;
    }

    void bv_lookahead::rescore() {
        m_top_score = 0;
        m_is_root.reset();
        for (auto a : get_root_assertions()) {
            m_is_root.mark(a);
            double score = new_score(a);
            set_score(a, score);
            m_top_score += score;
        }
    }

    void bv_lookahead::recalibrate_weights() {
        for (auto a : get_root_assertions()) {
            if (ctx.rand(2047) < m_config.paws_sp) {
                if (assertion_is_true(a))
                    dec_weight(a);
            }
            else if (!assertion_is_true(a))
                inc_weight(a);
        }

        IF_VERBOSE(20, display_weights(verbose_stream()));       
    }

    std::ostream& bv_lookahead::display_weights(std::ostream& out) {

        for (auto a : get_root_assertions()) {
            out << get_weight(a) << " "
                << (assertion_is_true(a)?"T":"F") << " "
                << mk_bounded_pp(a, m) << " "
                << old_score(a) << " " 
                << new_score(a) << "\n";
        }
        return out;
    }

    void bv_lookahead::ucb_forget() {
        if (m_config.ucb_forget >= 1.0)
            return;
        for (auto a : get_root_assertions()) {
            auto touched_old = get_touched(a);
            auto touched_new = static_cast<unsigned>((touched_old - 1) * m_config.ucb_forget + 1);
            set_touched(a, touched_new);
            m_touched += touched_new - touched_old;
        }
    }

    void bv_lookahead::collect_statistics(statistics& st) const {
        st.update("sls-bv-lookaheads", m_stats.m_lookaheads);
        st.update("sls-bv-moves", m_stats.m_moves);
        st.update("sls-bv-restarts", m_stats.m_restarts);
        st.update("sls-bv-rotations", m_stats.m_rotations);
    }

    bv_lookahead::root_assertions::root_assertions(bv_lookahead& la, bool start) : m_la(la) {
        if (start) {
            idx = 0;
            next();
        }
        else if (m_la.m_config.use_top_level_assertions)
            idx = m_la.ctx.input_assertions().size();
        else
            idx = la.ctx.root_literals().size();
    }

    void bv_lookahead::root_assertions::next() {
        if (m_la.m_config.use_top_level_assertions) 
            return;
        
        while (idx < m_la.ctx.root_literals().size() && !m_la.is_bv_literal(m_la.ctx.root_literals()[idx]))
            ++idx;
    }

    expr* bv_lookahead::root_assertions::operator*() const {
        if (m_la.m_config.use_top_level_assertions)
            return m_la.ctx.input_assertions().get(idx);
        return m_la.ctx.atom(m_la.ctx.root_literals()[idx].var());
    };



}