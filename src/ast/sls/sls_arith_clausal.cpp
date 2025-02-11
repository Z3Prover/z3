/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    sls_arith_clausal

Abstract:

    Theory plugin for arithmetic local search
    based on clausal search as used in HybridSMT (nia_ls)

    In contrast to HybridSMT/nia_ls we reuse ddfw 
    for everything Boolean. It requiers exposing the following:

    - unsat_vars - Boolean variables that are in unsat clauses.
    - num_external_vars_in_unsat - External variables in unsat clauses
    - shift_weights - allow plugin to invoke shift-weights

    
Author:

    Nikolaj Bjorner (nbjorner) 2025-01-16

--*/

#include "ast/sls/sls_arith_clausal.h"
#include "ast/sls/sls_arith_base.h"

namespace sls {
    template<typename num_t>
    arith_clausal<num_t>::arith_clausal(arith_base<num_t>& a) :
        ctx(a.ctx),
        a(a) { 
    }            

    template<typename num_t>
    void arith_clausal<num_t>::search() {

        initialize();

        TRACE("arith", ctx.display_all(tout));

        a.m_config.max_moves = a.m_stats.m_steps + a.m_config.max_moves_base;

        while (ctx.rlimit().inc() && a.m_stats.m_steps < a.m_config.max_moves && !ctx.unsat().empty()) {
            a.m_stats.m_steps++;

            check_restart();
            
            unsigned vars_in_unsat = ctx.unsat_vars().size();
            unsigned ext_in_unsat = ctx.num_external_in_unsat_vars();
            unsigned bool_in_unsat =  vars_in_unsat - ext_in_unsat;
            sat::bool_var bv = sat::null_bool_var;
            var_t v = null_arith_var;
            bool time_up_bool  = m_no_improve_bool  * vars_in_unsat >  5 * bool_in_unsat;
            bool time_up_arith = m_no_improve_arith * vars_in_unsat > 20 * ext_in_unsat;
            if ((m_bool_mode && bool_in_unsat < vars_in_unsat && time_up_bool) || bool_in_unsat == 0)
                enter_arith_mode();
            else if ((!m_bool_mode && bool_in_unsat > 0 && time_up_arith) || vars_in_unsat == bool_in_unsat)
                enter_bool_mode();
            if (m_bool_mode) {
                bv = ctx.bool_flip();        

                m_no_improve_bool = update_outer_best_solution() ? 0 : m_no_improve_bool + 1;
            }
            else {
                v = move_arith_variable();                
                m_no_improve_arith = update_inner_best_solution() ? 0 : m_no_improve_arith + 1;
            }
            m_no_improve = update_best_solution() ? 0 : m_no_improve + 1;

            (void)bv;
            (void)v;
            TRACE("arith", 
                if (bv != sat::null_bool_var) tout << "bool flip " << bv << "\n";
                else if (v != null_arith_var) tout << "arith flip v" << v << "\n";
                else tout << "no flip\n";
                tout << "unsat-vars " << ctx.unsat_vars().size() << "\n";
                tout << "bools: " << (ctx.unsat_vars().size() - ctx.num_external_in_unsat_vars()) << " timeup-bool " << time_up_bool << "\n";
                tout << "no-improve bool: " << m_no_improve_bool << "\n";
                tout << "no-improve arith: " << m_no_improve_arith << "\n";
                tout << "ext: " << ext_in_unsat << " timeup-arith " << time_up_arith << "\n";
                );
        }

        if (a.m_stats.m_steps >= a.m_config.max_moves)
            a.m_config.max_moves_base += 100;
    }

    template<typename num_t>
    var_t arith_clausal<num_t>::move_arith_variable() {

        var_t v = null_arith_var;

        {
            m_best_score = 1;
            flet<bool> _use_tabu(a.m_use_tabu, true);
            if (v == null_arith_var) {
                add_lookahead_on_unsat_vars();
                v = critical_move_on_updates(unsat_var_move);
            }
            if (v == null_arith_var) {
                add_lookahead_on_false_literals();
                v = critical_move_on_updates(false_literal_move);
            }
        }

        // tabu flips were not possible

        if (v == null_arith_var)
            ctx.shift_weights();

        if (v == null_arith_var) {
            m_best_score = -1;
            flet<bool> _use_tabu(a.m_use_tabu, false);
            add_lookahead_on_unsat_vars();
            v = random_move_on_updates();
        }

        return v;
    }

    template<typename num_t>
    void arith_clausal<num_t>::add_lookahead_on_unsat_vars() {
        a.m_updates.reset();
        TRACE("arith_verbose", tout << "unsat-vars ";
        for (auto v : ctx.unsat_vars())
            if (a.get_ineq(v)) tout << mk_bounded_pp(ctx.atom(v), a.m) << " ";
        tout << "\n";);

        for (auto v : ctx.unsat_vars()) 
            add_lookahead(v);
        
    }

    template<typename num_t>
    void arith_clausal<num_t>::add_lookahead(sat::bool_var bv) {
        auto* ineq = a.get_ineq(bv);
        if (!ineq)
            return;
        num_t na, nb;
        flet<bool> _allow_recursive_delta(a.m_allow_recursive_delta, true);
        for (auto const& [x, nl] : ineq->m_nonlinear) {
            if (a.is_fixed(x))
                continue;
            if (a.is_linear(x, nl, nb))
                a.find_linear_moves(*ineq, x, nb);
            else if (a.is_quadratic(x, nl, na, nb))
                a.find_quadratic_moves(*ineq, x, na, nb, ineq->m_args_value);
            else
                ;
        }
    }

    /**
    * \brief walk over literals that are false in some clause.
    * Try to determine if flipping them to true improves the overall score.
    */
    template<typename num_t>
    void arith_clausal<num_t>::add_lookahead_on_false_literals() {
        a.m_updates.reset();

        unsigned sz = a.m_bool_var_atoms.size();
        bool is_big = sz > 45u;
        sat::bool_var bv;

        auto occurs_negative = [&](sat::bool_var bv) {
            if (ctx.unsat_vars().contains(bv))
                return false;
            auto* ineq = a.get_ineq(bv);
            if (!ineq)
                return false;
            sat::literal lit(bv, !ineq->is_true());
            auto const& ul = ctx.get_use_list(~lit);
            return ul.begin() != ul.end();
        };

        unsigned idx = 0;
        if (is_big) {
            for (unsigned i = 45, j = 90; j-- > 0 && i-- > 0 && sz > 0;) {
                idx = ctx.rand(sz);
                bv = a.m_bool_var_atoms[idx];
                --sz;
                a.m_bool_var_atoms.swap_elems(idx, sz);
                if (occurs_negative(bv))
                    add_lookahead(bv);
                else
                    ++i;
            }
        }
        else {
            for (unsigned i = 0; i < sz; ++i) {
                bv = a.m_bool_var_atoms[i];
                if (occurs_negative(bv))
                    add_lookahead(bv);
            }
        }
    }

    template<typename num_t>
    var_t arith_clausal<num_t>::critical_move_on_updates(move_t mt) {
        if (a.m_updates.empty())
            return null_arith_var;
        std::stable_sort(a.m_updates.begin(), a.m_updates.end(), [](auto const& a, auto const& b) { return a.m_var < b.m_var || (a.m_var == b.m_var && a.m_delta < b.m_delta); });
        m_last_var = null_arith_var;
        m_last_delta = 0;
        m_best_var = null_arith_var;
        m_best_delta = 0;
        m_best_abs_value = num_t(-1);
        m_best_last_step = UINT_MAX;
        m_num_lookaheads = 0;
        for (auto const& u : a.m_updates)
            lookahead(u.m_var, u.m_delta);

        // verbose_stream() << a.m_updates.size() << " " << m_num_lookaheads << " lookaheads\n";
        ctx.rlimit().inc(1 + m_num_lookaheads);
        critical_move(m_best_var, m_best_delta, mt);        
        return m_best_var;
    }

    template<typename num_t>
    var_t arith_clausal<num_t>::random_move_on_updates() {
        if (a.m_updates.empty())
            return null_arith_var;
        unsigned idx = ctx.rand(a.m_updates.size());
        auto& [v, delta, score] = a.m_updates[idx];
        if (!a.can_update_num(v, delta))
            return null_arith_var;
        critical_move(v, delta, random_move);
        return v;
    }

    template<typename num_t>
    void arith_clausal<num_t>::lookahead(var_t v, num_t const& delta) {
        if (v == m_last_var && delta == m_last_delta)
            return;
        if (delta == 0)
            return;

        m_last_var = v;
        m_last_delta = delta;
        if (!a.can_update_num(v, delta))
            return;
        auto score = get_score(v, delta);
        auto& vi = a.m_vars[v];        
        num_t abs_value = abs(vi.value() + delta);
        unsigned last_step = vi.last_step(delta);
        ++m_num_lookaheads;
        if (score < m_best_score)
            return;
        if (score > m_best_score ||
            (m_best_abs_value == -1) ||
            (abs_value < m_best_abs_value) ||
            (abs_value == m_best_abs_value && last_step < m_best_last_step)) {
            m_best_score = score;
            m_best_var = v;
            m_best_delta = delta;
            m_best_last_step = last_step;
            m_best_abs_value = abs_value;
        }
    }

    template<typename num_t>
    void arith_clausal<num_t>::critical_move(var_t v, num_t const& delta, move_t mt) {
        if (v == null_arith_var)
            return;
        a.m_last_delta = delta;
        a.m_last_var = v;
        TRACE("arith", tout << mt << " v" << v << " " << mk_bounded_pp(a.m_vars[v].m_expr, a.m) 
                            << " += " << delta << " score:" << m_best_score << "\n");
        a.m_vars[v].set_step(a.m_stats.m_steps, a.m_stats.m_steps + 3 + ctx.rand(10), delta);
        VERIFY(a.update_num(v, delta));
        for (auto bv : a.m_vars[v].m_bool_vars_of) 
            if (a.get_ineq(bv) && a.get_ineq(bv)->is_true() != ctx.is_true(bv)) 
                ctx.flip(bv);   

        DEBUG_CODE(
            for (sat::bool_var bv = 0; bv < ctx.num_bool_vars(); ++bv) {
                if (a.get_ineq(bv) && a.get_ineq(bv)->is_true() != ctx.is_true(bv)) {
                    TRACE("arith", tout << "bv:" << bv << " " << *a.get_ineq(bv) << " " << (ctx.is_true(bv)?"T":"F") << "\n";
                    tout << "v" << v << " bool vars: " << a.m_vars[v].m_bool_vars_of << "\n";
                    tout << mk_bounded_pp(a.m_vars[v].m_expr, a.m) << "\n";
                    tout << mk_bounded_pp(ctx.atom(bv), a.m) << "\n";
                    ctx.display(tout););
                }
                // VERIFY(!a.get_ineq(bv) || a.get_ineq(bv)->is_true() == ctx.is_true(bv));
            });
    }

    template<typename num_t>
    double arith_clausal<num_t>::get_score(var_t v, num_t const& delta) {
        auto& vi = a.m_vars[v];
        TRACE("arith", tout << "get-score v" << v << " += " << delta << "\n";);
        if (!a.update_num(v, delta))
            return -1;
        double score = 0;
        for (auto ci : vi.m_clauses_of) {
            auto const& c = ctx.get_clause(ci);
            unsigned num_true = 0;
            for (auto lit : c) {
                auto bv = lit.var();
                auto ineq = a.get_ineq(bv);
                if (ineq) {
                    if (ineq->is_true() != lit.sign())
                        ++num_true;
                }
                else if (ctx.is_true(lit))
                    ++num_true;
            }

            CTRACE("arith_verbose", c.m_num_trues != num_true && (c.m_num_trues == 0 || num_true == 0),
                tout << "clause: " << c
                << " v" << v << " += " << delta
                << " new-true lits: " << num_true
                << " old-true lits: " << c.m_num_trues
                << " w: " << c.m_weight << "\n";
            for (auto lit : c)
                if (a.get_ineq(lit.var()))
                    tout << lit << " " << *a.get_ineq(lit.var()) << "\n";);
            if (c.m_num_trues > 0 && num_true == 0)
                score -= c.m_weight;
            else if (c.m_num_trues == 0 && num_true > 0)
                score += c.m_weight;
        }

        // verbose_stream() << num_clauses << " " << num_dup << "\n";
        // revert the update
        TRACE("arith", tout << "revert update v" << v << " -= " << delta << "\n";);
        a.update_unchecked(v, vi.value() - delta);        
        return score;
    }

    template<typename num_t>
    void arith_clausal<num_t>::check_restart() {

        if (m_no_improve <= 500000)
            return;
#if 0
        if (a.m_stats.m_steps < a.m_config.restart_next)
            return;

        
        ++a.m_stats.m_restarts;
        a.m_config.restart_next = std::max(a.m_config.restart_next, a.m_stats.m_steps);
        
        a.m_config.restart_next += (2 * a.m_stats.m_restarts * a.m_config.restart_base)/3;
#endif    
        
        IF_VERBOSE(2, verbose_stream() << "restart sls-arith " << a.m_config.restart_next << "\n");
        TRACE("arith", tout << "restart\n";);
        // reset values of (arithmetical) variables at bounds.
        for (auto& vi : a.m_vars) {
            if (vi.m_lo && !vi.m_lo->is_strict && vi.m_lo->value > 0)
                vi.set_value(vi.m_lo->value);
            else if (vi.m_hi && !vi.m_hi->is_strict && vi.m_hi->value < 0)
                vi.set_value(vi.m_hi->value);
            else
                vi.set_value(num_t(0));
        }
        initialize();
    }

    template<typename num_t>
    void arith_clausal<num_t>::initialize() {
        for (sat::bool_var v = 0; v < ctx.num_bool_vars(); ++v)
            a.init_bool_var_assignment(v);   

        DEBUG_CODE(
            for (sat::bool_var bv = 0; bv < ctx.num_bool_vars(); ++bv) {
                if (a.get_ineq(bv) && a.get_ineq(bv)->is_true() != ctx.is_true(bv)) {
                    TRACE("arith", tout << "bv:" << bv << " " << *a.get_ineq(bv) << ctx.is_true(bv) << "\n";
                    tout << mk_bounded_pp(ctx.atom(bv), a.m) << "\n";
                    ctx.display(tout););
                }
                VERIFY(!a.get_ineq(bv) || a.get_ineq(bv)->is_true() == ctx.is_true(bv));
            });
        
        m_best_found_cost_bool = ctx.unsat().size();
        m_best_found_cost_arith = ctx.unsat().size();
        m_best_found_cost_restart = ctx.unsat().size();
        m_no_improve = 0;
        m_no_improve_bool = 0;
        m_no_improve_arith = 0;
        for (; m_num_clauses < ctx.clauses().size(); ++m_num_clauses) {
            auto const& c = ctx.get_clause(m_num_clauses);
            for (auto lit : c) {
                auto bv = lit.var();
                if (a.get_ineq(bv))
                    a.initialize_clauses_of(bv, m_num_clauses);
            }
        }
    }    
   

    template<typename num_t>
    bool arith_clausal<num_t>::update_outer_best_solution() {
        if (ctx.unsat().size() >= m_best_found_cost_bool)
            return false;
        m_best_found_cost_bool = ctx.unsat().size();
        return true;
    }

    template<typename num_t>
    void arith_clausal<num_t>::enter_bool_mode() {
        CTRACE("arith", !m_bool_mode, tout << "enter bool mode\n";);
        m_best_found_cost_bool = ctx.unsat().size();
        if (!m_bool_mode) 
            m_no_improve_bool = 0; 
        m_bool_mode = true;
    }

    template<typename num_t>
    bool arith_clausal<num_t>::update_inner_best_solution() {
        if (ctx.unsat().size() >= m_best_found_cost_arith)
            return false;
        m_best_found_cost_arith = ctx.unsat().size();
        return true;
    }

    template<typename num_t>
    void arith_clausal<num_t>::enter_arith_mode() {
        CTRACE("arith", m_bool_mode, tout << "enter arith mode\n";);
        m_best_found_cost_arith = ctx.unsat().size();
        if (m_bool_mode)
            m_no_improve_arith = 0;
        m_bool_mode = false;
    }

    template<typename num_t>
    bool arith_clausal<num_t>::update_best_solution() {
        bool improved = false;
        if (ctx.unsat().size() < m_best_found_cost_restart) {
            improved = true;
            m_best_found_cost_restart = ctx.unsat().size();
        }
        if (ctx.unsat().size() < m_best_found_cost) {
            improved = true;
            m_best_found_cost = ctx.unsat().size();
        }
        return improved;
    }
}

template class sls::arith_clausal<checked_int64<true>>;
template class sls::arith_clausal<rational>;

