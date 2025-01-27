/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    sls_arith_lookahead

    
Author:

    Nikolaj Bjorner (nbjorner) 2025-01-16

--*/

#include <cmath>
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/sls/sls_arith_lookahead.h"
#include "ast/sls/sls_arith_base.h"

namespace sls {
    template<typename num_t>
    arith_lookahead<num_t>::arith_lookahead(arith_base<num_t>& a) :
        ctx(a.ctx),
        m(a.m),
        a(a),
        autil(m) { 
    }

    template<typename num_t>
    typename arith_lookahead<num_t>::bool_info& arith_lookahead<num_t>::get_bool_info(expr* e) {   
        unsigned id = e->get_id();
        if (id >= m_bool_info.size())
            m_bool_info.reserve(id + 1);
        if (!m_bool_info[id])
            m_bool_info.set(id, alloc(bool_info, a.m_config.paws_init));
        return *m_bool_info[id];
    }

    template<typename num_t>
    bool arith_lookahead<num_t>::get_bool_value_rec(expr* e) {        
        if (!is_app(e))
            return ctx.get_value(e) == l_true;

        if (is_uninterp(e))
            return ctx.get_value(e) == l_true;

        app* ap = to_app(e);
        bool is_arith_eq = m.is_eq(e) && autil.is_int_real(ap->get_arg(0));
        
        if (ap->get_family_id() == basic_family_id && !is_arith_eq) 
            return get_basic_bool_value(ap);                    

        auto v = ctx.atom2bool_var(e);
        if (v == sat::null_bool_var)
            return false;
        auto const* ineq = a.get_ineq(v);
        if (!ineq)
            return false;
        return ineq->is_true();
    }    

    template<typename num_t>
    bool arith_lookahead<num_t>::get_bool_value(expr* e) {
        auto& info = get_bool_info(e);
        if (info.value != l_undef)
            return info.value == l_true;

        auto r = get_bool_value_rec(e);
        info.value = to_lbool(r);
        return r;
    }


    template<typename num_t>
    bool arith_lookahead<num_t>::get_basic_bool_value(app* e) {
        switch (e->get_decl_kind()) {
        case OP_TRUE:
            return true;
        case OP_FALSE:
            return false;
        case OP_NOT:
            return !get_bool_value(e->get_arg(0));
        case OP_AND:
            return all_of(*e, [&](expr* arg) { return get_bool_value(arg); });
        case OP_OR:
            return any_of(*e, [&](expr* arg) { return get_bool_value(arg); });
        case OP_XOR:
            return xor_of(*e, [&](expr* arg) { return get_bool_value(arg); });
        case OP_IMPLIES:
            return !get_bool_value(e->get_arg(0)) || get_bool_value(e->get_arg(1));
        case OP_EQ:
            if (m.is_bool(e->get_arg(0)))
                return get_bool_value(e->get_arg(0)) == get_bool_value(e->get_arg(1));
            return ctx.get_value(e->get_arg(0)) == ctx.get_value(e->get_arg(1));            
        case OP_DISTINCT:
            return false;
        case OP_ITE:
            return get_bool_value(e->get_arg(0)) ? get_bool_value(e->get_arg(1)) : get_bool_value(e->get_arg(2));
        default:
            verbose_stream() << mk_pp(e, m) << "\n";
            NOT_IMPLEMENTED_YET();
        }
        return false;
    }


    template<typename num_t>
    double arith_lookahead<num_t>::new_score(expr* e) {
        return new_score(e, true);
    }

    template<typename num_t>
    double arith_lookahead<num_t>::new_score(expr* e, bool is_true) {
        bool is_true_new = get_bool_value(e);

        if (is_true == is_true_new)
            return 1;
        if (is_uninterp(e))
            return 0;
        if (m.is_true(e))
            return is_true ? 1 : 0;
        if (m.is_false(e))
            return is_true ? 0 : 1;
        expr* x, * y, * z;
        if (m.is_not(e, x))
            return new_score(x, !is_true);
        if ((m.is_and(e) && is_true) || (m.is_or(e) && !is_true)) {
            double score = 1;
            for (auto arg : *to_app(e))
                score = std::min(score, new_score(arg, is_true));
            return score;
        }
        if ((m.is_and(e) && !is_true) || (m.is_or(e) && is_true)) {
            double score = 0;
            for (auto arg : *to_app(e))
                score = std::max(score, new_score(arg, is_true));
            return score;
        }
        if (m.is_iff(e, x, y)) {
            auto v0 = get_bool_value(x);
            auto v1 = get_bool_value(y);
            return (is_true == (v0 == v1)) ? 1 : 0;
        }
        if (m.is_ite(e, x, y, z))
            return get_bool_value(x) ? new_score(y, is_true) : new_score(z, is_true);


        auto v = ctx.atom2bool_var(e);
        if (v == sat::null_bool_var)
            return 0;
        auto const* ineq = a.get_ineq(v);
        if (!ineq)
            return 0;

        auto const& args = ineq->m_args_value;
        auto const& coeff = ineq->m_coeff;
        auto value = args + coeff;

        switch (ineq->m_op) {
        case arith_base<num_t>::ineq_kind::LE: 
            if (is_true) {
                if (value <= 0)
                    return 1.0;
            }
            else {
                if (value > 0)
                    return 1.0;
                value = -value + 1;               
            }
            break;
        case arith_base<num_t>::ineq_kind::LT:
            if (is_true) {
                if (value < 0)
                    return 1.0;
            }
            else {
                if (value >= 0)
                    return 1.0;
                value = -value;
            }
            break;
        case arith_base<num_t>::ineq_kind::EQ:
            if (is_true) {
                if (value == 0)
                    return 1.0;
                if (value < 0)
                    value = -value;
            }
            else {
                if (value != 0)
                    return 1.0;
                return 0.0;
            }
            break;
        }        


        SASSERT(value > 0);
        unsigned max_value = 1000;
        if (value > max_value)
            return 0.0;
        auto d = value.get_double();
        double score = 1.0 - ((d * d) / ((double)max_value * (double)max_value));
        //score = 1.0 - d / max_value;
        return score;
    }

    template<typename num_t>
    void arith_lookahead<num_t>::rescore() {
        m_top_score = 0;
        m_is_root.reset();
        for (auto a : ctx.input_assertions()) {
            double score = new_score(a);
            set_score(a, score);
            m_top_score += score;
            m_is_root.mark(a);
        }
    }

    template<typename num_t>
    void arith_lookahead<num_t>::recalibrate_weights() {
        for (auto f : ctx.input_assertions()) {
            if (ctx.rand(2047) < a.m_config.paws_sp) {
                if (get_bool_value(f))
                    dec_weight(f);
            }
            else if (!get_bool_value(f))
                inc_weight(f);
        }        
    }

    template<typename num_t>
    void arith_lookahead<num_t>::dec_weight(expr* e) { 
        auto& i = get_bool_info(e); 
        i.weight = i.weight > a.m_config.paws_init ? i.weight - 1 : a.m_config.paws_init; 
    }

    template<typename num_t>
    void arith_lookahead<num_t>::insert_update_stack_rec(expr* t) {
        m_min_depth = m_max_depth = get_depth(t);
        insert_update_stack(t);
        for (unsigned depth = m_max_depth; depth <= m_max_depth; ++depth) {
            for (unsigned i = 0; i < m_update_stack[depth].size(); ++i) {
                auto a = m_update_stack[depth][i];
                for (auto p : ctx.parents(a)) {
                    insert_update_stack(p);
                    m_max_depth = std::max(m_max_depth, get_depth(p));
                }
            }
        }
        m_update_stack.reserve(m_max_depth + 1);
    }
    template<typename num_t>
    double arith_lookahead<num_t>::lookahead(expr* t, bool update_score) {
        ctx.rlimit().inc();
        SASSERT(autil.is_int_real(t) || m.is_bool(t));
        double score = m_top_score;
        for (unsigned depth = m_min_depth; depth <= m_max_depth; ++depth) {
            for (unsigned i = 0; i < m_update_stack[depth].size(); ++i) {
                auto* a = m_update_stack[depth][i];
                TRACE("arith_verbose", tout << "update " << mk_bounded_pp(a, m) << " depth: " << depth << "\n";);
                if (t != a)
                    set_bool_value(a, get_bool_value_rec(a));
                if (m_is_root.is_marked(a)) {
                    auto nscore = new_score(a);
                    score += get_weight(a) * (nscore - old_score(a));
                    if (update_score)
                        set_score(a, nscore);
                }
            }
        }
        return score;
    }

    template<typename num_t>
    void arith_lookahead<num_t>::insert_update_stack(expr* t) {
        unsigned depth = get_depth(t);
        m_update_stack.reserve(depth + 1);
        if (!m_in_update_stack.is_marked(t) && is_app(t)) {
            m_in_update_stack.mark(t);
            m_update_stack[depth].push_back(to_app(t));
        }
    }

    template<typename num_t>
    void arith_lookahead<num_t>::clear_update_stack() {
        m_in_update_stack.reset();
        m_update_stack.reserve(m_max_depth + 1);
        for (unsigned i = m_min_depth; i <= m_max_depth; ++i)
            m_update_stack[i].reset();        
    }

    template<typename num_t>
    void arith_lookahead<num_t>::lookahead_num(var_t v, num_t const& delta) {       
        num_t old_value = a.value(v);
        expr* e = a.m_vars[v].m_expr;
        if (m_last_expr != e) {
            if (m_last_expr)
                lookahead(m_last_expr, false);
            clear_update_stack();
            insert_update_stack_rec(e);
            m_last_expr = e;
        }
        else if (a.m_last_delta == delta)
            return;
        a.m_last_delta = delta;

        num_t new_value = old_value + delta;

        if (!a.update_num(v, delta))
            return;
        auto score = lookahead(e, false);
        TRACE("arith_verbose", tout << "lookahead " << v << " " << mk_bounded_pp(e, m) << " := " << delta + old_value << " " << score << " (" << m_best_score << ")\n";);
        if (score > m_best_score) {
            m_tabu_set = 0;
            m_best_score = score;
            m_best_value = new_value;
            m_best_expr = e;
        }
        else if (a.m_config.allow_plateau && score == m_best_score && !in_tabu_set(e, new_value)) {
            m_best_score = score;
            m_best_expr = e;
            m_best_value = new_value;
            insert_tabu_set(e, new_value);
            //verbose_stream() << "plateau " << mk_bounded_pp(e, m) << " := " << m_best_value << "\n";
        }

        // revert back to old value
        a.update_unchecked(v, old_value);
    }

    template<typename num_t>
    bool arith_lookahead<num_t>::in_tabu_set(expr* e, num_t const& n) {
        uint64_t h = hash_u_u(e->get_id(), n.hash());
        return (m_tabu_set & (1ull << (h & 63ull))) != 0;
    }

    template<typename num_t>
    void arith_lookahead<num_t>::insert_tabu_set(expr* e, num_t const& n) {
        uint64_t h = hash_u_u(e->get_id(), n.hash());
        m_tabu_set |= (1ull << (h & 63ull));
    }

    template<typename num_t>
    void arith_lookahead<num_t>::lookahead_bool(expr* e) {
        bool b = get_bool_value(e);
        set_bool_value(e, !b);
        insert_update_stack_rec(e);
        auto score = lookahead(e, false);
        if (score > m_best_score) {
            m_tabu_set = 0;
            m_best_score = score;            
            m_best_expr = e;
        }
        else if (a.m_config.allow_plateau && score == m_best_score &&  !in_tabu_set(e, num_t(1))) {
            m_best_score = score;
            m_best_expr = e;
            insert_tabu_set(e, num_t(1));
        }
        set_bool_value(e, b);   
        lookahead(e, false);
        clear_update_stack();
        m_last_expr = nullptr;
    }

    template<typename num_t>
    void arith_lookahead<num_t>::add_lookahead(bool_info& i, sat::bool_var bv) {
        if (!i.fixable_atoms.contains(bv))
            return;
        if (m_fixed_atoms.contains(bv))
            return;
        auto* ineq = a.get_ineq(bv);
        if (!ineq)
            return;
        num_t na, nb;
        for (auto const& [x, nl] : ineq->m_nonlinear) {
            if (!i.fixable_vars.contains(x))
                continue;
            if (a.is_fixed(x))
                continue;
            if (a.is_linear(x, nl, nb))
                a.find_linear_moves(*ineq, x, nb);
            else if (a.is_quadratic(x, nl, na, nb))
                a.find_quadratic_moves(*ineq, x, na, nb, ineq->m_args_value);
            else
                ;
        }
        m_fixed_atoms.insert(bv);
    }


    // for every variable e, for every atom containing e
    // add lookahead for e.
    // m_fixable_atoms contains atoms that can be fixed.
    // m_fixable_vars  contains variables that can be updated.
    template<typename num_t>
    void arith_lookahead<num_t>::add_lookahead(bool_info& i, expr* e) {

        auto add_finite_domain = [&](var_t v) {
            auto old_value = a.value(v);
            for (auto const& n : a.m_vars[v].m_finite_domain) 
                a.add_update(v, n - old_value);            
        };


        if (m.is_bool(e)) {
            auto bv = ctx.atom2bool_var(e);
            if (i.fixable_atoms.contains(bv))
                lookahead_bool(e);                      
        }
        else if (autil.is_int_real(e)) {
            auto v = a.mk_term(e);
            auto& vi = a.m_vars[v];
            if (false && !vi.m_finite_domain.empty()) {
                add_finite_domain(v);
                return;
            }
            for (auto bv : vi.m_bool_vars_of)
                add_lookahead(i, bv);            
        }
    }

    //
    // e is a formula that is false, 
    // assemble candidates that can flip the formula to true.
    // candidate expressions may be either numeric or boolean variables.
    //
    template<typename num_t>
    ptr_vector<expr> const& arith_lookahead<num_t>::get_fixable_exprs(expr* e) {
        auto& i = get_bool_info(e);
        if (!i.fixable_exprs.empty())
            return i.fixable_exprs;
        expr_mark visited;
        ptr_buffer<expr> todo;

        auto& tmp_set = a.m_tmp_set;
        tmp_set.reset();

        todo.push_back(e); 
        while (!todo.empty()) {
            auto e = todo.back();
            todo.pop_back();
            if (visited.is_marked(e))
                continue;
            visited.mark(e);           
            if (m.is_xor(e) || m.is_and(e) || m.is_or(e) || m.is_implies(e) || m.is_iff(e) || m.is_ite(e) || m.is_not(e)) {
                for (auto arg : *to_app(e))
                    todo.push_back(arg);
            }
            else {
                auto bv = ctx.atom2bool_var(e);
                if (bv == sat::null_bool_var)
                    continue;
                if (is_uninterp(e)) {
                    if (!i.fixable_atoms.contains(bv)) {
                        i.fixable_atoms.push_back(bv);
                        i.fixable_exprs.push_back(e);
                    }
                    continue;
                }
                auto* ineq = a.get_ineq(bv);
                if (!ineq)
                    continue;
                i.fixable_atoms.push_back(bv);
                buffer<var_t> vars;
                
                for (auto& [v, occ] : ineq->m_nonlinear) 
                    vars.push_back(v);
                
                for (unsigned j = 0; j < vars.size(); ++j) {
                    auto v = vars[j];
                    if (tmp_set.contains(v))
                        continue;
                    
                    if (a.is_add(v)) {
                        for (auto [c, w] : a.get_add(v).m_args)
                            vars.push_back(w);
                    }
                    else if (a.is_mul(v)) {
                        for (auto [w, p] : a.get_mul(v).m_monomial)
                            vars.push_back(w);
                    }
                    else {
                        i.fixable_exprs.push_back(a.m_vars[v].m_expr);
                        tmp_set.insert(v);
                    }
                }
            }
        }
        for (auto v : tmp_set)
            i.fixable_vars.push_back(v);
        return i.fixable_exprs;
    }

    template<typename num_t>
    bool arith_lookahead<num_t>::apply_move(expr* f, ptr_vector<expr> const& vars, arith_move_type t) {
        if (vars.empty())
            return false;
        auto& info = get_bool_info(f);
        m_best_expr = nullptr;
        m_best_score = m_top_score;
        unsigned sz = vars.size();
        unsigned start = ctx.rand();
        a.m_updates.reset();
        m_fixed_atoms.reset();

        switch (t) {
        case arith_move_type::random_update: {
            for (unsigned i = 0; i < sz; ++i)
                add_lookahead(info, vars[(start + i) % sz]);
            if (a.m_updates.empty())
                return false;
            unsigned idx = ctx.rand(a.m_updates.size());
            auto& [v, delta, score] = a.m_updates[idx];
            m_best_expr = a.m_vars[v].m_expr;
            if (false && !a.m_vars[v].m_finite_domain.empty())
                m_best_value = a.m_vars[v].m_finite_domain[ctx.rand() % a.m_vars[v].m_finite_domain.size()];
            else
                m_best_value = a.value(v) + delta;
            m_tabu_set = 0;
            break;
        }
        case arith_move_type::hillclimb_plateau:
        case arith_move_type::hillclimb: {
            for (unsigned i = 0; i < sz; ++i)
                add_lookahead(info, vars[(start + i) % sz]);
            if (a.m_updates.empty())
                return false;
            std::stable_sort(a.m_updates.begin(), a.m_updates.end(), [](auto const& a, auto const& b) { return a.m_var < b.m_var || (a.m_var == b.m_var && a.m_delta < b.m_delta); });
            m_last_expr = nullptr;
            sz = a.m_updates.size();
            flet<bool> _allow_plateau(a.m_config.allow_plateau, a.m_config.allow_plateau || t == arith_move_type::hillclimb_plateau);
            for (unsigned i = 0; i < sz; ++i) {
                auto const& [v, delta, score] = a.m_updates[(start + i) % a.m_updates.size()];
                lookahead_num(v, delta);
            }
            if (m_last_expr) {
                lookahead(m_last_expr, false);
                clear_update_stack();
            }
            break;
        }
        case arith_move_type::random_inc_dec: {
            auto e = vars[ctx.rand() % sz];
            m_best_expr = e;
            if (autil.is_int_real(e)) {
                var_t v = a.mk_term(e);
                auto& vi = a.m_vars[v];
                if (!vi.m_finite_domain.empty()) 
                    m_best_value = vi.m_finite_domain[ctx.rand() % vi.m_finite_domain.size()];                
                else if (ctx.rand(2) == 0)
                    m_best_value = a.value(v) + 1;
                else
                    m_best_value = a.value(v) - 1;
            }
            m_tabu_set = 0;
            break;
        }
        }

        if (m_best_expr) {            
            if (m.is_bool(m_best_expr))
                set_bool_value(m_best_expr, !get_bool_value(m_best_expr));
            else {
                var_t v = a.mk_term(m_best_expr);
                if (!a.update_num(v, m_best_value - a.value(v))) {
                    TRACE("arith",
                        tout << "could not move v" << v << " " << t << " " << mk_bounded_pp(m_best_expr, m) << " := " << a.value(v) << " " << m_top_score << "\n";
                        );
                    return false;
                }
            }
            insert_update_stack_rec(m_best_expr);
            m_top_score = lookahead(m_best_expr, true);
            clear_update_stack();
        }
                
        CTRACE("arith", !m_best_expr, tout << "no move " << t << "\n";);
        CTRACE("arith", m_best_expr && autil.is_int_real(m_best_expr), {
            var_t v = a.mk_term(m_best_expr);
            tout << t << " v" << v << " " << mk_bounded_pp(m_best_expr, m) << " := " << a.value(v) << " " << m_top_score << "\n";
            });
        return !!m_best_expr;
    }


    std::ostream& operator<<(std::ostream& out, arith_move_type mt) {
        switch (mt) {
        case arith_move_type::random_update: out << "random-update"; break;
        case arith_move_type::hillclimb: out << "hillclimb"; break;
        case arith_move_type::random_inc_dec: out << "random-inc-dec"; break;
        case arith_move_type::hillclimb_plateau: out << "hillclimb-plateau"; break;
        }
        return out;
    }



    template<typename num_t>
    void arith_lookahead<num_t>::check_restart() {
        if (a.m_stats.m_steps % a.m_config.restart_base == 0) {
            ucb_forget();
            rescore();
        }

        if (a.m_stats.m_steps < a.m_config.restart_next)
            return;

        ++a.m_stats.m_restarts;
        a.m_config.restart_next = std::max(a.m_config.restart_next, a.m_stats.m_steps);

        if (0x1 == (a.m_stats.m_restarts & 0x1))
            a.m_config.restart_next += a.m_config.restart_base;
        else
            a.m_config.restart_next += (2 * (a.m_stats.m_restarts >> 1)) * a.m_config.restart_base;

        // reset_uninterp_in_false_literals
        rescore();
    }

    template<typename num_t>
    void arith_lookahead<num_t>::ucb_forget() {
        if (a.m_config.ucb_forget >= 1.0)
            return;
        for (auto f : ctx.input_assertions()) {
            auto touched_old = get_touched(f);
            auto touched_new = static_cast<unsigned>((touched_old - 1) * a.m_config.ucb_forget + 1);
            set_touched(f, touched_new);
            m_touched += touched_new - touched_old;
        }
    }

    template<typename num_t>
    void arith_lookahead<num_t>::initialize_bool_assignment() {
        for (auto t : ctx.subterms())
            if (m.is_bool(t))
                set_bool_value(t, get_bool_value_rec(t));
#if 0
        for (auto t : ctx.subterms()) {
            if (m.is_bool(t))
                verbose_stream() << mk_bounded_pp(t, m) << " := " << get_bool_value(t) << "\n";
            else
                verbose_stream() << mk_bounded_pp(t, m) << " := " << ctx.get_value(t) << "\n";
        }
#endif
    }

    template<typename num_t>
    void arith_lookahead<num_t>::finalize_bool_assignment() {
        for (unsigned v = ctx.num_bool_vars(); v-- > 0; ) {
            auto a = ctx.atom(v);
            if (!a)
                continue;
            if (get_bool_value(a) != ctx.is_true(v))
                ctx.flip(v);
        }
#if 0
        for (auto idx : ctx.unsat()) {
            auto const& cl = ctx.get_clause(idx);
            verbose_stream() << "clause " << cl << "\n";
            for (auto lit : cl) {
                auto a = ctx.atom(lit.var());
                if (a)
                    verbose_stream() << lit << " " << mk_bounded_pp(a, m) << " " << get_bool_value(a) << " " << ctx.is_true(lit) << "\n";
                else
                    verbose_stream() << lit << " " << ctx.is_true(lit) << "\n";
            }
        }
#endif

    }


    template<typename num_t>
    void  arith_lookahead<num_t>::search() {
        initialize_bool_assignment();
        rescore();
        a.m_config.max_moves = a.m_stats.m_steps + a.m_config.max_moves_base;
        TRACE("arith", tout << "search " << a.m_stats.m_steps << " " << a.m_config.max_moves << "\n";);
        IF_VERBOSE(3, verbose_stream() << "lookahead-search steps:" << a.m_stats.m_steps << " max-moves:" << a.m_config.max_moves << "\n");
        TRACE("arith", a.display(tout));

        while (ctx.rlimit().inc() && a.m_stats.m_steps < a.m_config.max_moves) {
            a.m_stats.m_steps++;
            check_restart();

            auto t = get_candidate_unsat();

            if (!t) 
                break;
            
            auto& vars = get_fixable_exprs(t);

            if (vars.empty()) 
                break;            

            if (ctx.rand(2047) < a.m_config.wp && apply_move(t, vars, arith_move_type::random_inc_dec))
                continue;

            if (apply_move(t, vars, arith_move_type::hillclimb))
                continue;

            if (apply_move(t, vars, arith_move_type::random_update))
                recalibrate_weights();
        }
        if (a.m_stats.m_steps >= a.m_config.max_moves)
            a.m_config.max_moves_base += 100;
        finalize_bool_assignment();
    }

    template<typename num_t>
    expr* arith_lookahead<num_t>::get_candidate_unsat() {
        expr* e = nullptr;
        if (a.m_config.ucb) {
            double max = -1.0;            
            for (auto f : ctx.input_assertions()) {
                if (get_bool_value(f))
                    continue;

                auto const& vars = get_fixable_exprs(f);
                if (vars.empty())
                    continue;
                auto score = old_score(f);
                auto q = score
                    + a.m_config.ucb_constant * ::sqrt(log((double)m_touched) / get_touched(f))
                    + a.m_config.ucb_noise * ctx.rand(512);
                if (q > max)
                    max = q, e = f;
            }
            if (e) {
                m_touched++;
                inc_touched(e);
            }
        }
        else {
            unsigned n = 0;
            for (auto a : ctx.input_assertions())
                if (!get_bool_value(a) && !get_fixable_exprs(a).empty() && ctx.rand() % ++n == 0)
                    e = a;
        }

        m_last_atom = e;
        CTRACE("arith", !e, tout << "no unsatisfiable candidate\n";);
        CTRACE("arith", e, 
            tout << "select " << mk_bounded_pp(e, m) << " ";
            for (auto v : get_fixable_exprs(e)) 
                tout << mk_bounded_pp(v, m) << " ";        
            tout << "\n");
        return e;
    }



}

template class sls::arith_lookahead<checked_int64<true>>;
template class sls::arith_lookahead<rational>;

