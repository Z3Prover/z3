/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    solve_eqs.cpp

Abstract:

    simplifier for solving equations

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-2.

Notes:

extract_subst is inefficient.
It traverses the same sub-terms many times.

Outline of a presumably better scheme:

1. maintain map FV: term -> bit-set where bitset reprsents set of free variables. Assume the number of variables is bounded.
   FV is built from initial terms.
2. maintain parent: term -> term-list of parent occurrences.
3. repeat
   pick x = t, such that x not in FV(t)
        orient x -> t
        for p in parent*(x):
            FV(p) := FV(p) u FV(t)
        if y = s is processed and x in FV(s) order y < x
        if y = s is processed and x in FV(t) order x < y

--*/


#include "util/trace.h"
#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/occurs.h"
#include "ast/recfun_decl_plugin.h"
#include "ast/rewriter/expr_replacer.h"
#include "ast/simplifiers/solve_eqs.h"
#include "ast/simplifiers/solve_context_eqs.h"
#include "ast/converters/generic_model_converter.h"
#include "params/tactic_params.hpp"


namespace euf {

    void solve_eqs::get_eqs(dep_eq_vector& eqs) {
        for (extract_eq* ex : m_extract_plugins)
            for (unsigned i : indices())
                ex->get_eqs(m_fmls[i], eqs);
    }

    // initialize graph that maps variable ids to next ids
    void solve_eqs::extract_dep_graph(dep_eq_vector& eqs) {
        m_var2id.reset();
        m_id2var.reset();
        m_next.reset();
        unsigned sz = 0;
        for (auto const& [orig, v, t, d] : eqs)
            sz = std::max(sz, v->get_id());
        m_var2id.resize(sz + 1, UINT_MAX);
        for (auto const& [orig, v, t, d] : eqs) {
            if (is_var(v) || !can_be_var(v))
                continue;
            m_var2id[v->get_id()] = m_id2var.size();
            m_id2var.push_back(v);
        }
        m_next.resize(m_id2var.size());

        for (auto const& eq : eqs)
            if (can_be_var(eq.var))
                m_next[var2id(eq.var)].push_back(eq);
    }

    /**
    * Build a substitution while assigning levels to terms.
    * The substitution is well-formed when variables are replaced with terms whose
    * Free variables have higher levels.
    */
    void solve_eqs::extract_subst() {
        m_id2level.reset();
        m_id2level.resize(m_id2var.size(), UINT_MAX);
        m_subst_ids.reset();
        m_subst = alloc(expr_substitution, m, true, false);        

        auto is_explored = [&](unsigned id) {
            return m_id2level[id] != UINT_MAX;
        };

        unsigned init_level = UINT_MAX;
        unsigned_vector todo;
        
        for (unsigned id = 0; id < m_id2var.size(); ++id) {
            if (is_explored(id))
                continue;
            // initialize current level to have enough room to assign different levels to all variables.
            if (init_level < m_id2var.size() + 1)
                return;
            init_level -= m_id2var.size() + 1;
            unsigned curr_level = init_level;
            todo.push_back(id);
            
            while (!todo.empty()) {
                unsigned j = todo.back();
                todo.pop_back();
                if (is_explored(j))
                    continue;
                m_id2level[j] = curr_level++;

                for (auto const& eq : m_next[j]) {
                    auto const& [orig, v, t, d] = eq;
                    SASSERT(j == var2id(v));
                    if (m_fmls.frozen(v))
                        continue;
                    
                    bool is_safe = true;                    
                    unsigned todo_sz = todo.size();

                    // determine if substitution is safe.
                    // all time-stamps must be at or above current level
                    // unexplored variables that are part of substitution are appended to work list.
                    SASSERT(m_todo.empty());
                    m_todo.push_back(t);
                    expr_fast_mark1 visited;
                    while (!m_todo.empty()) {
                        expr* e = m_todo.back();
                        m_todo.pop_back();
                        if (visited.is_marked(e))
                            continue;
                        visited.mark(e, true);
                        if (is_app(e)) {
                            for (expr* arg : *to_app(e))
                                m_todo.push_back(arg);
                        }
                        else if (is_quantifier(e))
                            m_todo.push_back(to_quantifier(e)->get_expr());
                        if (!is_var(e))
                            continue;
                        if (m_id2level[var2id(e)] < curr_level) {
                            is_safe = false;
                            break;
                        }
                        if (!is_explored(var2id(e)))
                            todo.push_back(var2id(e));
                    }
                    m_todo.reset();
                    visited.reset();

                    if (!is_safe) {
                        todo.shrink(todo_sz);
                        continue;
                    }
                    SASSERT(!occurs(v, t));
                    m_next[j][0] = eq;
                    m_subst_ids.push_back(j);                   
                    break;
                }
            }                   
        }
    }

    void solve_eqs::normalize() {
        if (m_subst_ids.empty())
            return;
        scoped_ptr<expr_replacer> rp = mk_default_expr_replacer(m, false);
        rp->set_substitution(m_subst.get());

        std::sort(m_subst_ids.begin(), m_subst_ids.end(), [&](unsigned u, unsigned v) { return m_id2level[u] > m_id2level[v]; });

        for (unsigned id : m_subst_ids) {
            if (!m.inc())
                return;
            auto const& [orig, v, def, dep] = m_next[id][0];
            auto [new_def, new_dep] = rp->replace_with_dep(def);
            m_stats.m_num_steps += rp->get_num_steps() + 1;
            ++m_stats.m_num_elim_vars;
            new_dep = m.mk_join(dep, new_dep);
            IF_VERBOSE(11, verbose_stream() << mk_bounded_pp(v, m) << " -> " << mk_bounded_pp(new_def, m) << "\n");
            m_subst->insert(v, new_def, new_dep);
            SASSERT(can_be_var(v));
            // we updated the substitution, but we don't need to reset rp
            // because all cached values there do not depend on v.
        }

        TRACE("solve_eqs",
            tout << "after normalizing variables\n";
        for (unsigned id : m_subst_ids) {
            auto const& eq = m_next[id][0];
            expr* def = m_subst->find(eq.var);
            tout << mk_pp(eq.var, m) << "\n----->\n" << mk_pp(def, m) << "\n\n";
        });


    }

    void solve_eqs::apply_subst(vector<dependent_expr>& old_fmls) {
        if (!m.inc())
            return;
        if (m_subst_ids.empty())
            return;
        
        scoped_ptr<expr_replacer> rp = mk_default_expr_replacer(m, false);
        rp->set_substitution(m_subst.get());

        for (unsigned i : indices()) {
            auto [f, p, d] = m_fmls[i]();
            auto [new_f, new_dep] = rp->replace_with_dep(f);
            proof_ref new_pr(m);
            expr_ref tmp(m);
            m_rewriter(new_f, tmp, new_pr);
            if (tmp == f)
                continue;
            new_dep = m.mk_join(d, new_dep);
            old_fmls.push_back(m_fmls[i]);
            m_fmls.update(i, dependent_expr(m, tmp, mp(p, new_pr), new_dep));
        }
    }
    
    void solve_eqs::reduce() {

        m_fmls.freeze_suffix();

        for (extract_eq* ex : m_extract_plugins)
            ex->pre_process(m_fmls);

        unsigned count = 0;
        vector<dependent_expr> old_fmls;
        dep_eq_vector eqs;
        do {
            old_fmls.reset();
            m_subst_ids.reset();
            eqs.reset();
            get_eqs(eqs);
            extract_dep_graph(eqs);
            extract_subst();
            normalize();
            apply_subst(old_fmls);
            ++count;
            save_subst({});
        } 
        while (!m_subst_ids.empty() && count < 20 && m.inc());

        if (!m.inc())
            return;

        if (m_config.m_context_solve) {            
            old_fmls.reset();
            m_subst_ids.reset();
            eqs.reset();
            solve_context_eqs context_solve(*this);
            context_solve.collect_nested_equalities(eqs);
            extract_dep_graph(eqs);
            extract_subst();
            normalize();
            apply_subst(old_fmls);
            save_subst(old_fmls);
        }
    }

    void solve_eqs::collect_num_occs(expr * t, expr_fast_mark1 & visited) {
        ptr_buffer<app, 128> stack;
        
        auto visit = [&](expr* arg) {
            if (is_uninterp_const(arg))                    
                m_num_occs.insert_if_not_there(arg, 0)++;
            if (!visited.is_marked(arg) && is_app(arg)) {                          
                visited.mark(arg, true);                            
                stack.push_back(to_app(arg));                               
            }                                                       
        };
        
        visit(t);
        
        while (!stack.empty()) {
            app * t = stack.back();
            stack.pop_back();
            for (expr* arg : *t) 
                visit(arg);
        }
    }

    void solve_eqs::collect_num_occs() {
        if (m_config.m_max_occs == UINT_MAX)
            return; // no need to compute num occs
        m_num_occs.reset();
        expr_fast_mark1 visited;
        for (unsigned i : indices())
            collect_num_occs(m_fmls[i].fml(), visited);
    }

    // Check if the number of occurrences of t is below the specified threshold :solve-eqs-max-occs
    bool solve_eqs::check_occs(expr * t) const {
        if (m_config.m_max_occs == UINT_MAX)
            return true;
        unsigned num = 0;
        m_num_occs.find(t, num);
        TRACE("solve_eqs_check_occs", tout << mk_ismt2_pp(t, m) << " num_occs: " << num << " max: " << m_config.m_max_occs << "\n";);
        return num <= m_config.m_max_occs;
    }

    void solve_eqs::save_subst(vector<dependent_expr> const& old_fmls) {
        if (!m_subst->empty())   
            m_fmls.model_trail().push(m_subst.detach(), old_fmls, false);                
    }

    void solve_eqs::filter_unsafe_vars() {
        m_unsafe_vars.reset();
        recfun::util rec(m);
        for (func_decl* f : rec.get_rec_funs())
            for (expr* term : subterms::all(expr_ref(rec.get_def(f).get_rhs(), m), &m_todo, &m_visited))
                m_unsafe_vars.mark(term);
    }

    solve_eqs::solve_eqs(ast_manager& m, dependent_expr_state& fmls) : 
        dependent_expr_simplifier(m, fmls), m_rewriter(m) {
        register_extract_eqs(m, m_extract_plugins);
        m_rewriter.set_flat_and_or(false);
    }

    void solve_eqs::updt_params(params_ref const& p) {
        tactic_params tp(p);
        m_config.m_max_occs = p.get_uint("solve_eqs_max_occs", tp.solve_eqs_max_occs());
        m_config.m_context_solve = p.get_bool("context_solve", tp.solve_eqs_context_solve());
        for (auto* ex : m_extract_plugins)
            ex->updt_params(p);
        m_rewriter.updt_params(p);
    }

    void solve_eqs::collect_param_descrs(param_descrs& r) {
        r.insert("solve_eqs_max_occs", CPK_UINT, "(default: infty) maximum number of occurrences for considering a variable for gaussian eliminations.", "4294967295");
        r.insert("theory_solver", CPK_BOOL, "theory solvers.", "true");
        r.insert("ite_solver", CPK_BOOL, "use if-then-else solver.", "true");
        r.insert("context_solve", CPK_BOOL, "solve equalities under disjunctions.", "false");
        r.insert("eliminate_mod", CPK_BOOL, "eliminate modulus from equations", "true");
    }

    void solve_eqs::collect_statistics(statistics& st) const {
        st.update("solve-eqs-steps", m_stats.m_num_steps);
        st.update("solve-eqs-elim-vars", m_stats.m_num_elim_vars);
    }

}
