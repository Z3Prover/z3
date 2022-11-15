/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    solve_eqs.cpp

Abstract:

    simplifier for solving equations

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-2.

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
            for (unsigned i = m_qhead; i < m_fmls.size(); ++i)
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

        auto is_safe = [&](unsigned lvl, expr* t) {
            for (auto* e : subterms::all(expr_ref(t, m), &m_todo, &m_visited)) 
                if (is_var(e) && m_id2level[var2id(e)] < lvl)
                    return false;            
            return true;
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
                    if (!is_safe(curr_level, t))
                        continue;
                    SASSERT(!occurs(v, t));
                    m_next[j][0] = eq;
                    m_subst_ids.push_back(j);                   
                    for (expr* e : subterms::all(expr_ref(t, m), &m_todo, &m_visited))
                        if (is_var(e) && !is_explored(var2id(e))) 
                            todo.push_back(var2id(e));   
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

        for (unsigned i = m_qhead; i < m_fmls.size() && !m_fmls.inconsistent(); ++i) {
            auto [f, d] = m_fmls[i]();
            auto [new_f, new_dep] = rp->replace_with_dep(f);
            m_rewriter(new_f);
            if (new_f == f)
                continue;
            new_dep = m.mk_join(d, new_dep);
            old_fmls.push_back(m_fmls[i]);
            m_fmls.update(i, dependent_expr(m, new_f, new_dep));
        }
    }
    
    void solve_eqs::reduce() {

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

        advance_qhead(m_fmls.size());
    }

    void solve_eqs::save_subst(vector<dependent_expr> const& old_fmls) {
        if (!m_subst->empty())   
            m_fmls.model_trail().push(m_subst.detach(), old_fmls);                
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
    }

    void solve_eqs::collect_param_descrs(param_descrs& r) {
        r.insert("solve_eqs_max_occs", CPK_UINT, "(default: infty) maximum number of occurrences for considering a variable for gaussian eliminations.");
        r.insert("theory_solver", CPK_BOOL, "(default: true) use theory solvers.");
        r.insert("ite_solver", CPK_BOOL, "(default: true) use if-then-else solver.");
        r.insert("context_solve", CPK_BOOL, "(default: false) solve equalities under disjunctions.");
    }

    void solve_eqs::collect_statistics(statistics& st) const {
        st.update("solve-eqs-steps", m_stats.m_num_steps);
        st.update("solve-eqs-elim-vars", m_stats.m_num_elim_vars);
    }

}
