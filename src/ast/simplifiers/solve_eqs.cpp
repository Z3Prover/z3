/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    solve_eqs.cpp

Abstract:

    simplifier for solving equations

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-2.

--*/



#include "ast/simplifiers/solve_eqs.h"


namespace euf {


    void solve_eqs::init() {

    }

    // initialize graph that maps variable ids to next ids
    void solve_eqs::extract_dep_graph(dep_eq_vector& eqs) {
        m_var2id.reset();
        m_id2var.reset();
        m_next.reset();
        unsigned sz = 0;
        for (auto const& [v, t, d] : eqs)
            sz = std::max(sz, v->get_id());
        m_var2id.resize(sz + 1, UINT_MAX);
        for (auto const& [v, t, d] : eqs) {
            if (is_var(v))
                continue;
            m_var2id[v->get_id()] = m_id2var.size();
            m_id2var.push_back(v);
        }
        m_next.resize(m_id2var.size());

        for (auto const& [v, t, d] : eqs)
            m_next[var2id(v)].push_back(t);
    }

    void solve_eqs::add_subst(app* v, expr* term) {

    }

    /**
    * Build a substitution while assigning levels to terms.
    * The substitution is well-formed when variables are replaced with terms whose
    * Free variables have higher levels.
    */
    void solve_eqs::extract_subst() {
        m_var2level.reset();
        m_var2level.resize(m_id2var.size(), UINT_MAX);
        auto is_explored = [&](unsigned id) {
            return m_var2level[id] != UINT_MAX;
        };
        auto is_safe = [&](unsigned lvl, expr* t) {
            for (auto* e : subterms::all(expr_ref(t, m)))
                if (is_var(e) && m_var2level[var2id(e)] < lvl)
                    return false;
        };

        unsigned init_level = UINT_MAX;
        for (unsigned id = 0; id < m_id2var.size(); ++id) {
            if (is_explored(id))
                continue;
            // initialize current level to have enough room to assign different levels to all variables.
            init_level -= m_id2var.size() + 1;
            unsigned curr_level = init_level;
            todo.push_back(id);
            while (!todo.empty()) {
                unsigned j = todo.back();
                todo.pop_back();
                if (is_explored(j))
                    continue;
                m_var2level[id] = curr_level++;
                for (expr* t : m_next[j]) {
                    if (!is_safe(curr_level, t))
                        continue;
                    add_subst(m_id2var[j], t);
                    for (auto* e : subterms::all(expr_ref(t, m))) 
                        if (is_var(e) && !is_explored(var2id(e))) 
                            todo.push_back(var2id(e));   
                    break;
                }
            }            
        }
    }

    void solve_eqs::extract_subst(dep_eq_vector& eqs, dep_eq_vector& subst) {

    }

    void solve_eqs::apply_subst() {

    }
    
    void solve_eqs::reduce() {
        init();
        dep_eq_vector eqs, subst;
        get_eqs(eqs);
        extract_subst(eqs, subst);
        apply_subst();
        advance_qhead(m_fmls.size());
    }

}
