/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    solve_context_eqs.cpp

Abstract:

    simplifier for solving equations within a context

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-2.

Notes:

The variable v is solved based on expression e.
Check that every occurrence of v uses e in conjunctive context.
     
Walk formulas containing v in as and-or.
Equalities that occur within at least one alternation of or are
considered as candidates.
     
To constrain how formulas are traversed, first
label sub-expressions that contain v. An equality eq is safe for v
if every occurrence of v occurs in the same conjunctive context as eq.

--*/

#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/occurs.h"
#include "ast/simplifiers/solve_context_eqs.h"
#include "ast/simplifiers/solve_eqs.h"

namespace euf {

        
    solve_context_eqs::solve_context_eqs(solve_eqs& s): m(s.m), m_fmls(s.m_fmls), m_solve_eqs(s) {}

    bool solve_context_eqs::is_safe_eq(expr* e) {
        m_and_pos.reset(); m_and_neg.reset(); m_or_pos.reset(); m_or_neg.reset();        
        for (unsigned i = 0; i < m_fmls.size(); ++i)
            if (!is_safe_eq(m_fmls[i].fml(), e))
                return false;
        return true;
    }

    /**
    * Check if some conjunction of f contains equality 'e'.
    * If this is not the case, then check that every conjunct that contains v
    * recursively contains a disjunction that contains 'e'.
    */
    bool solve_context_eqs::is_safe_eq(unsigned recursion_depth, expr* f, bool sign, expr* e) {
        if (!contains_v(f))
            return true;                
        signed_expressions conjuncts;
        if (contains_conjunctively(f, sign, e, conjuncts)) 
            return true;
        if (recursion_depth > 3)
            return false;
        return all_of(conjuncts, [&](std::pair<bool,expr*> const& p) { return is_disjunctively_safe(recursion_depth, p.second, p.first, e); });
    }

    /*
    * Every disjunction in f that contains v also contains the equation e.
    */
    bool solve_context_eqs::is_disjunctively_safe(unsigned recursion_depth, expr* f0, bool sign, expr* e) {
        signed_expressions todo;
        todo.push_back({sign, f0});
        while (!todo.empty()) {
            auto [s, f] = todo.back();
            todo.pop_back();
            if (s && m_or_neg.is_marked(f))
                continue;
            if (!s && m_or_pos.is_marked(f))
                continue;
            if (s)
                m_or_neg.mark(f, true);
            else
                m_or_pos.mark(f, true);
            if (!s && f == e)
                continue;
            else if (!contains_v(f))
                continue;
            else if (s && m.is_and(f)) 
                for (auto* arg : *to_app(f))
                    todo.push_back({s, arg});            
            else if (!s && m.is_or(f)) 
                for (auto* arg : *to_app(f))
                    todo.push_back({s, arg});            
            else if (m.is_not(f, f))
                todo.push_back({!s, f});
            else if (!is_conjunction(s, f))
                return false;
            else if (!is_safe_eq(recursion_depth + 1, f, s, e))
                return false;
        }
        return true;
    }

    bool solve_context_eqs::is_conjunction(bool sign, expr* f) const {
        if (!sign && m.is_and(f))
            return true;
        if (sign && m.is_or(f))
            return true;
        return false;
    }
   
    /**
    * Determine whether some conjunction in f contains e. 
    * If no conjunction contains e, then return the set of conjunctions that contain v.
    */
    bool solve_context_eqs::contains_conjunctively(expr* f, bool sign, expr* e, signed_expressions& conjuncts) {
        signed_expressions todo;
        todo.push_back({sign, f});
        while (!todo.empty()) {
            auto [s, f] = todo.back();
            todo.pop_back();
            if (!s && f == e)
                return true;
            if (!s && m_and_pos.is_marked(f))
                continue;
            if (s && m_and_neg.is_marked(f))
                continue;
            if (s)
                m_and_neg.mark(f, true);
            else
                m_and_pos.mark(f, true);
            if (!contains_v(f))
                continue;
            if (!s && m.is_and(f)) 
                for (auto* arg : *to_app(f))
                    todo.push_back({false, arg});            
            else if (s && m.is_or(f)) 
                for (auto* arg : *to_app(f))
                    todo.push_back({true, arg});            
            else if (m.is_not(f, f))
                todo.push_back({!s, f});
            else
                conjuncts.push_back({s, f});
        }
        return false;
    }

    void solve_context_eqs::collect_nested_equalities(dep_eq_vector& eqs) {
        expr_mark visited;
        for (unsigned i = m_solve_eqs.m_qhead; i < m_fmls.size(); ++i)
            collect_nested_equalities(m_fmls[i], visited, eqs);

        std::stable_sort(eqs.begin(), eqs.end(), [&](dependent_eq const& e1, dependent_eq const& e2) {
                return e1.var->get_id() < e2.var->get_id(); });
        unsigned j = 0;
        expr* last_var = nullptr;
        for (auto const& eq : eqs) {

            SASSERT(!m.is_bool(eq.var));

            if (eq.var != last_var) {

                m_contains_v.reset();
                
                // first check if v is in term. If it is, then the substitution candidate is unsafe
                m_todo.push_back(eq.term);
                mark_occurs(m_todo, eq.var, m_contains_v);
                SASSERT(m_todo.empty());
                last_var = eq.var;
                if (m_contains_v.is_marked(eq.term))
                    continue;

                // then mark occurrences
                for (unsigned i = 0; i < m_fmls.size(); ++i)
                    m_todo.push_back(m_fmls[i].fml());
                mark_occurs(m_todo, eq.var, m_contains_v);
                SASSERT(m_todo.empty());
            }
            else if (m_contains_v.is_marked(eq.term))
                continue;

            // subject to occurrences, check if equality is safe
            if (is_safe_eq(eq.orig)) 
                eqs[j++] = eq;
        }
        eqs.shrink(j);
        TRACE("solve_eqs",
              for (auto const& eq : eqs)
                  tout << eq << "\n");
    }

    void solve_context_eqs::collect_nested_equalities(dependent_expr const& df, expr_mark& visited, dep_eq_vector& eqs) {

        svector<std::tuple<bool,unsigned,expr*>> todo;
        todo.push_back({ false, 0, df.fml()});

        // even depth is conjunctive context, odd is disjunctive
        // when alternating between conjunctive and disjunctive context, increment depth.
        auto inc_or = [](unsigned depth) {
            return (0 == depth % 2) ? depth + 1 : depth;
        };
        auto inc_and = [](unsigned depth) {
            return (0 == depth % 2) ? depth : depth + 1;
        };

        while (!todo.empty()) {
            auto [s, depth, f] = todo.back();
            todo.pop_back();
            if (visited.is_marked(f))
                continue;
            visited.mark(f, true);
            if (s && m.is_and(f)) {
                for (auto* arg : *to_app(f))
                    todo.push_back({ s, inc_or(depth), arg });
            }
            else if (!s && m.is_or(f)) {
                for (auto* arg : *to_app(f))
                    todo.push_back({ s, inc_or(depth), arg });
            }
            if (!s && m.is_and(f)) {
                for (auto* arg : *to_app(f))
                    todo.push_back({ s, inc_and(depth), arg });
            }
            else if (s && m.is_or(f)) {
                for (auto* arg : *to_app(f))
                    todo.push_back({ s, inc_and(depth), arg });
            }
            else if (m.is_not(f, f))
                todo.push_back({ !s, depth, f });
            else if (!s && 1 == depth % 2) {
                for (extract_eq* ex : m_solve_eqs.m_extract_plugins) {
                    ex->set_allow_booleans(false);
                    ex->get_eqs(dependent_expr(m, f, df.dep()), eqs);
                    ex->set_allow_booleans(true);
                }
            }
        }
    }
}
