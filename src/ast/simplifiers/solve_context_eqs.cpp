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
        for (unsigned i = 0; i < m_fmls.qtail(); ++i)
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
        unsigned sz = m_fmls.qtail();
        for (unsigned i = m_fmls.qhead(); i < sz; ++i)
            collect_nested_equalities(m_fmls[i], visited, eqs);

        if (eqs.empty())
            return;
        
        std::stable_sort(eqs.begin(), eqs.end(), [&](dependent_eq const& e1, dependent_eq const& e2) {
                return e1.var->get_id() < e2.var->get_id(); });


        // record the first and last occurrence of variables
        // if the first and last occurrence coincide, the variable occurs in only one formula.
        // otherwise it occurs in multiple formulas and should not be considered for solving.
        unsigned_vector occurs1(m.get_num_asts() + 1, sz);
        unsigned_vector occurs2(m.get_num_asts() + 1, sz);

        struct visitor {
            unsigned_vector& occurrence;
            unsigned i = 0;
            unsigned sz = 0;
            visitor(unsigned_vector& occurrence) : occurrence(occurrence), i(0), sz(0) {}
            void operator()(expr* t) {
                occurrence.setx(t->get_id(), i, sz);
            }
        };

        {
            visitor visitor1(occurs1);
            visitor visitor2(occurs2);
            visitor1.sz = sz;
            visitor2.sz = sz;
            expr_fast_mark1 fast_visited;
            for (unsigned i = 0; i < sz; ++i) {
                visitor1.i = i;
                quick_for_each_expr(visitor1, fast_visited, m_fmls[i].fml());
            }
            fast_visited.reset();
            for (unsigned i = sz; i-- > 0; ) {
                visitor2.i = i;
                quick_for_each_expr(visitor2, fast_visited, m_fmls[i].fml());
            }
        }

        unsigned j = 0;
        expr* last_var = nullptr;
        bool was_unsafe = false;
        for (auto const& eq : eqs) {
            if (!eq.var)
                continue;
            unsigned occ1 = occurs1.get(eq.var->get_id(), sz);
            unsigned occ2 = occurs2.get(eq.var->get_id(), sz);
            if (occ1 >= sz)
                continue;
            if (occ1 != occ2)
                continue;
            
            SASSERT(!m.is_bool(eq.var));

            if (eq.var != last_var) {

                m_contains_v.reset();
                
                // first check if v is in term. If it is, then the substitution candidate is unsafe
                m_todo.push_back(eq.term);
                mark_occurs(m_todo, eq.var, m_contains_v);
                SASSERT(m_todo.empty());
                last_var = eq.var;
                was_unsafe = false;
                if (m_contains_v.is_marked(eq.term)) {
                    was_unsafe = true;
                    continue;
                }

                // then mark occurrences
                m_todo.push_back(m_fmls[occ1].fml());
                mark_occurs(m_todo, eq.var, m_contains_v);
                SASSERT(m_todo.empty());
            }
            else if (m_contains_v.is_marked(eq.term))
                continue;
            else if (was_unsafe) 
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

        svector<std::tuple<bool,unsigned,expr*, unsigned>> todo;
        todo.push_back({ false, 0, df.fml(), 0});

        // even depth is conjunctive context, odd is disjunctive
        // when alternating between conjunctive and disjunctive context, increment depth.
        auto inc_or = [](unsigned depth) {
            return (0 == depth % 2) ? depth + 1 : depth;
        };
        auto inc_and = [](unsigned depth) {
            return (0 == depth % 2) ? depth : depth + 1;
        };

        for (unsigned i = 0; i < todo.size(); ++i) {
            auto [s, depth, f, p] = todo[i];
            if (visited.is_marked(f))
                continue;
            visited.mark(f, true);
            if (s && m.is_and(f)) {
                for (auto* arg : *to_app(f))
                    todo.push_back({ s, inc_or(depth), arg, i });
            }
            else if (!s && m.is_or(f)) {
                for (auto* arg : *to_app(f))
                    todo.push_back({ s, inc_or(depth), arg, i });
            }
            if (!s && m.is_and(f)) {
                for (auto* arg : *to_app(f))
                    todo.push_back({ s, inc_and(depth), arg, i });
            }
            else if (s && m.is_or(f)) {
                for (auto* arg : *to_app(f))
                    todo.push_back({ s, inc_and(depth), arg, i });
            }
            else if (m.is_not(f, f))
                todo.push_back({ !s, depth, f, i });
            else if (!s && 1 <= depth) {
                unsigned sz = eqs.size();
                for (extract_eq* ex : m_solve_eqs.m_extract_plugins) {
                    ex->set_allow_booleans(false);
                    ex->get_eqs(dependent_expr(m, f, nullptr, df.dep()), eqs);
                    ex->set_allow_booleans(true);
                }
                // prune eqs for solutions that are not safe in df.fml()
                for (; sz < eqs.size(); ++sz) {
                    if (!is_safe_var(eqs[sz].var, i, df.fml(), todo)) {
                        eqs[sz] = eqs.back();
                        --sz;
                        eqs.pop_back();
                    }
                }
            }
        }
    }
    
    bool solve_context_eqs::is_safe_var(expr* x, unsigned i, expr* f, svector<std::tuple<bool,unsigned,expr*,unsigned>> const& todo) {
        m_contains_v.reset();
        m_todo.push_back(f);
        mark_occurs(m_todo, x, m_contains_v);
        SASSERT(m_todo.empty());

        auto is_parent = [&](unsigned p, unsigned i) {
            while (p != i && i != 0) {
                auto [_s,_depth, _f, _p] = todo[i];
                i = _p;
            }
            return p == i;
        };

        // retrieve oldest parent of i within the same alternation of and
        unsigned pi = i;
        auto [_s, _depth, _f, _p] = todo[i];
        while (pi != 0) {
            auto [s, depth, f, p] = todo[pi];
            if (depth != _depth)
                break;
            pi = p;
        }
        
        // determine if j and j have common conjunctive parent
        // for every j in todo.
        for (unsigned j = 0; j < todo.size(); ++j) {
            auto [s, depth, f, p] = todo[j];
            if (i == j || !m_contains_v.is_marked(f))
                continue;
            if (is_parent(j, i)) // j is a parent if i
                continue;
            if (is_parent(pi, j)) // pi is a parent of j
                continue;
            return false;
        }
        return true;
    }

}
