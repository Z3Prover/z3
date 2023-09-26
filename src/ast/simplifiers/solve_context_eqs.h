/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    solve_context_eqs.h

Abstract:

    simplifier for solving equations within a context

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-2.

--*/


#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/simplifiers/extract_eqs.h"

namespace euf {

    class solve_eqs;
    

    class solve_context_eqs {

        ast_manager&              m;
        dependent_expr_state&     m_fmls;
        solve_eqs&                m_solve_eqs;
        expr_mark                 m_and_pos, m_and_neg, m_or_pos, m_or_neg;
        expr_mark                 m_contains_v;
        ptr_vector<expr>          m_todo;

        typedef svector<std::pair<bool, expr*>> signed_expressions;

        bool contains_v(expr* f) const { return m_contains_v.is_marked(f); }
        bool is_safe_eq(expr* e);
        bool is_safe_eq(unsigned recursion_depth, expr* f, bool sign, expr* e);
        bool is_safe_eq(expr* f, expr* e) { return is_safe_eq(0, f, false, e); }
        bool is_disjunctively_safe(unsigned recursion_depth, expr* f, bool sign, expr* e);
        bool contains_conjunctively(expr* f, bool sign, expr* e, signed_expressions& conjuncts);
        bool is_conjunction(bool sign, expr* f) const;
        
        void collect_nested_equalities(dependent_expr const& f, expr_mark& visited, dep_eq_vector& eqs);

        bool is_safe_var(expr* x, unsigned i, expr* f, svector<std::tuple<bool,unsigned,expr*,unsigned>> const& todo);

    public:
        
        solve_context_eqs(solve_eqs& s);

        void collect_nested_equalities(dep_eq_vector& eqs);

    };
}
