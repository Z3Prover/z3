/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    flatten_clauses.h

Abstract:

    flatten clauses

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-24

--*/

#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/ast_util.h"


class flatten_clauses : public dependent_expr_simplifier {

    unsigned m_num_flat = 0;

    bool is_literal(expr* a) {
        m.is_not(a, a);
        if (m.is_eq(a) && !m.is_iff(a))
            return true;
        if (!is_app(a))
            return true;
        return to_app(a)->get_family_id() != m.get_basic_family_id();
    }

    bool is_reducible(expr* a, expr* b) {
        return b->get_ref_count() == 1 || is_literal(a);
    }

public:
    flatten_clauses(ast_manager& m, params_ref const& p, dependent_expr_state& fmls):
        dependent_expr_simplifier(m, fmls) {
    }

    char const* name() const override { return "flatten-clauses"; }

    void reset_statistics() override { m_num_flat = 0; }

    void collect_statistics(statistics& st) const override {
        st.update("flatten-clauses-rewrites", m_num_flat);
    }
        
    void reduce() override {
        unsigned nf = m_num_flat + 1;        
        while (nf != m_num_flat) {
            nf = m_num_flat;
            for (unsigned idx : indices()) {
                auto de = m_fmls[idx];
                expr* f = de.fml(), *a, *b, *c;
                bool decomposed = false;
                // (or a (not (or b_i)) => and_i (or a (not b_i))
                if (m.is_or(f, a, b) && m.is_not(b, b) && m.is_or(b) && is_reducible(a, b)) 
                    decomposed = true;
                else if (m.is_or(f, b, a) && m.is_not(b, b) && m.is_or(b) && is_reducible(a, b))
                    decomposed = true;
                if (decomposed) {
                    for (expr* arg : *to_app(b)) 
                        m_fmls.add(dependent_expr(m, m.mk_or(a, mk_not(m, arg)), nullptr,  de.dep()));
                    m_fmls.update(idx, dependent_expr(m, m.mk_true(), nullptr, nullptr));
                    ++m_num_flat;
                    continue;
                }
                // (or a (and b_i)) => and_i (or a b_i)
                if (m.is_or(f, a, b) && m.is_and(b) && is_reducible(a, b))
                    decomposed = true;
                else if (m.is_or(f, b, a) && m.is_and(b) && is_reducible(a, b))
                    decomposed = true;
                if (decomposed) {
                    for (expr * arg : *to_app(b))
                        m_fmls.add(dependent_expr(m, m.mk_or(a, arg), nullptr,  de.dep()));
                    m_fmls.update(idx, dependent_expr(m, m.mk_true(), nullptr,  nullptr));
                    ++m_num_flat;
                    continue;
                }
                // not (and a (or b_i)) => and_i (not a) or (not b_i)
                if (m.is_not(f, c) && m.is_and(c, a, b) && m.is_or(b) && is_reducible(a, b))
                    decomposed = true;
                else if (m.is_not(f, c) && m.is_and(c, b, a) && m.is_or(b) && is_reducible(a, b))
                    decomposed = true;
                if (decomposed) {
                    expr* na = mk_not(m, a);
                    for (expr* arg : *to_app(b))
                        m_fmls.add(dependent_expr(m, m.mk_or(na, mk_not(m, arg)), nullptr, de.dep()));
                    m_fmls.update(idx, dependent_expr(m, m.mk_true(), nullptr, nullptr));
                    ++m_num_flat;
                    continue;
                }
                if (m.is_implies(f, a, b)) {
                    m_fmls.update(idx, dependent_expr(m, m.mk_or(mk_not(m, a), b), nullptr, de.dep()));
                    ++m_num_flat;
                    continue;
                }
                if (m.is_ite(f, a, b, c)) {
                    m_fmls.add(dependent_expr(m, m.mk_or(mk_not(m, a), b), nullptr, de.dep()));
                    m_fmls.add(dependent_expr(m, m.mk_or(a, c), nullptr, de.dep()));
                    m_fmls.update(idx, dependent_expr(m, m.mk_true(), nullptr, nullptr));
                    ++m_num_flat;
                    continue;
                }
            }
        }
    }
};
