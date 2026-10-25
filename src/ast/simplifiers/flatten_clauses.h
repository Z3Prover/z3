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

    // A conjunction appears as a disjunct either as (and b_i) or as (not (or b_i)).
    // Return the node that identifies it, or nullptr if e is not a conjunction.
    expr* conjunction_of(expr* e) {
        if (m.is_and(e))
            return e;
        if (m.is_not(e, e) && m.is_or(e))
            return e;
        return nullptr;
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

    /**
       \brief rewrite (or a (and b_i)) into the clauses (or a b_i) when the conjunction
       (and b_i) is a disjunct of a single top-level clause. This avoids a literal for the conjunction.

       A conjunction that is a disjunct of several clauses is left alone: distributing it
       would copy its conjuncts into every clause. Without the check, 
       (or (and a_1 .. a_n) (and b_1 .. b_m)) is first rewritten to the m clauses 
       (or (and a_1 .. a_n) b_j), and the next round distributes (and a_1 .. a_n) into
       each of them, producing n*m clauses.
    */
    void reduce() override {
        unsigned nf = m_num_flat + 1;        
        obj_map<expr, unsigned> occurrences;
        auto count_key = [&](expr* c) { occurrences.insert_if_not_there(c, 0)++; };
        auto count = [&](expr* e) {
            if (expr* c = conjunction_of(e))
                count_key(c);
        };
        auto can_distribute = [&](expr* e) {
            unsigned n = 0;
            return occurrences.find(e, n) && n == 1;
        };
        while (nf != m_num_flat) {
            nf = m_num_flat;
            occurrences.reset();
            for (unsigned idx : indices()) {
                expr* f = m_fmls[idx].fml(), *a, *b;
                if (m.is_or(f, a, b)) {
                    count(a);
                    count(b);
                }
                else if (m.is_not(f, f) && m.is_and(f, a, b)) {
                    // the clause (or (not a) (not b)): a conjunction appears as (not (or ..))
                    if (m.is_or(a)) count_key(a);
                    if (m.is_or(b)) count_key(b);
                }
            }
            for (unsigned idx : indices()) {
                auto de = m_fmls[idx];
                expr* f = de.fml(), *a, *b, *c;
                bool decomposed = false;
                // (or a (not (or b_i)) => and_i (or a (not b_i))
                if (m.is_or(f, a, b) && m.is_not(b, c) && m.is_or(c) && can_distribute(c)) 
                    decomposed = true;
                else if (m.is_or(f, b, a) && m.is_not(b, c) && m.is_or(c) && can_distribute(c))
                    decomposed = true;
                if (decomposed) {
                    for (expr* arg : *to_app(c)) 
                        m_fmls.add(dependent_expr(m, m.mk_or(a, mk_not(m, arg)), nullptr,  de.dep()));
                    m_fmls.update(idx, dependent_expr(m, m.mk_true(), nullptr, nullptr));
                    ++m_num_flat;
                    continue;
                }
                // (or a (and b_i)) => and_i (or a b_i)
                if (m.is_or(f, a, b) && m.is_and(b) && can_distribute(b))
                    decomposed = true;
                else if (m.is_or(f, b, a) && m.is_and(b) && can_distribute(b))
                    decomposed = true;
                if (decomposed) {
                    for (expr * arg : *to_app(b))
                        m_fmls.add(dependent_expr(m, m.mk_or(a, arg), nullptr,  de.dep()));
                    m_fmls.update(idx, dependent_expr(m, m.mk_true(), nullptr,  nullptr));
                    ++m_num_flat;
                    continue;
                }
                // not (and a (or b_i)) => and_i (not a) or (not b_i)
                if (m.is_not(f, c) && m.is_and(c, a, b) && m.is_or(b) && can_distribute(b))
                    decomposed = true;
                else if (m.is_not(f, c) && m.is_and(c, b, a) && m.is_or(b) && can_distribute(b))
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
