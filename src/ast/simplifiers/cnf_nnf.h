/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    cnf_nnf.h

Abstract:

    pull nested quantifiers

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-24

--*/

#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/normal_forms/pull_quant.h"


class cnf_nnf_simplifier : public dependent_expr_simplifier {

    defined_names m_defined_names;
    
public:
    cnf_nnf_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& fmls):
        dependent_expr_simplifier(m, fmls),
        m_pull(m) {
    }

    char const* name() const override { return "cnf-nnf"; }
    
    void reduce() override {
        nnf apply_nnf(m, m_defined_names);
        expr_ref_vector  push_todo(m);
        proof_ref_vector push_todo_prs(m);
        proof_ref pr(m);
        expr_ref r(m);
        unsigned sz = qtail();
        for (unsigned i = qhead(); i < sz && m.inc(); ++i) {
            auto d = m_fmls[idx];                
            push_todo.reset();
            push_todo_prs.reset();
            apply_nnf(d.fml(), push_todo, push_todo_prs, r, pr);
            m_fmls.update(i, dependent_expr(m, r, d.dep()));
            for (expr* f : m_push_todo) {
                if (!m.inc())
                    break;
                m_rewriter(f, r, pr);
                m_fmls.add(i, depdendent_expr(m, r, d.dep()));
            }
        }
    }
};
