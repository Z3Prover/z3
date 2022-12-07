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
#include "ast/normal_forms/nnf.h"
#include "ast/rewriter/th_rewriter.h"


class cnf_nnf_simplifier : public dependent_expr_simplifier {

    defined_names m_defined_names;
    th_rewriter   m_rewriter;
    
public:
    cnf_nnf_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& fmls):
        dependent_expr_simplifier(m, fmls),
        m_defined_names(m),
        m_rewriter(m, p){
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
            auto d = m_fmls[i];                
            push_todo.reset();
            push_todo_prs.reset();
            apply_nnf(d.fml(), push_todo, push_todo_prs, r, pr);
            m_fmls.update(i, dependent_expr(m, r, mp(d.pr(), pr), d.dep()));
            for (expr* f : push_todo) {
                if (!m.inc())
                    break;
                m_rewriter(f, r, pr);
                if (f != r)
                    m_fmls.add(dependent_expr(m, r, pr, d.dep()));
            }
        }
    }

    void push() override { dependent_expr_simplifier::push(); m_defined_names.push(); }

    void pop(unsigned n) override { dependent_expr_simplifier::pop(n); m_defined_names.pop(n); }
};
