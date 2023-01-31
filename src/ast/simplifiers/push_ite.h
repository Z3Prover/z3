
/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    push_ite.h

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-24

--*/

#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/rewriter/push_app_ite.h"


class push_ite_simplifier : public dependent_expr_simplifier {
    push_app_ite_rw m_push;
    
public:
    push_ite_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& fmls, bool c):
        dependent_expr_simplifier(m, fmls),
        m_push(m) {
        m_push.set_conservative(c);
    }

    char const* name() const override { return "push-app-ite"; }
        
    void reduce() override {
        expr_ref r(m);
        for (unsigned idx : indices()) {
            auto const& d = m_fmls[idx];
            m_push(d.fml(), r);
            if (r != d.fml())
                m_fmls.update(idx, dependent_expr(m, r, nullptr, d.dep()));
        }
    }
};


class ng_push_ite_simplifier : public dependent_expr_simplifier {
    ng_push_app_ite_rw m_push;
    
public:
    ng_push_ite_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& fmls, bool c):
        dependent_expr_simplifier(m, fmls),
        m_push(m) {
        m_push.set_conservative(c);
    }

    char const* name() const override { return "ng-push-app-ite"; }
        
    void reduce() override {
        expr_ref r(m);
        for (unsigned idx : indices()) {
            auto const& d = m_fmls[idx];
            m_push(d.fml(), r);
            m_fmls.update(idx, dependent_expr(m, r, nullptr, d.dep()));
        }
    }
};

/*
  ADD_SIMPLIFIER("push-app-ite-conservative", "Push functions over if-then else.", "alloc(push_ite_simplifier, m, p, s, true)")
  ADD_SIMPLIFIER("push-app-ite", "Push functions over if-then else.", "alloc(push_ite_simplifier, m, p, s, false)")
  ADD_SIMPLIFIER("ng-push-app-ite-conservative", "Push functions over if-then-else within non-ground terms only.", "alloc(ng_push_ite_simplifier, m, p, s, true)")
  ADD_SIMPLIFIER("ng-push-app-ite", "Push functions over if-then-else within non-ground terms only.", "alloc(ng_push_ite_simplifier, m, p, s, false)")
*/
