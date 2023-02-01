/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    refine_inj_axiom.h

Abstract:

    refine injectivity axiom

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-24

--*/

#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/rewriter/inj_axiom.h"



class refine_inj_axiom_simplifier : public dependent_expr_simplifier {

public:
    refine_inj_axiom_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& fmls):
        dependent_expr_simplifier(m, fmls) {
    }

    char const* name() const override { return "refine-injectivity"; }
        
    void reduce() override {
        if (!m_fmls.has_quantifiers())
            return;
        expr_ref r(m);
        for (unsigned idx : indices()) {
            expr* f = m_fmls[idx].fml();
            if (is_quantifier(f) && simplify_inj_axiom(m, to_quantifier(f), r)) 
                m_fmls.update(idx, dependent_expr(m, r, nullptr, m_fmls[idx].dep()));            
        }
    }
};

/*
  ADD_SIMPLIFIER("refine-injectivity", "refine injectivity axioms.", "alloc(refine_inj_axiom_simplifier, m, p, s)")
*/
