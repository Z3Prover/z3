/*++
Copyright (c) 2026 Microsoft Corporation

Eliminate one-sided real variables through Boolean combinations of linear inequalities.
--*/
#pragma once

#include "ast/arith_decl_plugin.h"
#include "ast/simplifiers/dependent_expr_state.h"

class elim_monotone : public dependent_expr_simplifier {
    arith_util a;
    unsigned m_eliminated = 0;

    bool eliminate();

public:
    elim_monotone(ast_manager& m, dependent_expr_state& fmls) :
        dependent_expr_simplifier(m, fmls), a(m) {}

    char const* name() const override { return "elim-monotone"; }
    void reduce() override;
    void reset_statistics() override { m_eliminated = 0; }
    void collect_statistics(statistics& st) const override { st.update("elim-monotone", m_eliminated); }
};
