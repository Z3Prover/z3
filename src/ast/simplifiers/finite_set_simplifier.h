/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    finite_set_simplifier.h

Abstract:

    Simplify bounded quantification encoded by finite-set filters.

--*/
#pragma once

#include "ast/simplifiers/dependent_expr_state.h"

class finite_set_simplifier : public dependent_expr_simplifier {
    struct rw_cfg;
    struct rw;

    params_ref m_params;
    unsigned m_fixed_points = 0;
    unsigned m_unused_vars = 0;
    unsigned m_independent_guards = 0;
    unsigned m_empty_domains = 0;
    unsigned m_extrema = 0;

public:
    finite_set_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& s):
        dependent_expr_simplifier(m, s), m_params(p) {}

    char const* name() const override { return "finite-set-simplify"; }
    void reduce() override;
    void collect_statistics(statistics& st) const override;
    void reset_statistics() override;
    void updt_params(params_ref const& p) override { m_params.append(p); }
    void collect_param_descrs(param_descrs& r) override;
};

Z3_ADD_SIMPLIFIER(finite_set, "finite-set-simplify", "simplify bounded quantification over native finite sets.", alloc(finite_set_simplifier, m, p, s));
