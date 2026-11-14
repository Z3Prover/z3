/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_regular_simplifier.h

Abstract:

    Decimal constant comparisons and bounded regular preimages of string observations.
    Run on original assertions, before general sequence rewriting.

--*/
#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "util/stopwatch.h"

class seq_regular_simplifier : public dependent_expr_simplifier {
    bool m_automatic = false;
    bool m_enabled = true;
    unsigned m_max_steps = 100000;
    unsigned m_steps = 0, m_preimages = 0, m_rewritten = 0, m_stoi_rewritten = 0;
    unsigned m_unsupported = 0, m_budget = 0, m_skipped = 0;
    stopwatch m_watch;
public:
    static bool has_string_terms(ast_manager& m, expr* e);
    seq_regular_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& s, bool automatic = false);
    char const* name() const override { return "seq-regular"; }
    void reduce() override;
    void updt_params(params_ref const& p) override;
    void collect_param_descrs(param_descrs& r) override;
    void collect_statistics(statistics& st) const override;
    void reset_statistics() override;
};

Z3_ADD_SIMPLIFIER(seq_regular, "seq-regular",
                 "lower decimal constant comparisons and fully regular string goals to memberships.",
                 alloc(seq_regular_simplifier, m, p, s));
