/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    propagate_values.h

Abstract:

    relatively cheap value propagation

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-24

Notes:
    incremental version of propagate_values_tactic, to be replaced

--*/

#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/rewriter/th_rewriter.h"


class propagate_values : public dependent_expr_simplifier {

    struct stats {
        unsigned m_num_rewrites = 0;
        void reset() { memset(this, 0, sizeof(*this)); }
    };

    th_rewriter            m_rewriter;
    stats                  m_stats;
    unsigned               m_max_rounds = 4;

public:
    propagate_values(ast_manager& m, params_ref const& p, dependent_expr_state& fmls);
    void reduce() override;
    void collect_statistics(statistics& st) const override;
    void reset_statistics() override { m_stats.reset(); }
    void updt_params(params_ref const& p) override;
    void collect_param_descrs(param_descrs& r) override;
};
