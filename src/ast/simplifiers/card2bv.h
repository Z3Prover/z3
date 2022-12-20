/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    card2bv.h

Abstract:

    convert cardinality constraints to bit-vectors

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-24


--*/

#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/rewriter/th_rewriter.h"


class card2bv : public dependent_expr_simplifier {

    struct stats {
        unsigned m_num_rewrites = 0;
        void reset() { memset(this, 0, sizeof(*this)); }
    };

    stats                  m_stats;
    params_ref             m_params;

public:
    card2bv(ast_manager& m, params_ref const& p, dependent_expr_state& fmls);
    char const* name() const override { return "card2bv"; }
    void reduce() override;
    void collect_statistics(statistics& st) const override;
    void reset_statistics() override { m_stats.reset(); }
    void updt_params(params_ref const& p) override { m_params.append(p); }
    void collect_param_descrs(param_descrs& r) override;
};
