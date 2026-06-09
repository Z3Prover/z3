/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_subset.h

Abstract:

    Heuristic regular-expression subset checks used by seq_rewriter.

Author:

    Nikolaj Bjorner (nbjorner) 2026-6-8

--*/
#pragma once

#include "ast/seq_decl_plugin.h"

class seq_subset {
    seq_util::rex& m_re;
    static constexpr unsigned m_max_depth = 3;

    bool is_subset_rec(expr* a, expr* b, unsigned depth) const;

public:
    explicit seq_subset(seq_util::rex& re) : m_re(re) {}
    bool is_subset(expr* a, expr* b) const;
};
