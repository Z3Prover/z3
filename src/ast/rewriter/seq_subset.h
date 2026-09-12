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
    // Step budget per is_subset call.  The rules branch on both operands
    // (union, intersection, concatenation) and several of them recurse without
    // increasing the depth, so a deeply nested regex spawns exponentially many
    // checks -- derivatives of nested intersections ran for minutes inside a
    // single call, past any time limit.  The check is a heuristic that may
    // always answer "no", so running out of steps merely skips a
    // simplification.
    static constexpr unsigned m_max_steps = 2000;
    mutable unsigned m_steps = 0;

    bool is_subset_rec(expr* a, expr* b, unsigned depth) const;

    // true if regex a, viewed as a flattened concatenation, has suf as a
    // structural (concatenation) suffix.
    bool ends_with(expr* a, expr* suf) const;

    void flatten_concat(expr* a, ptr_vector<expr>& out) const;

public:
    explicit seq_subset(seq_util::rex& re) : m_re(re) {}
    bool is_subset(expr* a, expr* b) const;
};
