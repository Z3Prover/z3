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
#include "util/obj_pair_hashtable.h"

class seq_subset {
    seq_util::rex& m_re;

    using cache = obj_pair_map<expr, expr, bool>;

    void flatten_concat(expr* r, ptr_vector<expr>& out) const;
    expr* mk_concat(ptr_vector<expr> const& es, unsigned lo, unsigned hi, sort* re_sort) const;
    bool has_suffix(expr* r, expr* suffix) const;
    bool is_subset_slices(
        ptr_vector<expr> const& as, unsigned alo, unsigned ahi,
        ptr_vector<expr> const& bs, unsigned blo, unsigned bhi,
        cache& visited) const;
    bool check_common_suffix(expr* a, expr* b, cache& visited) const;
    bool check_common_prefix(expr* a, expr* b, cache& visited) const;
    bool is_subset_rec(expr* a, expr* b, cache& visited) const;

public:
    explicit seq_subset(seq_util::rex& re) : m_re(re) {}
    bool is_subset(expr* a, expr* b) const;
};
