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
#include "util/lbool.h"

class seq_subset {
    seq_util::rex& m_re;

    using cache = obj_pair_map<expr, expr, lbool>; // maps (a,b) to computed is_subset(a,b)

    bool has_suffix(expr* r, expr* suffix) const;
    bool strip_common_suffix(expr* a, expr* b, expr*& aprefix, expr*& bprefix) const;
    bool check_common_suffix(expr* a, expr* b, cache& visited) const;
    bool check_common_prefix(expr* a, expr* b, cache& visited) const;
    bool is_subset_rec(expr* a, expr* b, cache& visited) const;

public:
    explicit seq_subset(seq_util::rex& re) : m_re(re) {}
    bool is_subset(expr* a, expr* b) const;
};
