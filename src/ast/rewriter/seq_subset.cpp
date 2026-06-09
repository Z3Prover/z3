/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_subset.cpp

Abstract:

    Heuristic regular-expression subset checks used by seq_rewriter.

Author:

    Nikolaj Bjorner (nbjorner) 2026-6-8

--*/

#include "ast/rewriter/seq_subset.h"

bool seq_subset::has_suffix(expr* r, expr* suffix) const {
    if (r == suffix)
        return true;
    expr* r1 = nullptr, * r2 = nullptr;
    return m_re.is_concat(r, r1, r2) && has_suffix(r2, suffix);
}

bool seq_subset::strip_common_suffix(expr* a, expr* b, expr*& aprefix, expr*& bprefix) const {
    expr* a1 = nullptr, * a2 = nullptr, * b1 = nullptr, * b2 = nullptr;
    if (!m_re.is_concat(a, a1, a2) || !m_re.is_concat(b, b1, b2))
        return false;

    expr* atail = nullptr, * btail = nullptr;
    if (strip_common_suffix(a2, b2, atail, btail)) {
        aprefix = m_re.mk_concat(a1, atail);
        bprefix = m_re.mk_concat(b1, btail);
        return true;
    }

    if (a2 == b2) {
        aprefix = a1;
        bprefix = b1;
        return true;
    }

    return false;
}

bool seq_subset::check_common_suffix(expr* a, expr* b, cache& visited) const {
    expr* aprefix = nullptr, * bprefix = nullptr;
    if (!strip_common_suffix(a, b, aprefix, bprefix))
        return false;

    // E1: A·R ⊆ B·R if A ⊆ B (for nested concatenations by stripping common suffix R).
    if (is_subset_rec(aprefix, bprefix, visited))
        return true;

    // E4: A·R ⊆ B*·R if A ⊆ B.
    expr* bbase = nullptr;
    if (m_re.is_star(bprefix, bbase))
        return is_subset_rec(aprefix, bbase, visited);

    return false;
}

bool seq_subset::check_common_prefix(expr* a, expr* b, cache& visited) const {
    expr* a1 = nullptr, * a2 = nullptr, * b1 = nullptr, * b2 = nullptr;
    if (!(m_re.is_concat(a, a1, a2) && m_re.is_concat(b, b1, b2) && a1 == b1))
        return false;

    // E1 dual: R·A ⊆ R·B if A ⊆ B (for nested concatenations by stripping common prefix R).
    return is_subset_rec(a2, b2, visited);
}

bool seq_subset::is_subset_rec(expr* a, expr* b, cache& visited) const {
    lbool cached_result = l_undef;
    if (visited.find(a, b, cached_result))
        return cached_result == l_true;
    visited.insert_if_not_there(a, b, l_undef);
    auto set_result = [&](bool v) -> bool {
        visited.erase(a, b);
        visited.insert(a, b, to_lbool(v));
        return v;
    };

    if (a == b)
        return set_result(true);
    if (m_re.is_empty(a))
        return set_result(true);
    if (m_re.is_full_seq(b))
        return set_result(true);

    expr* a1 = nullptr, * a2 = nullptr, * b1 = nullptr, * b2 = nullptr;
    unsigned la, ua, lb, ub;

    // a ⊆ .+ iff a is non-nullable
    if (m_re.is_dot_plus(b) && m_re.get_info(a).nullable == l_false)
        return set_result(true);

    // a ⊆ a*
    if (m_re.is_star(b, b1) && a == b1)
        return set_result(true);

    // E3: R ⊆ R*
    if (m_re.is_star(b, b1) && is_subset_rec(a, b1, visited))
        return set_result(true);

    // E3: R1* ⊆ R2* if R1 ⊆ R2
    if (m_re.is_star(a, a1) && m_re.is_star(b, b1) && is_subset_rec(a1, b1, visited))
        return set_result(true);

    // E3: R1+ ⊆ R2+ if R1 ⊆ R2
    if (m_re.is_plus(a, a1) && m_re.is_plus(b, b1) && is_subset_rec(a1, b1, visited))
        return set_result(true);

    // a ⊆ b1 ∪ b2 if a ⊆ b1 or a ⊆ b2
    if (m_re.is_union(b, b1, b2) && (is_subset_rec(a, b1, visited) || is_subset_rec(a, b2, visited)))
        return set_result(true);

    // a1 ∪ a2 ⊆ b if a1 ⊆ b and a2 ⊆ b
    if (m_re.is_union(a, a1, a2) && is_subset_rec(a1, b, visited) && is_subset_rec(a2, b, visited))
        return set_result(true);

    // a1 ∩ a2 ⊆ b if a1 ⊆ b or a2 ⊆ b
    if (m_re.is_intersection(a, a1, a2) && (is_subset_rec(a1, b, visited) || is_subset_rec(a2, b, visited)))
        return set_result(true);

    // a ⊆ b1 ∩ b2 if a ⊆ b1 and a ⊆ b2
    if (m_re.is_intersection(b, b1, b2) && is_subset_rec(a, b1, visited) && is_subset_rec(a, b2, visited))
        return set_result(true);

    // concat monotonicity
    if (m_re.is_concat(a, a1, a2) && m_re.is_concat(b, b1, b2) &&
        is_subset_rec(a1, b1, visited) && is_subset_rec(a2, b2, visited))
        return set_result(true);

    // E2: R ⊆ Σ*·R, and generalized suffix matching for nested concatenations.
    if (m_re.is_concat(b, b1, b2) && m_re.is_full_seq(b1) && has_suffix(a, b2))
        return set_result(true);

    // loop subsumption: r{la,ua} ⊆ r{lb,ub} when lb <= la and ua <= ub
    if (m_re.is_loop(a, a1, la, ua) && m_re.is_loop(b, b1, lb, ub) &&
        a1 == b1 && lb <= la && ua <= ub)
        return set_result(true);

    // complement: ~a ⊆ ~b if b ⊆ a
    if (m_re.is_complement(a, a1) && m_re.is_complement(b, b1))
        return set_result(is_subset_rec(b1, a1, visited));

    if (check_common_suffix(a, b, visited))
        return set_result(true);

    if (check_common_prefix(a, b, visited))
        return set_result(true);

    return set_result(false);
}

bool seq_subset::is_subset(expr* a, expr* b) const {
    cache visited;
    return is_subset_rec(a, b, visited);
}
