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

void seq_subset::flatten_concat(expr* r, ptr_vector<expr>& out) const {
    expr* r1 = nullptr, * r2 = nullptr;
    if (m_re.is_concat(r, r1, r2)) {
        flatten_concat(r1, out);
        flatten_concat(r2, out);
    }
    else {
        out.push_back(r);
    }
}

expr* seq_subset::mk_concat(ptr_vector<expr> const& es, unsigned lo, unsigned hi, sort* re_sort) const {
    SASSERT(lo <= hi);
    if (lo == hi)
        return m_re.mk_epsilon(m_re.to_seq(re_sort));
    expr* r = es[lo];
    for (unsigned i = lo + 1; i < hi; ++i)
        r = m_re.mk_concat(r, es[i]);
    return r;
}

bool seq_subset::has_suffix(expr* r, expr* suffix) const {
    ptr_vector<expr> rs, ss;
    flatten_concat(r, rs);
    flatten_concat(suffix, ss);
    if (ss.size() > rs.size())
        return false;
    for (unsigned i = 0; i < ss.size(); ++i) {
        if (ss[ss.size() - 1 - i] != rs[rs.size() - 1 - i])
            return false;
    }
    return true;
}

bool seq_subset::is_subset_slices(
    ptr_vector<expr> const& as, unsigned alo, unsigned ahi,
    ptr_vector<expr> const& bs, unsigned blo, unsigned bhi,
    cache& visited) const {
    SASSERT(alo <= ahi && blo <= bhi);
    if (alo == ahi && blo == bhi)
        return true;
    sort* re_sort = alo < ahi ? as[alo]->get_sort() : bs[blo]->get_sort();
    expr* a = mk_concat(as, alo, ahi, re_sort);
    expr* b = mk_concat(bs, blo, bhi, re_sort);
    return is_subset_rec(a, b, visited);
}

bool seq_subset::check_common_suffix(expr* a, expr* b, cache& visited) const {
    ptr_vector<expr> as, bs;
    flatten_concat(a, as);
    flatten_concat(b, bs);

    unsigned i = as.size(), j = bs.size();
    while (i > 0 && j > 0 && as[i - 1] == bs[j - 1]) {
        --i;
        --j;
    }
    unsigned common = as.size() - i;
    if (common == 0)
        return false;

    // E1: A·R ⊆ B·R if A ⊆ B (for nested concatenations by stripping common suffix R).
    if (is_subset_slices(as, 0, i, bs, 0, j, visited))
        return true;

    // E4: A·R ⊆ B*·R if A ⊆ B.
    expr* bbase = nullptr;
    if (j == 1 && m_re.is_star(bs[0], bbase)) {
        expr* aprefix = mk_concat(as, 0, i, a->get_sort());
        return is_subset_rec(aprefix, bbase, visited);
    }

    return false;
}

bool seq_subset::check_common_prefix(expr* a, expr* b, cache& visited) const {
    ptr_vector<expr> as, bs;
    flatten_concat(a, as);
    flatten_concat(b, bs);

    unsigned i = 0;
    while (i < as.size() && i < bs.size() && as[i] == bs[i])
        ++i;
    if (i == 0)
        return false;

    // E1 dual: R·A ⊆ R·B if A ⊆ B (for nested concatenations by stripping common prefix R).
    return is_subset_slices(as, i, as.size(), bs, i, bs.size(), visited);
}

bool seq_subset::is_subset_rec(expr* a, expr* b, cache& visited) const {
    if (a == b)
        return true;
    if (m_re.is_empty(a))
        return true;
    if (m_re.is_full_seq(b))
        return true;
    if (visited.contains(std::make_pair(a, b)))
        return false;
    visited.insert(std::make_pair(a, b));

    expr* a1 = nullptr, * a2 = nullptr, * b1 = nullptr, * b2 = nullptr;
    unsigned la, ua, lb, ub;

    // a ⊆ .+ iff a is non-nullable
    if (m_re.is_dot_plus(b) && m_re.get_info(a).nullable == l_false)
        return true;

    // a ⊆ a*
    if (m_re.is_star(b, b1) && a == b1)
        return true;

    // E3: R ⊆ R*
    if (m_re.is_star(b, b1) && is_subset_rec(a, b1, visited))
        return true;

    // E3: R1* ⊆ R2* if R1 ⊆ R2
    if (m_re.is_star(a, a1) && m_re.is_star(b, b1) && is_subset_rec(a1, b1, visited))
        return true;

    // E3: R1+ ⊆ R2+ if R1 ⊆ R2
    if (m_re.is_plus(a, a1) && m_re.is_plus(b, b1) && is_subset_rec(a1, b1, visited))
        return true;

    // a ⊆ b1 ∪ b2 if a ⊆ b1 or a ⊆ b2
    if (m_re.is_union(b, b1, b2) && (is_subset_rec(a, b1, visited) || is_subset_rec(a, b2, visited)))
        return true;

    // a1 ∪ a2 ⊆ b if a1 ⊆ b and a2 ⊆ b
    if (m_re.is_union(a, a1, a2) && is_subset_rec(a1, b, visited) && is_subset_rec(a2, b, visited))
        return true;

    // a1 ∩ a2 ⊆ b if a1 ⊆ b or a2 ⊆ b
    if (m_re.is_intersection(a, a1, a2) && (is_subset_rec(a1, b, visited) || is_subset_rec(a2, b, visited)))
        return true;

    // a ⊆ b1 ∩ b2 if a ⊆ b1 and a ⊆ b2
    if (m_re.is_intersection(b, b1, b2) && is_subset_rec(a, b1, visited) && is_subset_rec(a, b2, visited))
        return true;

    // concat monotonicity
    if (m_re.is_concat(a, a1, a2) && m_re.is_concat(b, b1, b2) &&
        is_subset_rec(a1, b1, visited) && is_subset_rec(a2, b2, visited))
        return true;

    // E2: R ⊆ Σ*·R, and generalized suffix matching for nested concatenations.
    if (m_re.is_concat(b, b1, b2) && m_re.is_full_seq(b1) && has_suffix(a, b2))
        return true;

    // loop subsumption: r{la,ua} ⊆ r{lb,ub} when lb <= la and ua <= ub
    if (m_re.is_loop(a, a1, la, ua) && m_re.is_loop(b, b1, lb, ub) &&
        a1 == b1 && lb <= la && ua <= ub)
        return true;

    // complement: ~a ⊆ ~b if b ⊆ a
    if (m_re.is_complement(a, a1) && m_re.is_complement(b, b1))
        return is_subset_rec(b1, a1, visited);

    if (check_common_suffix(a, b, visited))
        return true;

    if (check_common_prefix(a, b, visited))
        return true;

    return false;
}

bool seq_subset::is_subset(expr* a, expr* b) const {
    cache visited;
    return is_subset_rec(a, b, visited);
}
